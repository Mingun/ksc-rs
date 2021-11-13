//! Compiler backend for generate a Java source code from the Kaitai Struct definition.

use heck::{ToLowerCamelCase, ToUpperCamelCase};
use indexmap::IndexMap;
use ksc::model::{AttributeName, FieldName, OptionalName, Root, TypeName, UserType};
use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::quote;

/// List of names that generated identifiers cannot have.
///
/// Keep sorted!
const RESERVED: &[&str; 56] = &[
  "abstract",
  "assert",
  "boolean",
  "break",
  "byte",
  "case",
  "catch",
  "char",
  "class",
  "const",
  "continue",
  "default",
  "do",
  "double",
  "else",
  "enum",
  "equals",
  "extends",
  "false",
  "final",
  "finally",
  "float",
  "for",
  "goto",
  "hashCode",
  "if",
  "implements",
  "import",
  "instanceof",
  "int",
  "interface",
  "long",
  "native",
  "new",
  "null",
  "package",
  "private",
  "protected",
  "public",
  "return",
  "short",
  "static",
  "strictfp",
  "super",
  "switch",
  "synchronized",
  "this",
  "throw",
  "throws",
  "toString",
  "transient",
  "true",
  "try",
  "void",
  "volatile",
  "while",
];

/// Translates Kaitai Struct definition to Java 8 source code
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct JavaGenerator;
impl JavaGenerator {
  pub fn generate(&self, ksy: &Root) -> TokenStream {
    TypeGenerator::new(&ksy.type_).translate(&ksy.name, &ksy.type_, false)
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

struct TypeGenerator<'a> {
  /// Mapping from attribute names to Java names
  field_names: IndexMap<AttributeName<'a>, String>,
}
impl<'a> TypeGenerator<'a> {
  fn new(ty: &'a UserType) -> Self {
    // Generate Java name for each attribute of the type, resolve name clashes with reserved words
    let names = ty.attribute_names(|name, attempt| {
      use ksc::model::AttributeName::*;

      let generated = match (attempt, name) {
        (0, Unnamed(i)) => format!("unnamed{}", i),
        (a, Unnamed(i)) => format!("unnamed{}{}", i, a),

        (0, Seq(n)) => n.to_lower_camel_case(),
        (a, Seq(n)) => format!("{}{}", n.to_lower_camel_case(), a),

        (0, NonSeq(n)) => n.to_lower_camel_case(),
        (a, NonSeq(n)) => format!("{}{}", n.to_lower_camel_case(), a),
      };

      // Check if a generated name conflicts with a keyword and return `None` if that is true
      match RESERVED.binary_search(&generated.as_ref()) {
        Ok(_) => None,
        Err(_) => Some(generated),
      }
    });

    Self { field_names: names }
  }

  /// Translates a type into a Java class. Inner types translates to nested `public static final`
  /// classes.
  ///
  /// # Parameters
  /// - `name`: name of the type which will be converted to the CamelCase Java class name
  /// - `ty`: definition of the type. Attributes and instances translated to the class
  ///   fields and accessor methods
  /// - `inner`: if `true` then `static` class without annotations is generated, otherwise
  ///   top-level class will be generated
  fn translate(&self, name: &TypeName, ty: &UserType, inner: bool) -> TokenStream {
    let static_ = if inner { quote!(static final) } else { quote!() };
    let header = if inner {
      quote!()
    } else {
      let id: &str = name.as_ref();
      quote! {
        import java.util.HashMap;
        import java.util.Map;
        import io.kaitai.struct.PositionInfo;
        import io.kaitai.struct.Span;
        import io.kaitai.struct.annotations.SeqItem;
        import io.kaitai.struct.annotations.Generated;

        @Generated(
          id = #id,
          version = "",
          posInfo = true,
          autoRead = true
        )
      }
    };

    let name = self.translate_type_name(&name);

    let fields = ty.fields.iter().enumerate().filter_map(|(i, (n, _))| match n {
      OptionalName::Unnamed(_) => None,
      OptionalName::Named(n) => {
        let id: &str = n.as_ref();
        let name = self.translate_field_name(n);
        let ty = quote!(Object);//TODO: calculate actual field type
        let i = Literal::usize_unsuffixed(i);

        Some(quote! {
          @SeqItem(id = #id, index = #i)
          private #ty #name;
        })
      }
    });

    let classes = ty.types.iter().map(|(n, t)| TypeGenerator::new(t).translate(n, t, true));

    quote! {
      #header
      public #static_ class #name implements PositionInfo {
        #(#fields)*

        public final Map<String, Span> _spans = new HashMap<>();

        #(#classes)*

        @Override
        public Map<String, Span> _spans() { return _spans; }
      }
    }
  }

  /// Converts kaitai's type name to Java name
  fn translate_type_name(&self, name: &TypeName) -> Ident {
    Ident::new(&name.to_upper_camel_case(), Span::call_site())
  }

  /// Converts kaitai's field name to Java name
  fn translate_field_name(&self, name: &FieldName) -> Ident {
    match self.field_names.get(&AttributeName::Seq(name)) {
      Some(name) => Ident::new(name, Span::call_site()),
      // not exist field translate as is. This can happen only in tests
      None => Ident::new(&name.to_lower_camel_case(), Span::call_site()),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Compile specified `source` as a java code and check that it has no errors.
/// The source should contain definition of the `KscJavaTest` class.
///
/// # Parameters
/// - `dir`: directory in which source file should be placed
/// - `source`: Java source code to compile
#[cfg(test)]
#[track_caller]
fn compile(dir: &std::path::Path, source: &str) {
  use std::fs::File;
  use std::io::Write;
  use std::process::Command;

  let path = std::env::temp_dir().join(dir);
  std::fs::create_dir_all(&path).expect("cannot create directory for test");

  let path = path.join("KscJavaTest.java");
  let mut java = File::create(&path).expect("cannot create temp file with java code");
  java.write_all(source.as_ref()).expect("cannot write Java source code to the file");

  let output = Command::new("javac")
    .arg(path.as_os_str())
    .output()
    .expect("failed to execute javac. Check that `javac` in the PATH. Is JDK installed?");

  println!(r#"
status: {}
stdout(empty={}):
{}
stderr(empty={}):
{}
"#,
    output.status,
    output.stdout.is_empty(), String::from_utf8_lossy(&output.stdout),
    output.stderr.is_empty(), String::from_utf8_lossy(&output.stderr),
  );
  assert!(output.status.success());
}

/// Try to generate Java files for all format files and optionally compile them with
/// standalone the `javac` compiler (if `test-compile-formats` feature is defined).
#[cfg(test)]
mod formats {
  use super::*;
  use ksc::model::{ImportLoader, Package};
  use ksc::parser::{Import, Ksy};
  use std::fs::File;
  use std::io;
  use std::path::{Path, PathBuf};
  use test_generator::test_resources;

  #[derive(Debug)]
  // Values of enumeration is not used directly, but still valuable if test fail
  #[allow(dead_code)]
  enum LoaderError {
    Io(String, io::Error),
    Parse(serde_yml::Error),
  }

  fn to_path(mut base: PathBuf, import: &Import) -> PathBuf {
    for comp in &import.components {
      base.push(comp);
    }
    base.push(&import.name.0);
    base.set_extension("ksy");
    base
  }

  struct FileLoader {
    /// Bases for absolute imports
    abs_roots: Vec<PathBuf>,
  }
  impl ImportLoader for FileLoader {
    type Id = PathBuf;
    type Error = LoaderError;

    fn new_id(&mut self, mut base: Self::Id, import: &Import) -> Self::Id {
      if import.absolute {
        for base in self.abs_roots.iter().cloned() {
          let path = to_path(base, import);
          // Required for tests which expect that absolute import will look into several places
          // test-data/formats/imports_abs.ksy
          // test-data/formats/imports_abs_abs.ksy
          // test-data/formats/imports_abs_rel.ksy
          // test-data/formats/ks_path/for_abs_imports/imported_and_abs.ksy
          if path.exists() {
            return path;
          }
        }
        // In tests we should find file in one of the provided roots
        panic!("cannot find file for {import}");
      } else {
        // Remove name of the file from which we are imported
        base.pop();
        to_path(base, import)
      }
    }

    fn load(&mut self, id: Self::Id) -> Result<Ksy, Self::Error> {
      let display = id.display().to_string();
      let file = File::open(id).map_err(|e| LoaderError::Io(display, e))?;
      serde_yml::from_reader(file).map_err(LoaderError::Parse)
    }
  }

  fn gen(resource: &str) -> TokenStream {
    // Allow to Ctrl+click in VSCode output to open the file
    println!("file: {resource}");

    // Directory with `ksc` crate
    // The working with workspaces a buggy a bit
    // https://github.com/frehberg/test-generator/issues/6
    let ksc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let path = ksc_dir.join(resource);
    let display = path.display().to_string();

    let file = File::open(&path).expect(&format!("can't read file {}", display));
    let ksy: Ksy = serde_yml::from_reader(file).expect(&format!("invalid file {}", display));

    let name = ksy.meta.id.clone().expect("missing `meta/id`");
    let package = Package::new(path, name, ksy, FileLoader {
      abs_roots: vec![
        ksc_dir.join("formats"),
        ksc_dir.join("test-data").join("formats"),
        ksc_dir.join("test-data").join("formats").join("ks_path"),
      ],
    }).expect(&format!("invalid imports in {}", display));

    let roots = package.validate().expect(&format!("incorrect KSY {}", display));
    let root = roots.first().unwrap();

    let gen = JavaGenerator;
    gen.generate(&root)
  }

  fn is_valid_test(resource: &str) -> bool {
    // Currently this file cannot be successfully parsed in non-compatible mode
    // Unfortunately, negative glob patterns are not allowed in test_resources,
    // as well as adding #[ignore], so we filter out test here
    // TODO: Fix file `type_ternary_2nd_falsy.ksy` in upstream and enable testing
    // it in non-compatible mode
    #[cfg(not(feature = "compatible"))]
    if resource.ends_with("type_ternary_2nd_falsy.ksy") {
      return false;
    }
    // Contains underscores in numbers, which are threated as strings according to YAML 1.2 rules
    // which serde_yml applies, but original compiler apply YAML 1.1 rules.
    // See https://github.com/kaitai-io/kaitai_struct/issues/1132
    if resource.ends_with("renderware_binary_stream.ksy") {
      return false;
    }
    // Invalid spec - defines some enum values as strings instead of numbers
    // TODO: remove when https://github.com/kaitai-io/kaitai_struct_formats/pull/701 merged
    if resource.ends_with("nt_mdt.ksy") {
      return false;
    }
    true
  }


  #[cfg(not(feature = "test-compile-formats"))]
  #[test_resources("formats/**/*.ksy")]
  #[test_resources("test-data/formats/**/*.ksy")]
  fn generate(resource: &str) {
    if is_valid_test(resource) {
      gen(resource);
    }
  }

  /// Because compilation uses the filesystem, it can take a significant amount of time
  /// (unfortunately, `javac` has no ability to compile from memory). Therefore this
  /// tests are disabled by default. You need to run `cargo test --features test-compile-formats`
  /// to enable this tests.
  ///
  /// Expected, that https://github.com/kaitai-io/kaitai_struct_formats was checkout to
  /// crate root directory, next to `src`.
  #[cfg(feature = "test-compile-formats")]
  #[test_resources("formats/**/*.ksy")]
  #[test_resources("test-data/formats/**/*.ksy")]
  fn compile(resource: &str) {
    if is_valid_test(resource) {
      super::compile(Path::new("ksc-rs"), &gen(resource).to_string());
    }
  }
}
