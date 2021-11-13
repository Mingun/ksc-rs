//! Compiler backend for generate a Java source code from the Kaitai Struct definition.

use heck::{ToUpperCamelCase, ToLowerCamelCase};
use ksc::model::{FieldName, OptionalName, Root, TypeName, UserType};
use proc_macro2::{Literal, Ident, Span, TokenStream};
use quote::quote;

/// Translates Kaitai Struct definition to a Java 8 source code
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct JavaGenerator;
impl JavaGenerator {
  pub fn generate(&self, ksy: &Root) -> TokenStream {
    self.translate_type(&ksy.name, &ksy.type_, false)
  }
  fn translate_type_name(&self, name: &TypeName) -> Ident {
    Ident::new(&name.to_upper_camel_case(), Span::call_site())
  }
  fn translate_field(&self, name: &FieldName) -> Ident {
    //TODO: need to rename special Java methods (toString, hashCode, equals) and keywords
    Ident::new(&name.to_lower_camel_case(), Span::call_site())
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
  fn translate_type(&self, name: &TypeName, ty: &UserType, inner: bool) -> TokenStream {
    let static_ = if inner { quote!(static final) } else { quote!() };
    let header = if inner {
      quote!()
    } else {
      let id: &str = name.as_ref();
      quote!{
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
        let name = self.translate_field(&n);
        let ty = quote!(Object);//TODO: calculate actual field type
        let i = Literal::usize_unsuffixed(i);

        Some(quote! {
          @SeqItem(id = #id, index = #i)
          private #ty #name;
        })
      }
    });

    let classes = ty.types.iter().map(|(n, t)| self.translate_type(n, t, true));

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
}

/// Internal trait to facilitate translation of recursive structures
trait Translate {
  /// Translates self into a piece of Java code using settings in `gen`
  fn translate(&self, gen: &JavaGenerator) -> TokenStream;
}

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
  use std::fs::File;
  use std::path::Path;
  use test_generator::test_resources;
  use ksc::parser::Ksy;
  use ksc::model::Root;

  fn gen(resource: &str) -> TokenStream {
    // The working with workspaces a buggy a bit
    // https://github.com/frehberg/test-generator/issues/6
    let ksc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let path = ksc_dir.join(resource);
    let file = File::open(&path).expect(&format!("can't read file {}", path.display()));
    let ksy: Ksy = serde_yml::from_reader(file).expect(&format!("invalid file {}", path.display()));
    let root: Root = ksy.try_into().expect(&format!("incorrect KSY {}", path.display()));

    let gen = JavaGenerator;
    gen.generate(&root)
  }

  #[cfg(not(feature="test-compile-formats"))]
  #[test_resources("formats/**/*.ksy")]
  fn generate(resource: &str) {
    gen(resource);
  }

  /// Because compilation uses the filesystem, it can take a significant amount of time
  /// (unfortunately, `javac` has no ability to compile from memory). Therefore this
  /// tests are disabled by default. You need to run `cargo test --features test-compile-formats`
  /// to enable this tests.
  ///
  /// Expected, that https://github.com/kaitai-io/kaitai_struct_formats was checkout to
  /// crate root directory, next to `src`.
  #[cfg(feature="test-compile-formats")]
  #[test_resources("formats/**/*.ksy")]
  fn compile(resource: &str) {
    //TODO: enable compilation
    gen(resource);
    // super::compile(path.parent().unwrap(), &gen(resource).to_string());
  }
}
