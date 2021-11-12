//! Compiler backend for generate a Java source code from the Kaitai Struct definition.

use std::str::FromStr;

use heck::{ToLowerCamelCase, ToShoutySnakeCase, ToUpperCamelCase};
use indexmap::IndexMap;
use ksc::model::expressions::{OwningAttr, OwningNode};
use ksc::model::{
  Attribute, AttributeName, Chunk, EnumName, EnumVariantName, FieldName, OptionalName, Repeat, Root,
  SeqName, Terminator, TypeName, UserType, Variant,
};
use ksc::parser::expressions::ContextVar;
use num_traits::cast::ToPrimitive;
use proc_macro2::{Ident, Literal, Punct, Spacing, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};

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
    let parsers = ty.fields.iter().map(|(n, a)| self.translate_attribute(n, a));

    let classes = ty.types.iter().map(|(n, t)| TypeGenerator::new(t).translate(n, t, true));

    quote! {
      #header
      public #static_ class #name implements PositionInfo {
        #(#fields)*

        public final Map<String, Span> _spans = new HashMap<>();

        #(#classes)*

        @Override
        public Map<String, Span> _spans() { return _spans; }

        public _read() {
          KaitaiStream _io;
          #(#parsers)*
        }
      }
    }
  }

  /// Translate Kaitai Struct expression into Java expression
  ///
  /// # Parameters
  /// - `tokens`: this token stream will filled with expression
  /// - `expression`: expression to translate
  fn translate_expression(&self, tokens: &mut TokenStream, expression: &OwningNode) {
    use ksc::parser::expressions::ContextVar as CtxVar;
    use ksc::parser::expressions::UnaryOp::*;
    use OwningNode::*;

    match expression {
      Str(s) => s.to_tokens(tokens),
      Int(i) => {
        if let Some(i) = i.to_i32() {
          Literal::i32_unsuffixed(i).to_tokens(tokens);
        } else
        if let Some(i) = i.to_i64() {
          // Parsing are always successful because we generate a correct token
          tokens.extend(TokenStream::from_str(&format!("{}L", i)).unwrap());
        } else
        if let Some(i) = i.to_u64() {
          // Write unsigned big numbers in hexadecimal
          // Parsing are always successful because we generate a correct token
          tokens.extend(TokenStream::from_str(&format!("{:#x}L", i)).unwrap());
        } else {
          // Write unsigned big numbers in hexadecimal
          let i = i.to_str_radix(16);
          tokens.append_all(quote!(new BigInteger(#i, 16)));
        }
      },
      Float(f) => match f.to_f64() {
        // `to_f64` can return Infinity in case of overflow which `f64_unsuffixed`
        // cannot handle
        Some(f) if f.is_finite() => Literal::f64_unsuffixed(f).to_tokens(tokens),
        _ => {
          let f = f.to_string();
          tokens.append_all(quote!(new BigDecimal(#f)));
        }
      },
      Bool(b) => b.to_tokens(tokens),

      ContextVar(CtxVar::Index) => tokens.append_all(quote!{ i }),
      // FIXME: different meaning depending on context. This is for `repeat-until`
      ContextVar(CtxVar::Value) => tokens.append_all(quote!{ _value }),

      Attr(attr) => {// this.<attr>()
        tokens.append_all(quote!(this.));
        self.translate_access(tokens, attr);
      },

      EnumVariant { enum_, variant } => {
        let scope = enum_.scope.path.iter().map(|p| self.translate_type_name(p));
        let name  = self.translate_enum_name(&enum_.name);
        let value = self.translate_enum_value_name(variant);

        tokens.append_all(quote!(#(#scope.)* #name . #value));
      },

      // List(arr),

      // SizeOf { type_, bit },

      Call { callee, method, args } => {// <callee>.<method>(<args>)
        self.translate_expression(tokens, callee);
        Punct::new('.', Spacing::Alone).to_tokens(tokens);
        self.translate_field_name(method).to_tokens(tokens);
        Punct::new('(', Spacing::Alone).to_tokens(tokens);
        let mut first = true;
        for arg in args {
          if !first {
            Punct::new(',', Spacing::Alone).to_tokens(tokens);
          }
          self.translate_expression(tokens, arg);
          first = false;
        }
        Punct::new(')', Spacing::Alone).to_tokens(tokens);
      },
      // Cast { expr, to_type },
      // Index { expr, index },
      Index { expr, index } => {// <expr>.get(<index>)
        self.translate_expression(tokens, expr);
        tokens.append_all(quote!(.get));
        Punct::new('(', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, index);
        Punct::new(')', Spacing::Alone).to_tokens(tokens);
      },
      Access { expr, attr } => {// <expr>.<attr>()
        self.translate_expression(tokens, expr);
        Punct::new('.', Spacing::Alone).to_tokens(tokens);
        self.translate_access(tokens, attr);
      },

      Unary { op: Neg, expr } => {
        Punct::new('-', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, expr)
      },
      Unary { op: Not, expr } => {
        Punct::new('!', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, expr)
      },
      Unary { op: Inv, expr } => {
        Punct::new('~', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, expr)
      },

      Binary { op, left, right } => {
        use ksc::parser::expressions::BinaryOp::*;

        self.translate_expression(tokens, left);
        tokens.append_all(match op {
          Add => quote!(+),
          Sub => quote!(-),
          Mul => quote!(*),
          Div => quote!(/),
          Rem => quote!(%),

          Shl => quote!(<<),
          Shr => quote!(>>),

          Eq => quote!(==),
          Ne => quote!(!=),
          Le => quote!(<=),
          Ge => quote!(>=),
          Lt => quote!(<),
          Gt => quote!(>),

          And => quote!(&&),
          Or  => quote!(||),

          BitAnd => quote!(&),
          BitOr  => quote!(|),
          BitXor => quote!(^),
        });
        self.translate_expression(tokens, right);
      },
      Branch { condition, if_true, if_false } => {
        self.translate_expression(tokens, condition);
        Punct::new('?', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, if_true);
        Punct::new(':', Spacing::Alone).to_tokens(tokens);
        self.translate_expression(tokens, if_false);
      },
      e => unimplemented!("translating complex expressions not yet implemented. Expression:\n{:#?}", e),
    }
  }

  fn translate_attribute(&self, name: &SeqName, attr: &Attribute) -> TokenStream {
    let ty = quote!(Object);//TODO: calculate type
    let stream = quote!(this._io);//TODO: calculate stream
    let parse = attr.chunk.translate(self);

    let statement = match &attr.repeat {
      Repeat::None => parse,
      Repeat::Eos => quote!(
        int i = 0;
        final ArrayList<#ty> _arr = new ArrayList<>();
        while (!#stream.isEof()) {
          #parse
          _arr.add(_value);
          i += 1;
        }
      ),
      Repeat::Count(count) => {
        let count = count.translate(self);
        quote!(
          int _count = #count;
          final ArrayList<#ty> _arr = new ArrayList<>(_count);
          for (int i = 0; i < _count; i += 1) {
            #parse
            _arr.add(_value);
          }
        )
      },
      Repeat::Until(condition) => {
        let condition = condition.translate(self);
        quote!(
          int i = 0;
          final ArrayList<#ty> _arr = new ArrayList<>();
          do {
            #parse
            _arr.add(_value);
            i += 1;
          } while (!#condition);
        )
      },
    };
    let store = match name {
      // Assign `_value` or `_arr` to the field
      OptionalName::Named(name) => {
        let field = self.translate_field_name(name);
        match attr.repeat {
          Repeat::None => quote!(this.#field = _value;),
          _ => quote!(this.#field = _arr;),
        }
      }
      // Do not store result of parsing in case of unnamed fields
      OptionalName::Unnamed(_) => quote!(),
    };
    let statement = quote!({
      #statement
      #store
    });

    if let Some(condition) = &attr.condition {
      let condition = condition.translate(self);
      // Braces not required here because every expression already in braces
      quote!(if (#condition) #statement)
    } else {
      statement
    }
  }

  fn translate_access(&self, tokens: &mut TokenStream, name: &OwningAttr) {
    match name {
      OwningAttr::Stream => tokens.append_all(quote!{ _io() }),
      OwningAttr::Root   => tokens.append_all(quote!{ _root() }),
      OwningAttr::Parent => tokens.append_all(quote!{ _parent() }),
      OwningAttr::SizeOf => todo!("_sizeof not yet implemented"),
      OwningAttr::User(name) => {
        self.translate_field_name(name).to_tokens(tokens);
        tokens.append_all(quote!{ () });
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

  /// Converts kaitai's enum name to Java enum name
  fn translate_enum_name(&self, name: &EnumName) -> Ident {
    Ident::new(&name.to_upper_camel_case(), Span::call_site())
  }

  /// Converts kaitai's enum variant name to Java enum variant name
  fn translate_enum_value_name(&self, name: &EnumVariantName) -> Ident {
    Ident::new(&name.to_shouty_snake_case(), Span::call_site())
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Internal trait to facilitate translation of recursive structures
trait Translate {
  /// Translates self into a piece of Java code using settings in `gen`
  fn translate(&self, gen: &TypeGenerator) -> TokenStream;
}

impl Translate for OwningNode {
  fn translate(&self, gen: &TypeGenerator) -> TokenStream {
    let mut tokens = TokenStream::new();
    gen.translate_expression(&mut tokens, self);
    tokens
  }
}

impl<T: Translate> Translate for Variant<T> {
  fn translate(&self, gen: &TypeGenerator) -> TokenStream {
    match self {
      Variant::Fixed(value) => value.translate(gen),
      Variant::Choice { switch_on, cases } => {
        let choice = switch_on.translate(gen);

        //TODO: use `if` for complex cases
        let cases = cases.iter().map(|(case, body)| {
          let body = body.translate(gen);
          match case {
            OwningNode::ContextVar(ContextVar::Value) => quote!(
              default: {
                #body
                break;
              }
            ),
            _ => {
              let case = case.translate(gen);
              quote!(
                case #case: {
                  #body
                  break;
                }
              )
            },
          }
        });

        quote!(
          switch (#choice) {
            #(#cases)*
          }
        )
      }
    }
  }
}

impl Translate for Chunk {
  fn translate(&self, gen: &TypeGenerator) -> TokenStream {
    use ksc::model::Size::*;

    let stream = match &self.size {
      Natural | Eos(None) => None,
      Eos(Some(Terminator { value, consume, include, mandatory })) => {
        let value = Literal::u8_unsuffixed(*value);
        Some(quote!(this._io.subStream(#value, #consume, #include, #mandatory)))
      },
      Until(Terminator { value, consume, include, mandatory }) => {
        let value = Literal::u8_unsuffixed(*value);
        Some(quote!(this._io.subStream(#value, #consume, #include, #mandatory)))
      },
      Exact { count, until: None } => {
        let count = count.translate(gen);
        Some(quote!(this._io.subStream(#count)))
      },
      Exact { count, until: Some(Terminator { value, consume, include, mandatory }) } => {
        let count = count.translate(gen);
        let value = Literal::u8_unsuffixed(*value);
        Some(quote!(this._io.subStream(#count, #value, #consume, #include, #mandatory)))
      },
    }.map(|stream| quote!(_io = #stream;));

    quote! {
      #stream
      final Object _value = unimplemented();//TODO: implement parse of attribute
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

#[cfg(test)]
#[track_caller]
fn parse(expr: &str) -> OwningNode {
  use ksc::model::{ImportLoader, Package, PackageContext};
  use ksc::parser::{Import, Ksy, Name};

  struct NoneLoader;
  impl ImportLoader for NoneLoader {
    type Id = ();
    type Error = ();

    fn new_id(&mut self, _base: Self::Id, _import: &Import) -> Self::Id {
      panic!("never called in tests")
    }
    fn load(&mut self, _id: Self::Id) -> Result<Ksy, Self::Error> {
      panic!("never called in tests")
    }
  }

  let pkg = Package::new((), Name("".into()), Ksy::default(), NoneLoader).unwrap();
  let ksy = pkg.files.values().next().unwrap();
  let ctx = PackageContext::new(&pkg);
  let ctx = ctx.for_file(&ksy);
  OwningNode::parse(expr, &ctx.for_root()).expect("incorrect Kaitai expression")
}

#[cfg(test)]
mod expressions {
  use super::*;
  use std::path::Path;

  /// Translates Kaitai Struct expression into a Java expression and check that it compiles
  #[track_caller]
  fn translate(test_name: &str, java_type: &str, expr: &str) {
    println!("expression: {}", expr);
    let expr = parse(expr);

    let gen = TypeGenerator { field_names: IndexMap::new() };
    let tokens = expr.translate(&gen);
    println!("translated: {}", tokens);

    compile(Path::new(test_name), &format!(r#"
    // For numbers test
    import java.math.BigDecimal;
    import java.math.BigInteger;
    public class KscJavaTest {{
      // Helper functions for `call` and `method_call` tests
      String argument() {{ return ""; }}
      KscJavaTest object() {{ return this; }}
      char callable(int i, long l, String s) {{ return '0'; }}

      void test() {{
        final {} result = {};
      }}
    }}
    "#, java_type, tokens));
  }

  /// - `name`: the name of test function
  /// - `expr`: the Kaitai Struct expression with number literal
  /// - `java_type`: the Java type that will be used to hold a generated value
  macro_rules! expr_test {
    ($name:ident => $expr:literal, $java_type:ident) => {
      #[test]
      fn $name() { translate(stringify!($name), stringify!($java_type), $expr); }
    };
  }

  mod numbers {
    use super::*;

    expr_test!(byte_0x00 => "0",    byte);
    expr_test!(byte_0x7f => "127",  byte);
    expr_test!(byte_0x80 => "-128", byte);

    expr_test!(short_0x80   => "128",     short);
    expr_test!(short_0x7fff => "0x7FFF",  short);
    expr_test!(short_0x8000 => "-0x7FFF", short);

    expr_test!(int_0x8000      => "0x8000",       int);
    expr_test!(int_0x7fff_ffff => "0x7FFF_FFFF",  int);
    expr_test!(int_0x8000_0000 => "-0x7FFF_FFFF", int);

    expr_test!(long_0x8000_0000           => "0x8000_0000",           long);
    expr_test!(long_0xffff_ffff_ffff_ffff => "0xFFFF_FFFF_FFFF_FFFF", long);

    expr_test!(float_pos => " 123.456", double);
    expr_test!(float_neg => "-123.456", double);

    expr_test!(float_pos_sci => " 123.456e5", double);
    expr_test!(float_neg_sci => "-123.456e5", double);

    expr_test!(big_integer => "0xFFFF_FFFF_FFFF_FFFF_FFFF", BigInteger);
    expr_test!(big_decimal => "1234567890_1234567890_1234567890_1234567890e10000", BigDecimal);
  }

  mod booleans {
    use super::*;

    expr_test!(true_  => "true",  boolean);
    expr_test!(false_ => "false", boolean);
  }

  mod unary {
    use super::*;

    expr_test!(neg_byte  => "-1", byte);
    expr_test!(neg_short => "-1", short);
    expr_test!(neg_int   => "-1", int);
    expr_test!(neg_long  => "-1", long);
    expr_test!(not => "not true", boolean);
    expr_test!(inv_byte  => "~1", byte);
    expr_test!(inv_short => "~1", short);
    expr_test!(inv_int   => "~1", int);
    expr_test!(inv_long  => "~1", long);
  }

  mod binary {
    use super::*;

    expr_test!(add => "1 + 2", int);
    expr_test!(sub => "1 - 2", int);
    expr_test!(mul => "1 * 2", int);
    expr_test!(div => "1 / 2", int);
    expr_test!(rem => "1 % 2", int);

    expr_test!(eq => "1 == 2", boolean);
    expr_test!(ne => "1 != 2", boolean);
    expr_test!(le => "1 <= 2", boolean);
    expr_test!(ge => "1 >= 2", boolean);
    expr_test!(lt => "1 < 2",  boolean);
    expr_test!(gt => "1 > 2",  boolean);

    expr_test!(and => "true and false", boolean);
    expr_test!(or  => "true or false",  boolean);

    expr_test!(bit_and => "1 & 2", int);
    expr_test!(bit_or  => "1 | 2", int);
    expr_test!(bit_xor => "1 ^ 2", int);
  }

  expr_test!(ternary => r#"1 == 2 ? "equal" : "not equal""#, String);

  expr_test!(attr => r#"to_string"#, String);
  expr_test!(call => r#"callable(1, 2, argument)"#, char);
  expr_test!(method_call => r#"object.callable(1, 2, argument)"#, char);
  expr_test!(access => r#"to_string.hash_code"#, int);
}

#[cfg(test)]
mod variant {
  use super::*;
  use indexmap::indexmap;
  use std::path::Path;

  struct Empty(&'static str);
  impl Translate for Empty {
    fn translate(&self, _gen: &TypeGenerator) -> TokenStream {
      let text = self.0;
      quote!(System.out.println(#text);)
    }
  }

  /// Translates the following expression:
  ///
  /// ```yaml
  /// switch-on: 0
  /// cases:
  ///   0: branch 0
  ///   1: branch 1
  /// ```
  #[test]
  fn switch() {
    let variant = Variant::Choice {
      switch_on: OwningNode::Int(0.into()),
      cases: indexmap![
        OwningNode::Int(0.into()) => Empty("branch 0"),
        OwningNode::Int(1.into()) => Empty("branch 1"),
      ],
    };

    let gen = TypeGenerator { field_names: IndexMap::new() };
    let tokens = variant.translate(&gen);
    println!("translated: {}", tokens);

    compile(&Path::new("variant").join("switch"), &format!(r#"
    public class KscJavaTest {{
      void test() {{
        {}
      }}
    }}
    "#, tokens));
  }

  /// Translates the following expression:
  ///
  /// ```yaml
  /// switch-on: 0
  /// cases:
  ///   i: branch 0
  ///   j: branch 1
  /// ```
  ///
  /// Because cases are not constant, `if-else` chains is used
  #[test]
  fn if_() {
    let case1 = parse("i");
    let case2 = parse("j");

    let variant = Variant::Choice {
      switch_on: OwningNode::Int(0.into()),
      cases: indexmap![
        case1 => Empty("branch 0"),
        case2 => Empty("branch 1"),
      ],
    };

    let gen = TypeGenerator { field_names: IndexMap::new() };
    let tokens = variant.translate(&gen);
    println!("translated: {}", tokens);

    compile(&Path::new("variant").join("switch"), &format!(r#"
    public class KscJavaTest {{
      // Methods called by the translator
      void i() {{}}
      void j() {{}}
      void test() {{
        {}
      }}
    }}
    "#, tokens));
  }
}

#[cfg(test)]
mod attribute {
  use super::*;
  use ksc::model::{Chunk, TypeRef};
  use std::path::Path;

  #[track_caller]
  fn compile(path: &Path, attr: Attribute) {
    let gen = TypeGenerator { field_names: IndexMap::new() };
    let tokens = gen.translate_attribute(&SeqName::Unnamed(0), &attr);
    println!("translated: {}", tokens);

    super::compile(path, &format!(r#"
    import java.util.ArrayList;
    abstract interface KaitaiStream {{
      boolean isEof();
      KaitaiStream subStream(int size);
    }}
    public abstract class KscJavaTest {{
      KaitaiStream _io;
      abstract Object unimplemented();
      void test() {{
        {}
      }}
    }}
    "#, tokens));
  }

  mod repeat {
    use super::*;

    #[test]
    fn eos() {
      compile(&Path::new("attribute").join("repeat").join("eos"), Attribute {
        chunk: Variant::Fixed(Chunk {
          type_ref: TypeRef::Bytes,
          size: 10.into(),
        }),
        repeat: Repeat::Eos,
        condition: None,
        process: None,
      });
    }

    //TODO: finish repeat tests
    /*#[test]
    fn count() {
      use ksc::model::Count;
      compile(&Path::new("attribute").join("repeat").join("count"), Attribute {
        chunk: Variant::Fixed(Chunk {
          type_ref: TypeRef::Bytes,
          size: 10.into(),
        }),
        repeat: Repeat::Count(Count()),
        condition: None,
        process: None,
      });
    }

    #[test]
    fn until() {
      use ksc::model::Condition;
      compile(&Path::new("attribute").join("repeat").join("until"), Attribute {
        chunk: Variant::Fixed(Chunk {
          type_ref: TypeRef::Bytes,
          size: 10.into(),
        }),
        repeat: Repeat::Until(),
        condition: None,
        process: None,
      });
    }*/
  }
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

  #[test]
  fn check() {
    use std::io::Write;

    let tokens = gen("test.ksy");
    let ksc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let mut java = File::create(ksc_dir.join("test.java")).expect("cannot create temp file with java code");
    java.write_all(format!("{}", tokens).as_bytes()).expect("cannot write Java source code to the file");
  }
}
