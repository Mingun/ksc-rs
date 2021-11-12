//! Compiler backend for generate a Java source code from the Kaitai Struct definition.

use std::str::FromStr;

use heck::{ToUpperCamelCase, ToLowerCamelCase, ToShoutySnakeCase};
use num_traits::cast::ToPrimitive;
use ksc::model::{
  Attribute,
  EnumName,
  EnumValueName,
  FieldName,
  OptionalName,
  Repeat,
  Root,
  SeqName,
  TypeName,
  UserType,
  Variant,
};
use ksc::model::expressions::OwningNode;
use ksc::parser::expressions::SpecialName;
use proc_macro2::{Literal, Ident, Punct, Spacing, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt};

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
  fn translate_enum_name(&self, name: &EnumName) -> Ident {
    Ident::new(&name.to_upper_camel_case(), Span::call_site())
  }
  fn translate_enum_value_name(&self, name: &EnumValueName) -> Ident {
    Ident::new(&name.to_shouty_snake_case(), Span::call_site())
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
    let parsers = ty.fields.iter().map(|(n, a)| self.translate_attribute(n, a));

    let classes = ty.types.iter().map(|(n, t)| self.translate_type(n, t, true));

    quote! {
      #header
      public #static_ class #name implements PositionInfo {
        #(#fields)*

        public final Map<String, Span> _spans = new HashMap<>();

        #(#classes)*

        @Override
        public Map<String, Span> _spans() { return _spans; }

        public _read() {
          #(#parsers)*
        }
      }
    }
  }
  fn translate_attribute(&self, name: &SeqName, attr: &Attribute) -> TokenStream {
    let ty = quote!(Object);//TODO: calculate type
    let stream = quote!(this._io);//TODO: calculate stream
    let parse = quote!(unimplemented());//TODO: implement parse of attribute

    let statement = match &attr.repeat {
      Repeat::None => quote!(#parse;),
      Repeat::Eos => quote!({
        int i = 0;
        final ArrayList<#ty> _arr = new ArrayList<#ty>();
        while (!#stream.isEof()) {
          _arr.add(#parse);
          i += 1;
        }
      }),
      Repeat::Count(count) => {
        let count = count.translate(self);
        quote!({
          int _count = #count;
          final ArrayList<#ty> _arr = new ArrayList<#ty>(_count);
          for (int i = 0; i < _count; i += 1) {
            _arr.add(#parse);
          }
        })
      },
      Repeat::Until(condition) => {
        let condition = condition.translate(self);
        quote!({
          int i = 0;
          final ArrayList<#ty> _arr = new ArrayList<#ty>();
          do {
            _arr.add(#parse);
            i += 1;
          } while (!#condition);
        })
      },
    };

    if let Some(condition) = &attr.condition {
      let condition = condition.translate(self);
      // Braces not required here because every expression already in braces
      quote!(if (#condition) #statement)
    } else {
      statement
    }
  }
  /// Translate Kaitai Struct expression into Java expression
  ///
  /// # Parameters
  /// - `tokens`: this token stream will filled with expression
  /// - `expression`: expression to translate
  fn translate_expression(&self, tokens: &mut TokenStream, expression: &OwningNode) {
    use OwningNode::*;
    use ksc::parser::expressions::UnaryOp::*;

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

      //TODO: завершить трансляцию выражений
      Attr(attr) => {// this.<attr>()
        tokens.append_all(quote!(this.));
        self.translate_field(attr).to_tokens(tokens);
        tokens.append_all(quote!{()});
      },
      //SpecialName(n),
      EnumValue { scope, name, value } => {
        let scope = scope.path.iter().map(|p| self.translate_type_name(p));
        let name  = self.translate_enum_name(name);
        let value = self.translate_enum_value_name(value);

        tokens.append_all(quote!(#(#scope.)* #name . #value));
      },

      // List(arr),

      // SizeOf { type_, bit },

      Call { callee, method, args } => {//TODO: Fix call generation
        self.translate_expression(tokens, callee);
        Punct::new('.', Spacing::Alone).to_tokens(tokens);
        method.to_tokens(tokens);
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
      Access { expr, attr } => {// <expr>.<attr>()
        self.translate_expression(tokens, expr);
        tokens.append_all(quote!(.));
        self.translate_field(attr).to_tokens(tokens);
        tokens.append_all(quote!{()});
      },

      Unary { op: Neg, expr } => { tokens.append_all(quote!(-)); self.translate_expression(tokens, expr) },
      Unary { op: Not, expr } => { tokens.append_all(quote!(!)); self.translate_expression(tokens, expr) },
      Unary { op: Inv, expr } => { tokens.append_all(quote!(~)); self.translate_expression(tokens, expr) },
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
        tokens.append_all(quote!(?));
        self.translate_expression(tokens, if_true);
        tokens.append_all(quote!(:));
        self.translate_expression(tokens, if_false);
      },
      e => unimplemented!("translating complex expressions not yet implemented. Expression:\n{:#?}", e),
    }
  }
}

/// Internal trait to facilitate translation of recursive structures
trait Translate {
  /// Translates self into a piece of Java code using settings in `gen`
  fn translate(&self, gen: &JavaGenerator) -> TokenStream;
}

impl Translate for OwningNode {
  fn translate(&self, gen: &JavaGenerator) -> TokenStream {
    let mut tokens = TokenStream::new();
    gen.translate_expression(&mut tokens, self);
    tokens
  }
}

impl<T: Translate> Translate for Variant<T> {
  fn translate(&self, gen: &JavaGenerator) -> TokenStream {
    match self {
      Variant::Fixed(value) => value.translate(gen),
      Variant::Choice { switch_on, cases } => {
        let choice = switch_on.translate(gen);

        //TODO: use `if` for complex cases
        let cases = cases.iter().map(|(case, body)| {
          let body = body.translate(gen);
          match case {
            OwningNode::SpecialName(SpecialName::Value) => quote! {
              default: {
                #body
                break;
              }
            },
            _ => {
              let case = case.translate(gen);
              quote! {
                case #case: {
                  #body
                  break;
                }
              }
            },
          }
        });

        quote! {
          switch (#choice) {
            #(#cases)*
          }
        }
      },
    }
  }
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
    .expect("failed to execute javac. Is JDK installed?");

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
mod expressions {
  use super::*;
  use std::path::Path;

  /// Translates Kaitai Struct expression into a Java expression and check that it compiles
  fn translate(test_name: &str, java_type: &str, expr: &str) {
    let expr = OwningNode::parse(expr).expect("incorrect Kaitai expression");

    let gen = JavaGenerator;
    let tokens = expr.translate(&gen);
    println!("translated: {}", tokens);

    compile(Path::new(test_name), &format!(r#"
    // For numbers test
    import java.math.BigDecimal;
    import java.math.BigInteger;
    public class KscJavaTest {{
      // Helper functions for `call` test
      String argument() {{ return ""; }}
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
  expr_test!(access => r#"to_string.hash_code"#, int);
}

#[cfg(test)]
mod variant {
  use super::*;
  use indexmap::indexmap;
  use std::path::Path;

  struct Empty(&'static str);
  impl Translate for Empty {
    fn translate(&self, _gen: &JavaGenerator) -> TokenStream {
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

    let gen = JavaGenerator;
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
    let case1 = OwningNode::parse("i").unwrap();
    let case2 = OwningNode::parse("j").unwrap();

    let variant = Variant::Choice {
      switch_on: OwningNode::Int(0.into()),
      cases: indexmap![
        case1 => Empty("branch 0"),
        case2 => Empty("branch 1"),
      ],
    };

    let gen = JavaGenerator;
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
}

#[cfg(test)]
mod attribute {
  use super::*;
  use ksc::model::{Chunk, TypeRef};
  use std::path::Path;

  #[track_caller]
  fn compile(path: &Path, attr: Attribute) {
    let gen = JavaGenerator;
    let tokens = gen.translate_attribute(&SeqName::Unnamed(0), &attr);
    println!("translated: {}", tokens);

    super::compile(path, &format!(r#"
    import java.util.ArrayList;
    public abstract class KscJavaTest {{
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
  use std::convert::TryInto;
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
    let ksy: Ksy = serde_yaml::from_reader(file).expect(&format!("invalid file {}", path.display()));
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
    super::compile(path.parent().unwrap(), &gen(resource).to_string());
  }
}
