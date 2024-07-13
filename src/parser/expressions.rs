//! Parser and AST for Kaitai Struct expression language.

//TODO: Describe the language

use std::char;
use std::iter::FromIterator;

use bigdecimal::{BigDecimal, Num};
use bigdecimal::num_bigint::BigInt;
use serde_yml::Number;

use crate::parser::BitOrder;

// Re-export parsing functions from generated parser module
pub use parser::*;

/// AST Node, that represent some syntax construct
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node<'input> {
  /// String constant
  Str(String),
  /// Integral constant
  Int(BigInt),
  /// Floating-point constant
  Float(BigDecimal),
  /// Boolean constant
  Bool(bool),

  /// Name of field of the type in which attribute expression is defined
  Attr(&'input str),
  /// Built-in variable
  SpecialName(SpecialName),
  /// Reference to an enum value.
  EnumValue {
    /// A type that defines this enum.
    scope: Scope<'input>,
    /// An enum name.
    name: &'input str,
    /// An enum value.
    value: &'input str,
  },

  /// Array constructor
  List(Vec<Node<'input>>),

  /// Calculation of size of type
  SizeOf {
    /// Reference to type for which size must be calculated
    type_: TypeRef<'input>,
    /// if `true`, calculate size in bits, otherwise in bytes
    bit: bool,
  },

  /// Calling function or method: `${expr}(${args})`.
  Call {
    /// Expression which is called
    callee: Box<Node<'input>>,
    /// Arguments of method call
    args: Vec<Node<'input>>,
  },
  /// Conversion to type: `${expr}.as<${to_type}>`.
  Cast {
    /// Expression for conversion
    expr: Box<Node<'input>>,
    /// Reference to type for conversion
    to_type: TypeRef<'input>,
  },
  /// Access to expression by some index
  Index {
    /// Expression for indexing
    expr: Box<Node<'input>>,
    /// Index expression
    index: Box<Node<'input>>,
  },
  /// Access to some attribute of expression
  Access {
    /// Expression which attribute must be evaluated
    expr: Box<Node<'input>>,
    /// Retrieved attribute
    attr: &'input str,
  },

  /// The unary prefix operator, such as unary `-` or logical `not`.
  Unary {
    /// Operation to apply
    op: UnaryOp,
    /// Expression for applying operator
    expr: Box<Node<'input>>
  },
  /// The binary infix operator, such as `+` or `==`.
  Binary {
    /// Operation between left and right parts of expression
    op: BinaryOp,
    /// Left part of operator
    left: Box<Node<'input>>,
    /// Right part of operator
    right: Box<Node<'input>>,
  },
  /// Conditional expression, written as ternary operator
  Branch {
    /// Expression to check. Should evaluate to boolean value
    condition: Box<Node<'input>>,
    /// Expression that should be calculated in case of `true` `condition`.
    if_true:   Box<Node<'input>>,
    /// Expression that should be calculated in case of `false` `condition`.
    if_false:  Box<Node<'input>>,
  },
}
impl<'input> From<Number> for Node<'input> {
  fn from(number: Number) -> Self {
    if let Some(n) = number.as_u64() {
      return Node::Int(n.into());
    }
    if let Some(n) = number.as_i64() {
      // Can return only negative integers, because positive is handled above
      return Node::Int(n.into());
    }
    if let Some(n) = number.as_f64() {
      return Node::Float(n.try_into().unwrap());
    }
    unreachable!("internal error: YAML number is not an u64/i64/f64")
  }
}

macro_rules! from_int {
  ($($ty:ty,)*) => {$(
    impl<'input> From<$ty> for Node<'input> {
      #[inline]
      fn from(number: $ty) -> Self {
        Self::Int(number.into())
      }
    }
  )*};
}
from_int!(
  u8,
  u16,
  u32,
  u64,
  u128,
  usize,

  i8,
  i16,
  i32,
  i64,
  i128,
  isize,
);
impl<'input> From<bool> for Node<'input> {
  #[inline]
  fn from(value: bool) -> Self {
    Self::Bool(value)
  }
}
impl<'input, 'a> From<&'a str> for Node<'input> {
  #[inline]
  fn from(string: &'a str) -> Self {
    Self::Str(string.into())
  }
}
impl<'input> From<String> for Node<'input> {
  #[inline]
  fn from(string: String) -> Self {
    Self::Str(string)
  }
}
impl<'input> From<SpecialName> for Node<'input> {
  #[inline]
  fn from(value: SpecialName) -> Self {
    Self::SpecialName(value)
  }
}

/// A scope in which types and enums are defined, used to resolve references
/// to them in the expressions.
///
/// Technically, in Kaitai Struct it matches the one of the [type names],
/// but generators feel free to choose another representation for the
/// scope that matches the language best practices.
///
/// [type names]: ../parser/struct.TypeSpec.html#structfield.types
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Scope<'input> {
  /// Path starts from a top-level type of the current KSY file.
  pub absolute: bool,
  /// Names of types defining this scope.
  pub path: Vec<&'input str>,
}

/// A possible qualified type name, used in references
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeName<'input> {
  /// A scope in which type is defined
  pub scope: Scope<'input>,
  /// A local name of the referenced type
  pub name: &'input str,
}

/// Represents a reference to a type definition, used in the cast and sizeof
/// expressions.
///
/// Reference to a type consist of:
/// - optional absolute path specifier (`::`)
/// - zero or more types in which required type is defined, delimited by `::`
/// - (local) name of the required type
/// - optional array specifier (`[]`)
///
/// Examples:
/// - `simple_type`
/// - `array_type[]`
/// - `path::to_inner::type`
/// - `::absolute::path`
///
/// `'input` lifetime is bound to the lifetime of a parsed string. Each element
/// in a path just a slice inside the original string.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeRef<'input> {
  /// A possible qualified type name of the type used
  pub name: TypeName<'input>,
  /// If `true` then reference represents an array of the specified type.
  pub array: bool,
}

/// Names with a special meaning
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecialName {
  /// `_io`: stream associated with this object of user-defined type.
  Stream,
  /// `_root`: top-level user-defined structure in the current file.
  Root,
  /// `_parent`: structure that produced this particular instance of the
  /// user-defined type.
  Parent,
  /// `_index`: current repetition index in repeated attribute. Valid only
  /// in attributes with [`repeat`] keys.
  ///
  /// [`repeat`]: ../parser/struct.Attribute.html#structfield.repeat
  Index,
  /// `_`: current attribute value. Usually used in the [`repeat-until`]
  /// expression to refer to the last parsed object, but also can be used
  /// as a value of the [`case`] in `switch-on` (because `case` labels in
  /// that construction is expressions).
  ///
  /// [`repeat-until`]: ../parser/struct.Attribute.html#structfield.repeat_until
  /// [`case`]: ../parser/enum.Variant.html#variant.Choice.field.cases
  Value,
  /// `_buf`: current unparsed attribute value, available only in the [`repeat-until`]
  /// expression.
  ///
  /// [`repeat-until`]: ../parser/struct.Attribute.html#structfield.repeat_until
  RawValue,
  /// `_sizeof`: used as an attribute of the struct to get a compile-time size
  /// of the structure:
  ///
  /// ```yaml
  /// seq:
  /// - id: file_hdr
  ///   type: file_header
  /// - id: dib_info
  ///   size: file_hdr.ofs_bitmap - file_hdr._sizeof
  /// ```
  SizeOf,
  /// `_on`: result of the [`switch-on`] expression.
  ///
  /// [`switch-on`]: ../parser/enum.Variant.html#variant.Choice.field.switch_on
  SwitchOn,//TODO: probably not available in the expression language - no examples of usage
  /// `_is_le`.
  IsLe,//TODO: what's this?
}

/// List of possible unary operations
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
  /// `-`: The unary negation operator.
  Neg,
  /// `not`: The unary logical negation operator.
  Not,
  /// `~`: The unary bit inversion operator.
  Inv,
}

/// List of possible operations over two arguments. All operations is left-associative
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
  /// `+`: Addition of two numeric arguments or concatenation of two strings.
  Add,
  /// `-`: Subtraction of two numeric arguments.
  Sub,
  /// `*`: Multiplication of two numeric arguments.
  Mul,
  /// `/`: Division of two numeric arguments.
  Div,
  /// `%`: Remainder of division of two numeric arguments.
  Rem,

  /// `<<`: The left shift operator.
  Shl,
  /// `>>`: The right shift operator.
  Shr,

  /// `==`: Equality operator
  Eq,
  /// `!=`: Non-equality operator
  Ne,
  /// `<=`: Less or equal operator
  Le,
  /// `>=`: Greater or equal operator
  Ge,
  /// `<`: Strict less operator
  Lt,
  /// `>`: Strict greater operator
  Gt,

  /// `and`: Two expressions evaluates to `true` iif both of them evaluates to `true`.
  And,
  /// `or`: Two expressions evaluates to `true` if at least one of them evaluates to `true`.
  Or,

  /// `&`: Performs bitwise AND operation
  BitAnd,
  /// `&`: Performs bitwise OR operation
  BitOr,
  /// `^`: Performs bitwise XOR (exclusive-or) operation
  BitXor,
}
impl BinaryOp {
  #[inline]
  fn into_node<'i>(self, left: Node<'i>, right: Node<'i>) -> Node<'i> {
    Node::Binary { op: self, left: Box::new(left), right: Box::new(right) }
  }
}

/// A reference to the type in the attributes' [`type`] field.
///
/// [`type`]: ../parser/struct.Attribute.html#structfield.type_
#[derive(Debug, PartialEq)]
pub enum AttrType<'input> {
  /// Type is a built-in arbitrary-sized bit type
  Bits {
    /// The size of an integer in bits
    size: usize,
    /// The order in which bits is layed out in the stream
    order: Option<BitOrder>,
  },
  /// Type is a reference to another user-defined type
  User {
    /// A possible qualified type name of the type used
    name: TypeName<'input>,
    /// Optional arguments for a type
    args: Vec<Node<'input>>,
  },
}

/// Name and parameters of process routine.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ProcessAlgo<'input> {
  /// Name of process routine
  pub name: &'input str,
  /// Optional arguments for routine
  pub args: Vec<Node<'input>>,
}

/// Represents postfix operators.
///
/// Temporary hold operators until all postfix operators is parsed,
/// then converted to `Node` with `make_chain` call.
enum Postfix<'input> {
  /// Calling function or method with specified arguments.
  Args(Vec<Node<'input>>),
  /// Conversion to specified type.
  CastTo(TypeRef<'input>),
  /// Index expression
  Index(Node<'input>),
  /// Field name for attribute access
  Field(&'input str),
}

/// Helper function to convert escape codes to characters
#[inline]
fn to_char(number: &str, radix: u32) -> Result<char, &'static str> {
  let code = u32::from_str_radix(&number.replace('_', ""), radix)
                 .map_err(|_| "escape sequence must contain at least one digit");

  char::from_u32(code?).ok_or("unknown character for escape sequence")
}
/// Helper function to convert parsed numbers from string to integer
#[inline]
fn to_int(number: &str, radix: u32) -> Result<BigInt, &'static str> {
  BigInt::from_str_radix(&number.replace('_', ""), radix)
      .map_err(|_| "integer literal must contain at least one digit")
}
/// Helper function to convert parsed escape characters mnemonics to characters itself
#[inline]
fn to_escaped(ch: &str) -> char {
  match ch.chars().next().unwrap() {
    'a' => '\x07',// bell
    'b' => '\x08',// backspace
    't' => '\t',
    'n' => '\n',
    'v' => '\x0B',// vertical tab
    'f' => '\x0C',// formfeed page break
    'r' => '\r',
    'e' => '\x1B',// escape
    '\''=> '\'',
    '"' => '"',
    '\\'=> '\\',

    // this function called only with above list of characters
    _ => unreachable!(),
  }
}
/// Helper function to create left-associative chain of calls of postfix operators.
#[inline]
fn make_chain<'i>(mut expr: Node<'i>, tail: Vec<Postfix<'i>>) -> Node<'i> {
  for p in tail {
    expr = match p {
      Postfix::Args(args)      => Node::Call   { callee: Box::new(expr), args },
      Postfix::CastTo(to_type) => Node::Cast   { expr: Box::new(expr), to_type },
      Postfix::Index(index)    => Node::Index  { expr: Box::new(expr), index: Box::new(index) },
      Postfix::Field(attr)     => Node::Access { expr: Box::new(expr), attr },
    }
  }
  expr
}
/// Helper function to create left-associative chain of calls of infix operators.
#[inline]
fn left_associative<'i, T>(mut left: Node<'i>, tail: T) -> Node<'i>
  where T: IntoIterator<Item = (BinaryOp, Node<'i>)>,
{
  for right in tail.into_iter() {
    left = right.0.into_node(left, right.1);
  }
  left
}

peg::parser! {
  /// Contains generated parser for Kaitai Struct expression language.
  grammar parser() for str {
    use UnaryOp::*;
    use BinaryOp::*;

    /// Entry point for parsing names of attributes, types, enumerations etc.
    pub rule parse_name() -> &'input str = $(['a'..='z' | 'A'..='Z'] name_part()*);

    /// Entry point for parsing expressions in `if`, `io`, `pos`, `repeat-expr`,
    /// `repeat-until`, `size`, `switch-on`, `valid.min`, `valid.max`, `valid.expr`,
    /// `value`.
    pub rule parse_single() -> Node<'input> = _ e:expr() _ EOS() {e};

    /// Entry point for parsing [`type`] field value.
    ///
    /// [`type`]: ../../parser/struct.Attribute.html#structfield.type_
    pub rule parse_type_ref() -> AttrType<'input>
      = _ r:(bits_type() / user_type()) _ EOS() { r };

    /// Entry point for parsing [`process`] field value.
    ///
    /// [`process`]: ../../parser/struct.Attribute.html#structfield.process
    pub rule parse_process() -> ProcessAlgo<'input>
        //TODO: Original KSC do not allow spaces before "(" and after ")"
        // https://github.com/kaitai-io/kaitai_struct/issues/792
      = name:name() args:("(" _ args:args() _ ")" { args })? EOS() {
        ProcessAlgo { name, args: args.unwrap_or_default() }
      };

    /// Whitespace rule
    rule _() = quiet!{([' '|'\n']+ / "\\\n" / comment())*};

    rule comment() = "#" (!EOL() [_])* EOL();

    /// End-Of-Line
    rule EOL() = ['\n'] / EOS();
    /// End-Of-Stream
    rule EOS() = ![_];

    rule string() -> String
      = "'" s:$([x if x != '\'']*) "'"  { s.to_owned() }
      / "\"" v:(ch() / escaped())* "\"" { String::from_iter(v.into_iter()) }
      ;

    /// Single non-escaped character in string
    rule ch() -> char = ch:$[x if x != '\\' && x != '"'] { ch.chars().next().unwrap() };
    /// One escaped character
    rule escaped() -> char = "\\" r:(quoted_char() / quoted_oct() / quoted_hex()) { r };
    /// Characters that can be escaped by backslash
    rule quoted_char() -> char = ch:$['a'|'b'|'t'|'n'|'v'|'f'|'r'|'e'|'\''|'"'|'\\'] { to_escaped(ch) };
    rule quoted_oct() -> char  = s:$(oct()+) {? to_char(s, 8) };
    rule quoted_hex() -> char  = ['u'] s:$(hex()*<4>) {? to_char(s, 16) };

    rule integer() -> BigInt
      = n:$(['1'..='9'] ['0'..='9' | '_']*) {? to_int(n, 10) }
      / "0" ['b' | 'B'] n:$(bin()+) {? to_int(n,  2) }
      / "0" ['o' | 'O'] n:$(oct()+) {? to_int(n,  8) }
      / "0" ['x' | 'X'] n:$(hex()+) {? to_int(n, 16) }
      / "0" { 0.into() }
      ;
    rule oct() = ['0'..='7' | '_'];
    rule bin() = ['0'..='1' | '_'];
    rule hex() = ['0'..='9' | 'a'..='f' | 'A'..='F' | '_'];

    rule digit() = ['0'..='9'];

    rule float() -> BigDecimal = n:$(//TODO: allow '_' in floats
        digit()+ exponent()   // Ex.: 4E2, 4E+2, 4e-2
      / fixed() exponent()?   // Ex.: 4.E2, .4e+2, 4.2e-0
    ) {? n.replace('_', "").parse().map_err(|_| "float literal must contain at least one digit") };
    rule fixed()
      = digit()* "." digit()+        // Ex.: 4.2, .42
      / digit()+ "." !(_ name_start())// Ex.: 42.
      ;
    rule exponent() = ['e' | 'E'] ['+' | '-']? digit()+;

    //-------------------------------------------------------------------------------------------------

    rule name() -> &'input str = $(name_start() name_part()*);
    rule name_start() = ['a'..='z' | 'A'..='Z' | '_'];
    rule name_part()  = ['a'..='z' | 'A'..='Z' | '_' | '0'..='9'];

    /// Reference to the type for casts and evaluating size.
    ///
    /// Ex.: `xyz`, `::abc::def`, `array[]`
    rule type_ref() -> TypeRef<'input>
      = name:type_name() array:(_ "[" _ "]")? {
        TypeRef { name, array: array.is_some() }
      };
    /// Ex.: `enum::value`, `::root::type::enum::value`
    rule enum_name() -> Node<'input>
      = absolute:"::"? _ n1:name() _ "::" _ n2:name() tail:(_ "::" _ n:name() {n})* {
        let mut path = vec![n1, n2];
        path.extend(tail);
        //TODO: use unwrap_unchecked when it's stabilized
        let value = path.pop().unwrap();
        let name  = path.pop().unwrap();

        Node::EnumValue {
          scope: Scope { absolute: absolute.is_some(), path },
          name,
          value,
        }
      };

    //-------------------------------------------------------------------------------------------------
    // Operators
    //-------------------------------------------------------------------------------------------------

    rule OR()  -> Node<'input> = _ "or"  !name_part() _ e:and_test() {e};
    rule AND() -> Node<'input> = _ "and" !name_part() _ e:and_test() {e};
    rule NOT() -> Node<'input> = _ "not" !name_part() _ e:and_test() {e};

    rule expr() -> Node<'input>
      = condition:or_test() branch:(_ "?" _ t:expr() _ ":" _ f:expr() {(t, f)})? {
        if let Some((t, f)) = branch {
          Node::Branch {
            condition: Box::new(condition),
            if_true:   Box::new(t),
            if_false:  Box::new(f),
          }
        } else {
          condition
        }
      };
    rule or_test()  -> Node<'input> = l:and_test() r:OR()*  { left_associative(l, r.into_iter().map(|e| (Or, e))) };
    rule and_test() -> Node<'input> = l:not_test() r:AND()* { left_associative(l, r.into_iter().map(|e| (And, e))) };

    rule not_test() -> Node<'input>
      = e:NOT() { Node::Unary { op: Not, expr: Box::new(e) } }
      / l:or_expr() r:(_ op:comp_op() _ e:or_expr() { (op, e) })?
        { if let Some((op, r)) = r { op.into_node(l, r) } else { l } }
      ;

    rule comp_op() -> BinaryOp
      = "==" { Eq }
      / "!=" { Ne }
      / "<=" { Le }
      / ">=" { Ge }
      / "<"  { Lt }
      / ">"  { Gt }
      ;
    rule shift_op() -> BinaryOp
      = "<<" { Shl }
      / ">>" { Shr }
      ;
    rule add_op() -> BinaryOp
      = "+" { Add }
      / "-" { Sub }
      ;
    rule mul_op() -> BinaryOp
      = "*" { Mul }
      / "/" { Div }
      / "%" { Rem }
      ;

    rule or_expr()    -> Node<'input> = l:xor_expr()   r:(_ "|"           _ e:xor_expr()   {e})* { left_associative(l, r.into_iter().map(|e| (BitOr , e))) };
    rule xor_expr()   -> Node<'input> = l:and_expr()   r:(_ "^"           _ e:and_expr()   {e})* { left_associative(l, r.into_iter().map(|e| (BitXor, e))) };
    rule and_expr()   -> Node<'input> = l:shift_expr() r:(_ "&"           _ e:shift_expr() {e})* { left_associative(l, r.into_iter().map(|e| (BitAnd, e))) };
    rule shift_expr() -> Node<'input> = l:arith_expr() r:(_ op:shift_op() _ e:arith_expr() {(op, e)})* { left_associative(l, r) };
    rule arith_expr() -> Node<'input> = l:term()       r:(_ op:add_op()   _ e:term()       {(op, e)})* { left_associative(l, r) };
    rule term()       -> Node<'input> = l:factor()     r:(_ op:mul_op()   _ e:factor()     {(op, e)})* { left_associative(l, r) };

    rule factor() -> Node<'input>
      = "+" _ e:factor() { e }
      / "-" _ e:factor() { Node::Unary { op:Neg, expr: Box::new(e) } }
      / "~" _ e:factor() { Node::Unary { op:Inv, expr: Box::new(e) } }
      / e:atom() p:(_ e:postfix() {e})* { make_chain(e, p) }
      ;

    rule atom() -> Node<'input>
      = "(" _ e:expr() _ ")"                   { e }
      / "[" _ l:list()? _ "]"                  { Node::List(l.unwrap_or_default()) }
      / "sizeof" _ "<" _ t:type_ref() _ ">"    { Node::SizeOf { type_: t, bit: false } }
      / "bitsizeof" _ "<" _ t:type_ref() _ ">" { Node::SizeOf { type_: t, bit: true  } }
      / v:(s:string() _ {s})+                  { Node::Str(String::from_iter(v.into_iter())) }
      / n:special_name() !name_part()          { n }
      / e:enum_name()                          { e }
      / n:name()                               { Node::Attr(n) }
      / f:float()                              { Node::Float(f) }
      / i:integer()                            { Node::Int(i) }
      ;

    rule special_name() -> Node<'input>
      = "true"    { Node::Bool(true) }
      / "false"   { Node::Bool(false) }
      / "_io"     { Node::SpecialName(SpecialName::Stream) }
      / "_on"     { Node::SpecialName(SpecialName::SwitchOn) }
      / "_root"   { Node::SpecialName(SpecialName::Root) }
      / "_parent" { Node::SpecialName(SpecialName::Parent) }
      / "_index"  { Node::SpecialName(SpecialName::Index) }
      / "_is_le"  { Node::SpecialName(SpecialName::IsLe) }
      / "_sizeof" { Node::SpecialName(SpecialName::SizeOf) }
      / "_"       { Node::SpecialName(SpecialName::Value) }
      ;
    rule postfix() -> Postfix<'input>
      = "(" _ a:args() _ ")"                  { Postfix::Args(a)   }// call
      / "[" _ e:expr() _ "]"                  { Postfix::Index(e)  }// indexing
      / "." _ "as" _ "<" _ t:type_ref() _ ">" { Postfix::CastTo(t) }// type cast
      / "." _ n:name()                        { Postfix::Field(n)  }// attribute access
      ;

    /// List of names, delimited by `::`, with an optional leading `::`.
    ///
    /// At least one name is guaranteed
    rule type_name() -> TypeName<'input>
      = absolute:"::"? _ path:name() ++ (_ "::" _) {
        let mut path = path;
        // `path` guarantee that path will contain at least one element
        //TODO: use unwrap_unchecked when it's stabilized
        let name = path.pop().unwrap();
        TypeName {
          scope: Scope { absolute: absolute.is_some(), path },
          name,
        }
      };
    /// List of expressions, delimited by comma, allowing dangling comma
    rule list() -> Vec<Node<'input>> = list:args() _ ","? { list };
    /// List of expressions, delimited by comma
    rule args() -> Vec<Node<'input>> = args:expr() ** (_ "," _) { args };

    //-------------------------------------------------------------------------------------------------
    /// Variants of bit endianness in bit-sized integers
    rule endian() -> BitOrder
      = "le" { BitOrder::Le }
      / "be" { BitOrder::Be }
      ;
    rule bits_type() -> AttrType<'input>
      //FIXME: leading zeroes looks strange: https://github.com/kaitai-io/kaitai_struct/issues/939
      = "b" n:$(['0'..='9']+) order:endian()? {?
        Ok(AttrType::Bits {
          size: n.parse().map_err(|_| "bit size is too long")?,
          order,
        })
      };
    rule user_type() -> AttrType<'input>
      = name:type_name() args:(_ "(" _ args:args() _ ")" { args })? {
        AttrType::User { name, args: args.unwrap_or_default() }
      };
  }
}

#[cfg(test)]
mod parse {
  // Colorful diffs in assertions
  use pretty_assertions::assert_eq;
  use super::{AttrType, BigDecimal, BigInt, BitOrder, Node, Scope, TypeName, TypeRef};
  use super::Node::*;
  use super::UnaryOp::*;
  use super::BinaryOp::*;

  /// Wrapper, for use with https://github.com/fasterthanlime/pegviz
  fn parse_single(input: &str) -> Result<Node, peg::error::ParseError<peg::str::LineCol>> {
    println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
    let result = super::parse_single(input);
    println!("[PEG_TRACE_STOP]");
    result
  }

  mod comments {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn empty() {
      assert_eq!(parse_single("#\n123"), Ok(Int(123.into())));
    }
    #[test]
    fn following() {
      assert_eq!(parse_single("123# comment"), Ok(Int(123.into())));
      assert_eq!(parse_single("123\n# comment"), Ok(Int(123.into())));
    }
    #[test]
    fn leading() {
      assert_eq!(parse_single("# comment\n123"), Ok(Int(123.into())));
    }
    #[test]
    fn multi_line() {
      assert_eq!(parse_single(r#"
      1
      # multi-line
      # comment
      +
      # and yet
      # another
      2
      "#), Ok(Binary { op: Add, left: Int(1.into()).into(), right: Int(2.into()).into() }));
    }
  }

  mod dec {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn positive() {
      assert_eq!(parse_single("123"), Ok(Int(123.into())));
    }

    #[test]
    fn negative() {
      assert_eq!(parse_single("-456"), Ok(Unary { op: Neg, expr: Box::new(Int(456.into())) }));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("100_500"), Ok(Int(100_500.into())));
      assert_eq!(parse_single("100500_"), Ok(Int(100_500.into())));
    }
  }

  mod hex {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0x1234"), Ok(Int(0x1234.into())));
      assert_eq!(parse_single("0X1234"), Ok(Int(0x1234.into())));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0x_1234"), Ok(Int(0x1234.into())));
      assert_eq!(parse_single("0x12_34"), Ok(Int(0x1234.into())));
      assert_eq!(parse_single("0x1234_"), Ok(Int(0x1234.into())));

      assert_eq!(parse_single("0X_1234"), Ok(Int(0x1234.into())));
      assert_eq!(parse_single("0X12_34"), Ok(Int(0x1234.into())));
      assert_eq!(parse_single("0X1234_"), Ok(Int(0x1234.into())));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0x_").is_err());
      assert!(parse_single("0X_").is_err());
    }
  }

  mod oct {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0o644"), Ok(Int(0o644.into())));
      assert_eq!(parse_single("0O644"), Ok(Int(0o644.into())));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0o_0644"), Ok(Int(0o644.into())));
      assert_eq!(parse_single("0o06_44"), Ok(Int(0o644.into())));
      assert_eq!(parse_single("0o0644_"), Ok(Int(0o644.into())));

      assert_eq!(parse_single("0O_0644"), Ok(Int(0o644.into())));
      assert_eq!(parse_single("0O06_44"), Ok(Int(0o644.into())));
      assert_eq!(parse_single("0O0644_"), Ok(Int(0o644.into())));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0o_").is_err());
      assert!(parse_single("0O_").is_err());
    }
  }

  mod bin {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0b10101010"), Ok(Int(0b10101010.into())));
      assert_eq!(parse_single("0B10101010"), Ok(Int(0b10101010.into())));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0b_1010_1010"), Ok(Int(0b10101010.into())));
      assert_eq!(parse_single("0b1010_1_010"), Ok(Int(0b10101010.into())));
      assert_eq!(parse_single("0b1010_1010_"), Ok(Int(0b10101010.into())));

      assert_eq!(parse_single("0B_1010_1010"), Ok(Int(0b10101010.into())));
      assert_eq!(parse_single("0B1010_1_010"), Ok(Int(0b10101010.into())));
      assert_eq!(parse_single("0B1010_1010_"), Ok(Int(0b10101010.into())));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0b_").is_err());
      assert!(parse_single("0B_").is_err());
    }
  }

  mod float {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("1.2345"), Ok(Float((12345, 4).into())));
    }

    #[test]
    fn with_signless_exponent() {
      assert_eq!(parse_single("123e4"), Ok(Float((123, -4).into())));
      assert_eq!(parse_single("123E4"), Ok(Float((123, -4).into())));
    }

    #[test]
    fn with_positive_exponent() {
      assert_eq!(parse_single("123e+4"), Ok(Float((123, -4).into())));
      assert_eq!(parse_single("123E+4"), Ok(Float((123, -4).into())));
    }

    #[test]
    fn with_negative_exponent() {
      assert_eq!(parse_single("123e-7"), Ok(Float((123, 7).into())));
      assert_eq!(parse_single("123E-7"), Ok(Float((123, 7).into())));
    }

    #[test]
    fn non_integral_part_with_signless_exponent() {
      assert_eq!(parse_single("1.2345e7"), Ok(Float((12345, 4-7).into())));
      assert_eq!(parse_single("1.2345E7"), Ok(Float((12345, 4-7).into())));
    }

    #[test]
    fn non_integral_part_with_positive_exponent() {
      assert_eq!(parse_single("123.45e+7"), Ok(Float((12345, 2-7).into())));
      assert_eq!(parse_single("123.45E+7"), Ok(Float((12345, 2-7).into())));
    }

    #[test]
    fn non_integral_part_with_negative_exponent() {
      assert_eq!(parse_single("123.45e-7"), Ok(Float((12345, 2+7).into())));
      assert_eq!(parse_single("123.45E-7"), Ok(Float((12345, 2+7).into())));
    }

    #[test]
    fn big_numbers() {
      assert_eq!(
        parse_single("1234567890_1234567890_1234567890_1234567890"),
        Ok(Int(BigInt::parse_bytes(b"1234567890123456789012345678901234567890", 10).unwrap()))
      );
      assert_eq!(
        parse_single("1e+10000"),
        Ok(Float(BigDecimal::from((1, -10000))))
      );
    }
  }

  mod string {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("\"abc\""), Ok(Str("abc".into())));
    }

    #[test]
    fn interpolated_with_newline() {
      assert_eq!(parse_single("\"abc\\ndef\""), Ok(Str("abc\ndef".into())));
    }

    #[test]
    fn non_interpolated_with_newline() {
      assert_eq!(parse_single("'abc\\ndef'"), Ok(Str(r#"abc\ndef"#.into())));
    }

    #[test]
    fn interpolated_with_zero_char() {
      assert_eq!(parse_single("\"abc\\0def\""), Ok(Str("abc\0def".into())));
    }

    #[test]
    fn non_interpolated_with_zero_char() {
      assert_eq!(parse_single("'abc\\0def'"), Ok(Str(r#"abc\0def"#.into())));
    }

    #[test]
    fn interpolated_with_octal_char() {
      assert_eq!(parse_single("\"abc\\75def\""), Ok(Str("abc=def".into())));
    }

    #[test]
    fn interpolated_with_hex_unicode_char() {
      assert_eq!(parse_single("\"abc\\u21bbdef\""), Ok(Str("abc\u{21bb}def".into())));
    }

    mod escape_sequence {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;

      #[test]
      fn character() {
        assert_eq!(parse_single(r#""\a""#), Ok(Str("\x07".into())));
        assert_eq!(parse_single(r#""\b""#), Ok(Str("\x08".into())));
        assert_eq!(parse_single(r#""\t""#), Ok(Str("\t".into())));
        assert_eq!(parse_single(r#""\n""#), Ok(Str("\n".into())));
        assert_eq!(parse_single(r#""\v""#), Ok(Str("\x0B".into())));
        assert_eq!(parse_single(r#""\f""#), Ok(Str("\x0C".into())));
        assert_eq!(parse_single(r#""\r""#), Ok(Str("\r".into())));
        assert_eq!(parse_single(r#""\e""#), Ok(Str("\x1B".into())));
        assert_eq!(parse_single(r#""\'""#), Ok(Str("\'".into())));
        assert_eq!(parse_single(r#""\"""#), Ok(Str("\"".into())));
        assert_eq!(parse_single(r#""\\""#), Ok(Str("\\".into())));
      }

      #[test]
      fn oct() {
        assert_eq!(parse_single(r#""\0000""#), Ok(Str("\u{0}".into())));
        assert_eq!(parse_single(r#""\123""# ), Ok(Str("S".into())));
      }

      #[test]
      fn hex() {
        assert_eq!(parse_single(r#""\u0000""#), Ok(Str("\u{0}".into())));
        assert_eq!(parse_single(r#""\uFFFF""#), Ok(Str("\u{ffff}".into())));
      }

      #[test]
      fn with_underscores() {
        assert_eq!(parse_single(r#""\_00_00""#), Ok(Str("\u{0}".into())));
        assert_eq!(parse_single(r#""\__0000""#), Ok(Str("\u{0}".into())));
        assert_eq!(parse_single(r#""\0000__""#), Ok(Str("\u{0}".into())));

        //TODO: Unify behavior of Octal and Hex escape sequences in strings.
        //TODO: Better to disallow underscores
        assert_eq!(parse_single(r#""\u_00_00""#), Ok(Str("\u{0}00".into())));
        assert_eq!(parse_single(r#""\u__0000""#), Ok(Str("\u{0}00".into())));
        assert_eq!(parse_single(r#""\u0000__""#), Ok(Str("\u{0}__".into())));
      }

      #[test]
      fn with_only_underscores() {
        assert!(parse_single(r#""\_""#).is_err());
        assert!(parse_single(r#""\u____""#).is_err());
      }
    }

    mod concat {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;

      #[test]
      fn interpolated_strings() {
        assert_eq!(parse_single(r#""abc""def""#   ), Ok(Str("abcdef".into())));
        assert_eq!(parse_single(r#""abc" "def""#  ), Ok(Str("abcdef".into())));
        assert_eq!(parse_single("\"abc\"\n\"def\""), Ok(Str("abcdef".into())));
      }

      #[test]
      fn non_interpolated_strings() {
        assert_eq!(parse_single("'abc''def'"  ), Ok(Str("abcdef".into())));
        assert_eq!(parse_single("'abc' 'def'" ), Ok(Str("abcdef".into())));
        assert_eq!(parse_single("'abc'\n'def'"), Ok(Str("abcdef".into())));
      }

      #[test]
      fn mixed_strings() {
        assert_eq!(parse_single(r#""abc"'def'"#), Ok(Str("abcdef".into())));
        assert_eq!(parse_single(r#"'abc'"def""#), Ok(Str("abcdef".into())));

        assert_eq!(parse_single(r#""abc" 'def'"#), Ok(Str("abcdef".into())));
        assert_eq!(parse_single(r#"'abc' "def""#), Ok(Str("abcdef".into())));

        assert_eq!(parse_single("\"abc\"\n'def'"), Ok(Str("abcdef".into())));
        assert_eq!(parse_single("'abc'\n\"def\""), Ok(Str("abcdef".into())));
      }
    }
  }

  mod expr {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn unary() {
      macro_rules! test {
        ($string:expr => $op:ident) => {
          assert_eq!(parse_single($string), Ok(
            Unary {
              op: $op,
              expr: Box::new(Unary { op: $op, expr: Box::new(Int(1.into())) })
            }
          ));
        };
      }
      assert_eq!(parse_single("++1"), Ok(Int(1.into())));
      test!("--1" => Neg);
      test!("~~1" => Inv);
      test!("not not 1" => Not);
    }

    #[test]
    fn binary() {
      macro_rules! test {
        ($string:expr => $op:ident) => {
          assert_eq!(parse_single($string), Ok(Binary {
            op: $op,
            left: Box::new(Binary {
              op: $op,
              left:  Box::new(Int(1.into())),
              right: Box::new(Int(2.into())),
            }),
            right: Box::new(Int(3.into()))
          }));
        };
      }
      test!("1 + 2 + 3"   => Add);
      test!("1 - 2 - 3"   => Sub);
      test!("1 * 2 * 3"   => Mul);
      test!("1 / 2 / 3"   => Div);
      test!("1 % 2 % 3"   => Rem);
      test!("1 | 2 | 3"   => BitOr);
      test!("1 & 2 & 3"   => BitAnd);
      test!("1 ^ 2 ^ 3"   => BitXor);
      test!("1 << 2 << 3" => Shl);
      test!("1 >> 2 >> 3" => Shr);
    }

    #[test]
    fn ternary() {
      assert_eq!(parse_single("x ? \"foo\" : \"bar\""), Ok(
        Branch {
          condition: Box::new(Attr("x")),
          if_true:   Box::new(Str("foo".into())),
          if_false:  Box::new(Str("bar".into()))
        }
      ));
    }

    #[test]
    fn arith() {
      assert_eq!(parse_single("(1 + 2) / (7 * 8)"), Ok(
        Binary {
          op: Div,
          left: Box::new(Binary {
            op: Add,
            left: Box::new(Int(1.into())),
            right: Box::new(Int(2.into()))
          }),
          right: Box::new(Binary {
            op: Mul,
            left: Box::new(Int(7.into())),
            right: Box::new(Int(8.into()))
          }),
        }
      ));
    }

    #[test]
    fn comparison() {
      assert_eq!(parse_single("1 == 2"), Ok(
        Binary { op: Eq, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
      assert_eq!(parse_single("1 != 2"), Ok(
        Binary { op: Ne, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
      assert_eq!(parse_single("1 <= 2"), Ok(
        Binary { op: Le, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
      assert_eq!(parse_single("1 >= 2"), Ok(
        Binary { op: Ge, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
      assert_eq!(parse_single("1 < 2" ), Ok(
        Binary { op: Lt, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
      assert_eq!(parse_single("1 > 2" ), Ok(
        Binary { op: Gt, left: Box::new(Int(1.into())), right: Box::new(Int(2.into())) }
      ));
    }

    #[test]
    fn indexing() {
      assert_eq!(parse_single("a[42]"), Ok(
        Index { expr: Box::new(Attr("a")), index: Box::new(Int(42.into())) }
      ));
      assert_eq!(parse_single("a[42 - 2]"), Ok(
        Index {
          expr: Box::new(Attr("a")),
          index: Box::new(Binary {
            op: Sub,
            left:  Box::new(Int(42.into())),
            right: Box::new(Int(2.into())),
          })
        }
      ));
    }
  }

  mod enums {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn value() {
      assert_eq!(parse_single("port::http"), Ok(
        EnumValue {
          scope: Scope { absolute: false, path: vec![] },
          name: "port",
          value: "http",
        }
      ));
    }

    #[test]
    fn with_type() {
      assert_eq!(parse_single("some_type::port::http"), Ok(
        EnumValue {
          scope: Scope { absolute: false, path: vec!["some_type"] },
          name: "port",
          value: "http",
        }
      ));
      assert_eq!(parse_single("parent_type::child_type::port::http"), Ok(
        EnumValue {
          scope: Scope { absolute: false, path: vec!["parent_type", "child_type"] },
          name: "port",
          value: "http",
        }
      ));
    }

    #[test]
    fn with_abs_path() {
      assert_eq!(parse_single("::port::http"), Ok(
        EnumValue {
          scope: Scope { absolute: true, path: vec![] },
          name: "port",
          value: "http",
        }
      ));
      assert_eq!(parse_single("::parent_type::child_type::port::http"), Ok(
        EnumValue {
          scope: Scope { absolute: true, path: vec!["parent_type", "child_type"] },
          name: "port",
          value: "http",
        }
      ));
    }
  }

  #[test]
  fn complex() {
    assert_eq!(parse_single("port::http.to_i + 8000 == 8080"), Ok(
      Binary {
        op: Eq,
        left: Box::new(Binary {
          op: Add,
          left: Box::new(Access {
            expr: Box::new(EnumValue {
              scope: Scope { absolute: false, path: vec![] },
              name: "port",
              value: "http",
            }),
            attr: "to_i"
          }),
          right: Box::new(Int(8000.into()))
        }),
        right: Box::new(Int(8080.into()))
      }
    ));
  }

  #[test]
  fn list() {
    assert_eq!(parse_single("[1, 2, 0x1234]"), Ok(
      List(vec![Int(1.into()), Int(2.into()), Int(0x1234.into())])
    ));
  }

  mod literals {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn boolean() {
      assert_eq!(parse_single("true" ), Ok(Bool(true)));
      assert_eq!(parse_single("false"), Ok(Bool(false)));
    }

    #[test]
    fn special() {
      assert_eq!(parse_single("_io"),     Ok(SpecialName(crate::parser::expressions::SpecialName::Stream)));
      assert_eq!(parse_single("_root"),   Ok(SpecialName(crate::parser::expressions::SpecialName::Root)));
      assert_eq!(parse_single("_parent"), Ok(SpecialName(crate::parser::expressions::SpecialName::Parent)));
      assert_eq!(parse_single("_index"),  Ok(SpecialName(crate::parser::expressions::SpecialName::Index)));
      assert_eq!(parse_single("_"),       Ok(SpecialName(crate::parser::expressions::SpecialName::Value)));
      assert_eq!(parse_single("_on"),     Ok(SpecialName(crate::parser::expressions::SpecialName::SwitchOn)));
      assert_eq!(parse_single("_sizeof"), Ok(SpecialName(crate::parser::expressions::SpecialName::SizeOf)));
      assert_eq!(parse_single("_is_le"),  Ok(SpecialName(crate::parser::expressions::SpecialName::IsLe)));
    }

    #[test]
    fn identifiers() {
      assert_eq!(parse_single("truex"), Ok(Attr("truex")));
      assert_eq!(parse_single("true1"), Ok(Attr("true1")));

      assert_eq!(parse_single("falsex"), Ok(Attr("falsex")));
      assert_eq!(parse_single("false1"), Ok(Attr("false1")));

      assert_eq!(parse_single("notx"), Ok(Attr("notx")));
      assert_eq!(parse_single("not1"), Ok(Attr("not1")));

      assert_eq!(parse_single("andx"), Ok(Attr("andx")));
      assert_eq!(parse_single("and1"), Ok(Attr("and1")));

      assert_eq!(parse_single("orx"), Ok(Attr("orx")));
      assert_eq!(parse_single("or1"), Ok(Attr("or1")));

      assert_eq!(parse_single("_iox"), Ok(Attr("_iox")));
      assert_eq!(parse_single("_io1"), Ok(Attr("_io1")));

      assert_eq!(parse_single("_rootx"), Ok(Attr("_rootx")));
      assert_eq!(parse_single("_root1"), Ok(Attr("_root1")));

      assert_eq!(parse_single("_parentx"), Ok(Attr("_parentx")));
      assert_eq!(parse_single("_parent1"), Ok(Attr("_parent1")));

      assert_eq!(parse_single("_indexx"), Ok(Attr("_indexx")));
      assert_eq!(parse_single("_index1"), Ok(Attr("_index1")));

      assert_eq!(parse_single("_x"), Ok(Attr("_x")));
      assert_eq!(parse_single("_1"), Ok(Attr("_1")));

      assert_eq!(parse_single("_onx"), Ok(Attr("_onx")));
      assert_eq!(parse_single("_on1"), Ok(Attr("_on1")));

      assert_eq!(parse_single("_sizeofx"), Ok(Attr("_sizeofx")));
      assert_eq!(parse_single("_sizeof1"), Ok(Attr("_sizeof1")));

      assert_eq!(parse_single("_is_lex"), Ok(Attr("_is_lex")));
      assert_eq!(parse_single("_is_le1"), Ok(Attr("_is_le1")));
    }
  }

  mod cast {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn int_as_type() {
      assert_eq!(parse_single("123.as<u4>"), Ok(
        Cast {
          expr: Box::new(Int(123.into())),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "u4",
            },
            array: false,
          },
        }
      ));
    }
    #[test]
    fn expr_as_type() {
      assert_eq!(parse_single("(123).as<u4>"), Ok(
        Cast {
          expr: Box::new(Int(123.into())),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "u4",
            },
            array: false,
          },
        }
      ));
    }
    #[test]
    fn str_as_type() {
      assert_eq!(parse_single("\"str\".as<x>"), Ok(
        Cast {
          expr: Box::new(Str("str".into())),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "x",
            },
            array: false,
          },
        }
      ));
    }
    #[test]
    fn var_as_type() {
      assert_eq!(parse_single("foo.as<x>"), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "x",
            },
            array: false,
          },
        }
      ));
    }
    #[test]
    fn as_type_with_spaces() {
      assert_eq!(parse_single("foo.as < x  >  "), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "x",
            },
            array: false,
          },
        }
      ));
    }

    #[test]
    fn as_enum() {
      assert_eq!(parse_single("foo.as<bar::baz>"), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {//TODO: should be enum
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["bar"] },
              name: "baz",
            },
            array: false,
          },
        }
      ));
      assert_eq!(parse_single("foo.as<::bar::baz>"), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {//TODO: should be enum
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["bar"] },
              name: "baz",
            },
            array: false,
          },
        }
      ));
    }

    #[test]
    fn as_array() {
      assert_eq!(parse_single("foo.as<bar[]>"), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "bar",
            },
            array: true,
          },
        }
      ));
      assert_eq!(parse_single("foo.as<::bar::baz[]>"), Ok(
        Cast {
          expr: Box::new(Attr("foo")),
          to_type: TypeRef {
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["bar"] },
              name: "baz",
            },
            array: true,
          },
        }
      ));
    }

    #[test]
    fn attribute() {
      assert_eq!(parse_single("foo.as"), Ok(
        Access {
          expr: Box::new(Attr("foo")),
          attr: "as",
        }
      ));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("foo.as<x"), Ok(
        Binary {
          op: Lt,
          left: Box::new(Access {
            expr: Box::new(Attr("foo")),
            attr: "as"
          }),
          right: Box::new(Attr("x")),
        }
      ));
    }
  }

  mod sizeof_ {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("sizeof<foo>"), Ok(
        SizeOf {
          type_: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "foo",
            },
            array: false,
          },
          bit: false,
        }
      ));
    }

    #[test]
    fn of_enum() {
      assert_eq!(parse_single("sizeof<foo::bar>"), Ok(
        SizeOf {
          type_: TypeRef {//TODO: should be enum
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["foo"] },
              name: "bar",
            },
            array: false,
          },
          bit: false,
        }
      ));
      assert_eq!(parse_single("sizeof<::foo::bar>"), Ok(
        SizeOf {
          type_: TypeRef {//TODO: should be enum
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["foo"] },
              name: "bar",
            },
            array: false,
          },
          bit: false,
        }
      ));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("sizeof<foo"), Ok(
        Binary {
          op: Lt,
          left: Box::new(Attr("sizeof")),
          right: Box::new(Attr("foo")),
        }
      ));
    }
  }

  mod bitsizeof_ {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("bitsizeof<foo>"), Ok(
        SizeOf {
          type_: TypeRef {
            name: TypeName {
              scope: Scope { absolute: false, path: vec![] },
              name: "foo",
            },
            array: false,
          },
          bit: true,
        }
      ));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("bitsizeof<foo"), Ok(
        Binary {
          op: Lt,
          left: Box::new(Attr("bitsizeof")),
          right: Box::new(Attr("foo")),
        }
      ));
    }
  }

  mod attrs {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn access() {
      assert_eq!(parse_single("123.to_s"  ), Ok(Access { expr: Box::new(Int(123.into())), attr: "to_s" }));
      assert_eq!(parse_single("123. to_s" ), Ok(Access { expr: Box::new(Int(123.into())), attr: "to_s" }));
      assert_eq!(parse_single("123.\nto_s"), Ok(Access { expr: Box::new(Int(123.into())), attr: "to_s" }));
      assert_eq!(parse_single("foo.bar"   ), Ok(Access { expr: Box::new(Attr("foo")), attr: "bar" }));
    }

    #[test]
    fn int_not_float() {
      assert_eq!(parse_single("123.e"  ), Ok(Access { expr: Box::new(Int(123.into())), attr: "e" }));
      assert_eq!(parse_single("123. e" ), Ok(Access { expr: Box::new(Int(123.into())), attr: "e" }));
      assert_eq!(parse_single("123.\ne"), Ok(Access { expr: Box::new(Int(123.into())), attr: "e" }));

      assert_eq!(parse_single("123.E"  ), Ok(Access { expr: Box::new(Int(123.into())), attr: "E" }));
      assert_eq!(parse_single("123. E" ), Ok(Access { expr: Box::new(Int(123.into())), attr: "E" }));
      assert_eq!(parse_single("123.\nE"), Ok(Access { expr: Box::new(Int(123.into())), attr: "E" }));

      assert_eq!(parse_single("123._"  ), Ok(Access { expr: Box::new(Int(123.into())), attr: "_" }));
      assert_eq!(parse_single("123. _" ), Ok(Access { expr: Box::new(Int(123.into())), attr: "_" }));
      assert_eq!(parse_single("123.\n_"), Ok(Access { expr: Box::new(Int(123.into())), attr: "_" }));
    }

    #[test]
    fn float_and_access() {
      assert_eq!(parse_single("123.4.to_s"  ), Ok(Access { expr: Box::new(Float((1234, 1).into())), attr: "to_s" }));
      assert_eq!(parse_single("123.4. to_s" ), Ok(Access { expr: Box::new(Float((1234, 1).into())), attr: "to_s" }));
      assert_eq!(parse_single("123.4.\nto_s"), Ok(Access { expr: Box::new(Float((1234, 1).into())), attr: "to_s" }));
    }
  }

  /// Tests for parsing of attributes' type reference definitions
  mod type_ref {
    use super::*;

    /// Wrapper, for use with https://github.com/fasterthanlime/pegviz
    fn parse(input: &str) -> Result<AttrType, peg::error::ParseError<peg::str::LineCol>> {
      println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
      let result = super::super::parse_type_ref(input);
      println!("[PEG_TRACE_STOP]");
      result
    }

    /// Bit-sized integers
    mod bit_sized {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;

      #[test]//FIXME: should fail after https://github.com/kaitai-io/kaitai_struct/issues/939
      fn b0() {
        assert_eq!(parse("b0"), Ok(AttrType::Bits {
          size: 0,
          order: None,
        }));
      }

      #[test]//FIXME: should fail after https://github.com/kaitai-io/kaitai_struct/issues/939
      fn b1be() {
        assert_eq!(parse("b1be"), Ok(AttrType::Bits {
          size: 1,
          order: Some(BitOrder::Be),
        }));
      }

      #[test]//FIXME: should fail after https://github.com/kaitai-io/kaitai_struct/issues/939
      fn b1le() {
        assert_eq!(parse("b1le"), Ok(AttrType::Bits {
          size: 1,
          order: Some(BitOrder::Le),
        }));
      }

      #[test]//FIXME: should fail after https://github.com/kaitai-io/kaitai_struct/issues/939
      fn leading_zeros() {
        assert_eq!(parse("b0001"), Ok(AttrType::Bits {
          size: 1,
          order: None,
        }));
      }

      #[test]
      fn correct() {
        assert_eq!(parse("b12345"), Ok(AttrType::Bits {
          size: 12345,
          order: None,
        }));
      }

      #[test]
      fn explicit_endian() {
        assert_eq!(parse("b12345le"), Ok(AttrType::Bits {
          size: 12345,
          order: Some(BitOrder::Le),
        }));

        assert_eq!(parse("b12345be"), Ok(AttrType::Bits {
          size: 12345,
          order: Some(BitOrder::Be),
        }));
      }
    }

    /// Types, represented only by their local name
    mod local {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;

      #[test]
      fn simple() {
        assert_eq!(parse("some_type"), Ok(AttrType::User {
          name: TypeName {
            scope: Scope { absolute: false, path: vec![] },
            name: "some_type",
          },
          args: vec![],
        }));
      }
      #[test]
      fn with_spaces() {
        assert_eq!(parse("  some_type  "), Ok(AttrType::User {
          name: TypeName {
            scope: Scope { absolute: false, path: vec![] },
            name: "some_type",
          },
          args: vec![],
        }));
      }
      #[test]
      fn with_args() {
        assert_eq!(parse("some_type(1+2,data)"), Ok(AttrType::User {
          name: TypeName {
            scope: Scope { absolute: false, path: vec![] },
            name: "some_type",
          },
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1.into())),
              right: Box::new(Int(2.into())),
            },
            Attr("data"),
          ],
        }));
      }
      #[test]
      fn with_args_and_spaces() {
        assert_eq!(parse(" some_type ( 1 + 2 , data ) "), Ok(AttrType::User {
          name: TypeName {
            scope: Scope { absolute: false, path: vec![] },
            name: "some_type",
          },
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1.into())),
              right: Box::new(Int(2.into())),
            },
            Attr("data"),
          ],
        }));
      }
    }

    /// Types, represented by the path -- absolute or relative
    mod path {
      use super::*;

      mod absolute {
        // Colorful diffs in assertions - resolve ambiguous
        use pretty_assertions::assert_eq;
        use super::*;

        #[test]
        fn simple() {
          assert_eq!(parse("::some::type"), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["some"] },
              name: "type",
            },
            args: vec![],
          }));
        }

        #[test]
        fn with_spaces() {
          assert_eq!(parse("  ::  some  ::  type  "), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["some"] },
              name: "type",
            },
            args: vec![],
          }));
        }

        #[test]
        fn with_args() {
          assert_eq!(parse("::some::type(1+2,data)"), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["some"] },
              name: "type",
            },
            args: vec![
              Binary {
                op:    Add,
                left:  Box::new(Int(1.into())),
                right: Box::new(Int(2.into())),
              },
              Attr("data"),
            ],
          }));
        }

        #[test]
        fn with_args_and_spaces() {
          assert_eq!(parse(" :: some :: type ( 1 + 2 , data ) "), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: true, path: vec!["some"] },
              name: "type",
            },
            args: vec![
              Binary {
                op:    Add,
                left:  Box::new(Int(1.into())),
                right: Box::new(Int(2.into())),
              },
              Attr("data"),
            ],
          }));
        }
      }

      mod relative {
        // Colorful diffs in assertions - resolve ambiguous
        use pretty_assertions::assert_eq;
        use super::*;

        #[test]
        fn simple() {
          assert_eq!(parse("some::type"), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["some"] },
              name: "type",
            },
            args: vec![],
          }));
        }

        #[test]
        fn with_spaces() {
          assert_eq!(parse("  some  ::  type  "), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["some"] },
              name: "type",
            },
            args: vec![],
          }));
        }

        #[test]
        fn with_args() {
          assert_eq!(parse("some::type(1+2,data)"), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["some"] },
              name: "type",
            },
            args: vec![
              Binary {
                op:    Add,
                left:  Box::new(Int(1.into())),
                right: Box::new(Int(2.into())),
              },
              Attr("data"),
            ],
          }));
        }

        #[test]
        fn with_args_and_spaces() {
          assert_eq!(parse(" some :: type ( 1 + 2 , data ) "), Ok(AttrType::User {
            name: TypeName {
              scope: Scope { absolute: false, path: vec!["some"] },
              name: "type",
            },
            args: vec![
              Binary {
                op:    Add,
                left:  Box::new(Int(1.into())),
                right: Box::new(Int(2.into())),
              },
              Attr("data"),
            ],
          }));
        }
      }
    }
  }
}
