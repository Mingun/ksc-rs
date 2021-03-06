//! Parser and AST for Kaitai Struct expression language.

//TODO: Describe the language

use std::convert::TryFrom;
use std::char;
use std::iter::FromIterator;

use ordered_float::OrderedFloat;
use serde_yaml::Number;

use crate::error::ModelError;
use crate::parser::Scalar;

/// Owning counterpart of AST [`Node`].
///
/// [`Node`]: ./enum.Node.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwningNode {
  /// String constant
  Str(String),
  /// Integral constant
  Int(u64),
  /// Floating-point constant
  Float(OrderedFloat<f64>),
  /// Boolean constant
  Bool(bool),

  /// Name of attribute or variable
  Name(String),
  /// Reference to type
  Type(OwningTypeRef),
  /// Reference to enum value
  EnumValue {
    /// Reference to enum value.
    ///
    /// Contains names of all types in path to current value.
    /// Last element is local name of enum value, and element before last is
    /// enum local name.
    path: Vec<String>,
    /// Path is absolute (starts from top-level type)
    absolute: bool,
  },

  /// Array constructor
  List(Vec<OwningNode>),

  /// Calculation of size of type
  SizeOf {
    /// Reference to type for which size must be calculated
    type_: OwningTypeRef,
    /// if `true`, calculate size in bits, otherwise in bytes
    bit: bool,
  },

  /// Calling function or method: `${expr}(${args})`.
  Call {
    /// Expression which is called
    callee: Box<OwningNode>,
    /// Arguments of method call
    args: Vec<OwningNode>,
  },
  /// Conversion to type: `${expr}.as<${to_type}>`.
  Cast {
    /// Expression for conversion
    expr: Box<OwningNode>,
    /// Reference to type for conversion
    to_type: OwningTypeRef,
  },
  /// Access to expression by some index
  Index {
    /// Expression for indexing
    expr: Box<OwningNode>,
    /// Index expression
    index: Box<OwningNode>,
  },
  /// Access to some attribute of expression
  Access {
    /// Expression which attribute must be evaluated
    expr: Box<OwningNode>,
    /// Retrieved attribute
    attr: String,
  },

  /// The unary prefix operator, such as unary `-` or logical `not`.
  Unary {
    /// Operation to apply
    op: UnaryOp,
    /// Expression for applying operator
    expr: Box<OwningNode>
  },
  /// The binary infix operator, such as `+` or `==`.
  Binary {
    /// Operation between left and right parts of expression
    op: BinaryOp,
    /// Left part of operator
    left: Box<OwningNode>,
    /// Right part of operator
    right: Box<OwningNode>,
  },
  /// Conditional expression, written as ternary operator
  Branch {
    /// Expression to check. Should evaluate to boolean value
    condition: Box<OwningNode>,
    /// Expression that should be calculated in case of `true` `condition`.
    if_true:   Box<OwningNode>,
    /// Expression that should be calculated in case of `false` `condition`.
    if_false:  Box<OwningNode>,
  },
}
impl<'input> From<Node<'input>> for OwningNode {
  fn from(reference: Node<'input>) -> Self {
    use Node::*;

    match reference {
      Str(val)  => Self::Str(val),
      Int(val)  => Self::Int(val),
      Float(val)=> Self::Float(val),
      Bool(val) => Self::Bool(val),

      Name(val) => Self::Name(val.into()),
      Type(val) => Self::Type(val.into()),
      EnumValue { path, absolute } => Self::EnumValue {
        path: path.into_iter().map(Into::into).collect(),
        absolute
      },

      List(val) => Self::List(val.into_iter().map(Into::into).collect()),

      SizeOf { type_, bit } => Self::SizeOf { type_: type_.into(), bit },

      Call { callee, args } => Self::Call {
        callee: Box::new((*callee).into()),
        args: args.into_iter().map(Into::into).collect(),
      },
      Cast { expr, to_type } => Self::Cast {
        expr: Box::new((*expr).into()),
        to_type: to_type.into(),
      },
      Index { expr, index } => Self::Index {
        expr:  Box::new((*expr).into()),
        index: Box::new((*index).into()),
      },
      Access { expr, attr } => Self::Access {
        expr: Box::new((*expr).into()),
        attr: attr.into(),
      },

      Unary { op, expr } => Self::Unary {
        op,
        expr: Box::new((*expr).into()),
      },
      Binary { op, left, right } => Self::Binary {
        op,
        left:  Box::new((*left).into()),
        right: Box::new((*right).into()),
      },
      Branch { condition, if_true, if_false } => Self::Branch {
        condition: Box::new((*condition).into()),
        if_true:   Box::new((*if_true).into()),
        if_false:  Box::new((*if_false).into()),
      },
    }
  }
}
impl From<Number> for OwningNode {
  #[inline]
  fn from(number: Number) -> Self {
    Node::from(number).into()
  }
}
impl TryFrom<Scalar> for OwningNode {
  type Error = ModelError;

  fn try_from(scalar: Scalar) -> Result<Self, Self::Error> {
    use ModelError::*;
    use Scalar::*;

    match scalar {
      Null        => Err(Validation(
        "Expected expression, but null found (note that `null` literal in YAML is \
         equivalent of absence of any value, use 'null' if you want to refer to name `null`)".into())),
      Bool(val)   => Ok(Self::Bool(val)),
      Number(n)   => Ok(n.into()),
      String(val) => Ok(parser::parse_single(&val)?.into()),
    }
  }
}

/// Owning counterpart of AST [`TypeRef`].
///
/// [`Node`]: ./struct.TypeRef.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OwningTypeRef {
  /// Names of all types in path to current type.
  /// Last element is local name of current type.
  pub path: Vec<String>,
  /// Path is absolute (starts from top-level type)
  pub absolute: bool,
  /// Path is array type
  pub array: bool,
}
impl<'input> From<TypeRef<'input>> for OwningTypeRef {
  fn from(reference: TypeRef<'input>) -> Self {
    Self {
      path:     reference.path.into_iter().map(ToOwned::to_owned).collect(),
      absolute: reference.absolute,
      array:    reference.array,
    }
  }
}

/// AST Node, that represent some syntax construct
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node<'input> {
  /// String constant
  Str(String),
  /// Integral constant
  Int(u64),
  /// Floating-point constant
  Float(OrderedFloat<f64>),
  /// Boolean constant
  Bool(bool),

  /// Name of attribute or variable
  Name(&'input str),
  /// Reference to type
  Type(TypeRef<'input>),
  /// Reference to enum value
  EnumValue {
    /// Reference to enum value.
    ///
    /// Contains names of all types in path to current value.
    /// Last element is local name of enum value, and element before last is
    /// enum local name.
    path: Vec<&'input str>,
    /// Path is absolute (starts from top-level type)
    absolute: bool,
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
      return Node::Int(n);
    }
    if let Some(n) = number.as_i64() {
      // Can return only negative integers, because positive is handled above
      return Node::Unary {
        op: UnaryOp::Neg,
        expr: Box::new(Node::Int((-n) as u64)),
      };
    }
    if let Some(n) = number.as_f64() {
      return Node::Float(n.into());
    }
    unreachable!("internal error: YAML number is not u64/i64/f64")
  }
}

/// Represents reference to type definition.
///
/// Reference to type consist of:
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
/// `'input` lifetime is bound to lifetime of parsed string. Each element in path
/// just a slice inside original string.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeRef<'input> {
  /// Names of all types in path to current type.
  /// Last element is local name of current type.
  pub path: Vec<&'input str>,
  /// Path is absolute (starts from top-level type)
  pub absolute: bool,
  /// Path is array type
  pub array: bool,
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

/// Reference to user-defined type name with optional parameters.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct UserTypeRef<'input> {
  /// Absolute path to type definition
  pub path: Vec<&'input str>,
  /// Optional arguments for type
  pub args: Vec<Node<'input>>,
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
fn to_u64(number: &str, radix: u32) -> Result<u64, &'static str> {
  u64::from_str_radix(&number.replace('_', ""), radix)
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
  pub grammar parser() for str {
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
    pub rule parse_type_ref() -> UserTypeRef<'input>
        //TODO: Original KSC do not allow spaces between "::" in type reference,
        // before and after "(" and after ")"
        // https://github.com/kaitai-io/kaitai_struct/issues/792
      = path:(name() ** "::") args:("(" args:args() _ ")" { args })? EOS() {
        UserTypeRef { path, args: args.unwrap_or_default() }
      };

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

    rule integer() -> u64
      = n:$(['1'..='9'] ['0'..='9' | '_']*) {? to_u64(n, 10) }
      / "0" ['b' | 'B'] n:$(bin()+) {? to_u64(n,  2) }
      / "0" ['o' | 'O'] n:$(oct()+) {? to_u64(n,  8) }
      / "0" ['x' | 'X'] n:$(hex()+) {? to_u64(n, 16) }
      / "0" { 0 }
      ;
    rule oct() = ['0'..='7' | '_'];
    rule bin() = ['0'..='1' | '_'];
    rule hex() = ['0'..='9' | 'a'..='f' | 'A'..='F' | '_'];

    rule digit() = ['0'..='9'];

    rule float() -> f64 = n:$(//TODO: allow '_' in floats
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

    /// Ex.: `xyz`, `::abc::def`, `array[]`
    rule type_name() -> TypeRef<'input>
      = absolute:"::"? _ path:path() array:(_ "[" _ "]")? {
        TypeRef { path, absolute: absolute.is_some(), array: array.is_some() }
      };
    /// Ex.: `enum::value`, `::root::type::enum::value`
    rule enum_name() -> Node<'input>
      = absolute:"::"? _ n1:name() _ "::" _ n2:name() tail:(_ "::" _ n:name() {n})* {
        let mut path = vec![n1, n2];
        path.extend(tail);

        Node::EnumValue { path, absolute: absolute.is_some() }
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
      = "(" _ e:expr() _ ")"                    { e }
      / "[" _ l:list()? _ "]"                   { Node::List(l.unwrap_or_default()) }
      / "sizeof" _ "<" _ t:type_name() _ ">"    { Node::SizeOf { type_: t, bit: false } }
      / "bitsizeof" _ "<" _ t:type_name() _ ">" { Node::SizeOf { type_: t, bit: true  } }
      / v:(s:string() _ {s})+                   { Node::Str(String::from_iter(v.into_iter())) }
      / "true"  !name_part()                    { Node::Bool(true) }
      / "false" !name_part()                    { Node::Bool(false) }
      / e:enum_name()                           { e }
      / n:name()                                { Node::Name(n) }
      / f:float()                               { Node::Float(f.into()) }
      / i:integer()                             { Node::Int(i) }
      ;

    rule postfix() -> Postfix<'input>
      = "(" _ a:args() _ ")"                   { Postfix::Args(a)   }// call
      / "[" _ e:expr() _ "]"                   { Postfix::Index(e)  }// indexing
      / "." _ "as" _ "<" _ t:type_name() _ ">" { Postfix::CastTo(t) }// type cast
      / "." _ n:name()                         { Postfix::Field(n)  }// attribute access
      ;

    /// List of names, delimited by `::`
    rule path() -> Vec<&'input str> = path:name() ** (_ "::" _) { path };
    /// List of expressions, delimited by comma, allowing dangling comma
    rule list() -> Vec<Node<'input>> = list:args() _ ","? { list };
    /// List of expressions, delimited by comma
    rule args() -> Vec<Node<'input>> = args:expr() ** (_ "," _) { args };
  }
}

#[cfg(test)]
mod parse {
  use super::{Node, TypeRef, UserTypeRef};
  use super::Node::*;
  use super::UnaryOp::*;
  use super::BinaryOp::*;

  /// Wrapper, for use with https://github.com/fasterthanlime/pegviz
  fn parse_single(input: &str) -> Result<Node, peg::error::ParseError<peg::str::LineCol>> {
    println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
    let result = super::parser::parse_single(input);
    println!("[PEG_TRACE_STOP]");
    result
  }

  mod comments {
    use super::*;

    #[test]
    fn empty() {
      assert_eq!(parse_single("#\n123"), Ok(Int(123)));
    }
    #[test]
    fn following() {
      assert_eq!(parse_single("123# comment"), Ok(Int(123)));
      assert_eq!(parse_single("123\n# comment"), Ok(Int(123)));
    }
    #[test]
    fn leading() {
      assert_eq!(parse_single("# comment\n123"), Ok(Int(123)));
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
      "#), Ok(Binary { op: Add, left: Int(1).into(), right: Int(2).into() }));
    }
  }

  mod dec {
    use super::*;

    #[test]
    fn positive() {
      assert_eq!(parse_single("123"), Ok(Int(123)));
    }

    #[test]
    fn negative() {
      assert_eq!(parse_single("-456"), Ok(Unary { op: Neg, expr: Box::new(Int(456)) }));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("100_500"), Ok(Int(100_500)));
      assert_eq!(parse_single("100500_"), Ok(Int(100_500)));
    }
  }

  mod hex {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0x1234"), Ok(Int(0x1234)));
      assert_eq!(parse_single("0X1234"), Ok(Int(0x1234)));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0x_1234"), Ok(Int(0x1234)));
      assert_eq!(parse_single("0x12_34"), Ok(Int(0x1234)));
      assert_eq!(parse_single("0x1234_"), Ok(Int(0x1234)));

      assert_eq!(parse_single("0X_1234"), Ok(Int(0x1234)));
      assert_eq!(parse_single("0X12_34"), Ok(Int(0x1234)));
      assert_eq!(parse_single("0X1234_"), Ok(Int(0x1234)));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0x_").is_err());
      assert!(parse_single("0X_").is_err());
    }
  }

  mod oct {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0o644"), Ok(Int(0o644)));
      assert_eq!(parse_single("0O644"), Ok(Int(0o644)));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0o_0644"), Ok(Int(0o644)));
      assert_eq!(parse_single("0o06_44"), Ok(Int(0o644)));
      assert_eq!(parse_single("0o0644_"), Ok(Int(0o644)));

      assert_eq!(parse_single("0O_0644"), Ok(Int(0o644)));
      assert_eq!(parse_single("0O06_44"), Ok(Int(0o644)));
      assert_eq!(parse_single("0O0644_"), Ok(Int(0o644)));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0o_").is_err());
      assert!(parse_single("0O_").is_err());
    }
  }

  mod bin {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("0b10101010"), Ok(Int(0b10101010)));
      assert_eq!(parse_single("0B10101010"), Ok(Int(0b10101010)));
    }

    #[test]
    fn with_underscores() {
      assert_eq!(parse_single("0b_1010_1010"), Ok(Int(0b10101010)));
      assert_eq!(parse_single("0b1010_1_010"), Ok(Int(0b10101010)));
      assert_eq!(parse_single("0b1010_1010_"), Ok(Int(0b10101010)));

      assert_eq!(parse_single("0B_1010_1010"), Ok(Int(0b10101010)));
      assert_eq!(parse_single("0B1010_1_010"), Ok(Int(0b10101010)));
      assert_eq!(parse_single("0B1010_1010_"), Ok(Int(0b10101010)));
    }

    #[test]
    fn with_only_underscores() {
      assert!(parse_single("0b_").is_err());
      assert!(parse_single("0B_").is_err());
    }
  }

  mod float {
    use super::*;

    #[test]
    fn simple() {
      assert_eq!(parse_single("1.2345"), Ok(Float(1.2345.into())));
    }

    #[test]
    fn with_signless_exponent() {
      assert_eq!(parse_single("123e4"), Ok(Float(123e+4.into())));
      assert_eq!(parse_single("123E4"), Ok(Float(123e+4.into())));
    }

    #[test]
    fn with_positive_exponent() {
      assert_eq!(parse_single("123e+4"), Ok(Float(123e+4.into())));
      assert_eq!(parse_single("123E+4"), Ok(Float(123e+4.into())));
    }

    #[test]
    fn with_negative_exponent() {
      assert_eq!(parse_single("123e-7"), Ok(Float(123e-7.into())));
      assert_eq!(parse_single("123E-7"), Ok(Float(123e-7.into())));
    }

    #[test]
    fn non_integral_part_with_signless_exponent() {
      assert_eq!(parse_single("1.2345e7"), Ok(Float(1.2345e+7.into())));
      assert_eq!(parse_single("1.2345E7"), Ok(Float(1.2345e+7.into())));
    }

    #[test]
    fn non_integral_part_with_positive_exponent() {
      assert_eq!(parse_single("123.45e+7"), Ok(Float(123.45e+7.into())));
      assert_eq!(parse_single("123.45E+7"), Ok(Float(123.45e+7.into())));
    }

    #[test]
    fn non_integral_part_with_negative_exponent() {
      assert_eq!(parse_single("123.45e-7"), Ok(Float(123.45e-7.into())));
      assert_eq!(parse_single("123.45E-7"), Ok(Float(123.45e-7.into())));
    }
  }

  mod string {
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
    use super::*;

    #[test]
    fn unary() {
      macro_rules! test {
        ($string:expr => $op:ident) => {
          assert_eq!(parse_single($string), Ok(
            Unary {
              op: $op,
              expr: Box::new(Unary { op: $op, expr: Box::new(Int(1)) })
            }
          ));
        };
      }
      assert_eq!(parse_single("++1"), Ok(Int(1)));
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
              left:  Box::new(Int(1)),
              right: Box::new(Int(2)),
            }),
            right: Box::new(Int(3))
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
          condition: Box::new(Name("x")),
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
            left: Box::new(Int(1)),
            right: Box::new(Int(2))
          }),
          right: Box::new(Binary {
            op: Mul,
            left: Box::new(Int(7)),
            right: Box::new(Int(8))
          }),
        }
      ));
    }

    #[test]
    fn comparison() {
      assert_eq!(parse_single("1 == 2"), Ok(
        Binary { op: Eq, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
      assert_eq!(parse_single("1 != 2"), Ok(
        Binary { op: Ne, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
      assert_eq!(parse_single("1 <= 2"), Ok(
        Binary { op: Le, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
      assert_eq!(parse_single("1 >= 2"), Ok(
        Binary { op: Ge, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
      assert_eq!(parse_single("1 < 2" ), Ok(
        Binary { op: Lt, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
      assert_eq!(parse_single("1 > 2" ), Ok(
        Binary { op: Gt, left: Box::new(Int(1)), right: Box::new(Int(2)) }
      ));
    }

    #[test]
    fn indexing() {
      assert_eq!(parse_single("a[42]"), Ok(
        Index { expr: Box::new(Name("a")), index: Box::new(Int(42)) }
      ));
      assert_eq!(parse_single("a[42 - 2]"), Ok(
        Index {
          expr: Box::new(Name("a")),
          index: Box::new(Binary {
            op: Sub,
            left:  Box::new(Int(42)),
            right: Box::new(Int(2)),
          })
        }
      ));
    }
  }

  mod enums {
    use super::*;

    #[test]
    fn value() {
      assert_eq!(parse_single("port::http"), Ok(
        EnumValue { path: vec!["port", "http"], absolute: false }
      ));
    }

    #[test]
    fn with_type() {
      assert_eq!(parse_single("some_type::port::http"), Ok(
        EnumValue { path: vec!["some_type", "port", "http"], absolute: false }
      ));
      assert_eq!(parse_single("parent_type::child_type::port::http"), Ok(
        EnumValue { path: vec!["parent_type", "child_type", "port", "http"], absolute: false }
      ));
    }

    #[test]
    fn with_abs_path() {
      assert_eq!(parse_single("::port::http"), Ok(
        EnumValue { path: vec!["port", "http"], absolute: true }
      ));
      assert_eq!(parse_single("::parent_type::child_type::port::http"), Ok(
        EnumValue { path: vec!["parent_type", "child_type", "port", "http"], absolute: true }
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
              path: vec!["port", "http"],
              absolute: false
            }),
            attr: "to_i"
          }),
          right: Box::new(Int(8000))
        }),
        right: Box::new(Int(8080))
      }
    ));
  }

  #[test]
  fn list() {
    assert_eq!(parse_single("[1, 2, 0x1234]"), Ok(
      List(vec![Int(1), Int(2), Int(0x1234)])
    ));
  }

  mod literals {
    use super::*;

    #[test]
    fn boolean() {
      assert_eq!(parse_single("true" ), Ok(Bool(true)));
      assert_eq!(parse_single("false"), Ok(Bool(false)));
    }

    #[test]
    fn identifiers() {
      assert_eq!(parse_single("truex"), Ok(Name("truex")));
      assert_eq!(parse_single("true1"), Ok(Name("true1")));

      assert_eq!(parse_single("falsex"), Ok(Name("falsex")));
      assert_eq!(parse_single("false1"), Ok(Name("false1")));

      assert_eq!(parse_single("notx"), Ok(Name("notx")));
      assert_eq!(parse_single("not1"), Ok(Name("not1")));

      assert_eq!(parse_single("andx"), Ok(Name("andx")));
      assert_eq!(parse_single("and1"), Ok(Name("and1")));

      assert_eq!(parse_single("orx"), Ok(Name("orx")));
      assert_eq!(parse_single("or1"), Ok(Name("or1")));
    }
  }

  mod casts {
    use super::*;

    #[test]
    fn int_as_type() {
      assert_eq!(parse_single("123.as<u4>"), Ok(
        Cast {
          expr: Box::new(Int(123)),
          to_type: TypeRef { path: vec!["u4"], absolute: false, array: false }
        }
      ));
    }
    #[test]
    fn expr_as_type() {
      assert_eq!(parse_single("(123).as<u4>"), Ok(
        Cast {
          expr: Box::new(Int(123)),
          to_type: TypeRef { path: vec!["u4"], absolute: false, array: false }
        }
      ));
    }
    #[test]
    fn str_as_type() {
      assert_eq!(parse_single("\"str\".as<x>"), Ok(
        Cast {
          expr: Box::new(Str("str".into())),
          to_type: TypeRef { path: vec!["x"], absolute: false, array: false }
        }
      ));
    }
    #[test]
    fn var_as_type() {
      assert_eq!(parse_single("foo.as<x>"), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["x"], absolute: false, array: false }
        }
      ));
    }
    #[test]
    fn as_type_with_spaces() {
      assert_eq!(parse_single("foo.as < x  >  "), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["x"], absolute: false, array: false }
        }
      ));
    }

    #[test]
    fn as_enum() {
      assert_eq!(parse_single("foo.as<bar::baz>"), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["bar", "baz"], absolute: false, array: false }
        }
      ));
      assert_eq!(parse_single("foo.as<::bar::baz>"), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["bar", "baz"], absolute: true, array: false }
        }
      ));
    }

    #[test]
    fn as_array() {
      assert_eq!(parse_single("foo.as<bar[]>"), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["bar"], absolute: false, array: true }
        }
      ));
      assert_eq!(parse_single("foo.as<::bar::baz[]>"), Ok(
        Cast {
          expr: Box::new(Name("foo")),
          to_type: TypeRef { path: vec!["bar", "baz"], absolute: true, array: true }
        }
      ));
    }

    #[test]
    fn attribute() {
      assert_eq!(parse_single("foo.as"), Ok(
        Access {
          expr: Box::new(Name("foo")),
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
            expr: Box::new(Name("foo")),
            attr: "as"
          }),
          right: Box::new(Name("x")),
        }
      ));
    }
  }

  mod sizeof_ {
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("sizeof<foo>"), Ok(
        SizeOf {
          type_: TypeRef {
            path: vec!["foo"],
            absolute: false,
            array: false
          },
          bit: false
        }
      ));
    }

    #[test]
    fn of_enum() {
      assert_eq!(parse_single("sizeof<foo::bar>"), Ok(
        SizeOf {
          type_: TypeRef { path: vec!["foo", "bar"], absolute: false, array: false },
          bit: false
        }
      ));
      assert_eq!(parse_single("sizeof<::foo::bar>"), Ok(
        SizeOf {
          type_: TypeRef { path: vec!["foo", "bar"], absolute: true, array: false },
          bit: false
        }
      ));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("sizeof<foo"), Ok(
        Binary {
          op: Lt,
          left: Box::new(Name("sizeof")),
          right: Box::new(Name("foo")),
        }
      ));
    }
  }

  mod bitsizeof_ {
    use super::*;

    #[test]
    fn of_type() {
      assert_eq!(parse_single("bitsizeof<foo>"), Ok(
        SizeOf {
          type_: TypeRef {
            path: vec!["foo"],
            absolute: false,
            array: false
          },
          bit: true
        }
      ));
    }

    #[test]
    fn less() {
      assert_eq!(parse_single("bitsizeof<foo"), Ok(
        Binary {
          op: Lt,
          left: Box::new(Name("bitsizeof")),
          right: Box::new(Name("foo")),
        }
      ));
    }
  }

  mod attrs {
    use super::*;

    #[test]
    fn access() {
      assert_eq!(parse_single("123.to_s"  ), Ok(Access { expr: Box::new(Int(123)), attr: "to_s" }));
      assert_eq!(parse_single("123. to_s" ), Ok(Access { expr: Box::new(Int(123)), attr: "to_s" }));
      assert_eq!(parse_single("123.\nto_s"), Ok(Access { expr: Box::new(Int(123)), attr: "to_s" }));
      assert_eq!(parse_single("foo.bar"   ), Ok(Access { expr: Box::new(Name("foo")), attr: "bar" }));
    }

    #[test]
    fn int_not_float() {
      assert_eq!(parse_single("123.e"  ), Ok(Access { expr: Box::new(Int(123)), attr: "e" }));
      assert_eq!(parse_single("123. e" ), Ok(Access { expr: Box::new(Int(123)), attr: "e" }));
      assert_eq!(parse_single("123.\ne"), Ok(Access { expr: Box::new(Int(123)), attr: "e" }));

      assert_eq!(parse_single("123.E"  ), Ok(Access { expr: Box::new(Int(123)), attr: "E" }));
      assert_eq!(parse_single("123. E" ), Ok(Access { expr: Box::new(Int(123)), attr: "E" }));
      assert_eq!(parse_single("123.\nE"), Ok(Access { expr: Box::new(Int(123)), attr: "E" }));

      assert_eq!(parse_single("123._"  ), Ok(Access { expr: Box::new(Int(123)), attr: "_" }));
      assert_eq!(parse_single("123. _" ), Ok(Access { expr: Box::new(Int(123)), attr: "_" }));
      assert_eq!(parse_single("123.\n_"), Ok(Access { expr: Box::new(Int(123)), attr: "_" }));
    }

    #[test]
    fn float_and_access() {
      assert_eq!(parse_single("123.4.to_s"  ), Ok(Access { expr: Box::new(Float(123.4.into())), attr: "to_s" }));
      assert_eq!(parse_single("123.4. to_s" ), Ok(Access { expr: Box::new(Float(123.4.into())), attr: "to_s" }));
      assert_eq!(parse_single("123.4.\nto_s"), Ok(Access { expr: Box::new(Float(123.4.into())), attr: "to_s" }));
    }
  }

  #[cfg(test)]
  mod type_ref {
    use super::*;

    /// Wrapper, for use with https://github.com/fasterthanlime/pegviz
    fn parse(input: &str) -> Result<UserTypeRef, peg::error::ParseError<peg::str::LineCol>> {
      println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
      let result = super::super::parser::parse_type_ref(input);
      println!("[PEG_TRACE_STOP]");
      result
    }

    mod local {
      use super::*;

      #[test]
      fn simple() {
        assert_eq!(parse("some_type"), Ok(UserTypeRef {
          path: vec!["some_type"],
          args: vec![],
        }));
      }
      #[test]
      #[should_panic]//TODO: https://github.com/kaitai-io/kaitai_struct/issues/792
      fn with_spaces() {
        assert_eq!(parse("  some_type  "), Ok(UserTypeRef {
          path: vec!["some_type"],
          args: vec![],
        }));
      }
      #[test]
      fn with_args() {
        assert_eq!(parse("some_type(1+2,data)"), Ok(UserTypeRef {
          path: vec!["some_type"],
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1)),
              right: Box::new(Int(2)),
            },
            Name("data"),
          ],
        }));
      }
      #[test]
      #[should_panic]//TODO: https://github.com/kaitai-io/kaitai_struct/issues/792
      fn with_args_and_spaces() {
        assert_eq!(parse(" some_type ( 1 + 2 , data ) "), Ok(UserTypeRef {
          path: vec!["some_type"],
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1)),
              right: Box::new(Int(2)),
            },
            Name("data"),
          ],
        }));
      }
    }

    mod path {
      use super::*;

      #[test]
      fn simple() {
        assert_eq!(parse("some::type"), Ok(UserTypeRef {
          path: vec!["some", "type"],
          args: vec![],
        }));
      }

      #[test]
      #[should_panic]//TODO: https://github.com/kaitai-io/kaitai_struct/issues/792
      fn with_spaces() {
        assert_eq!(parse("  some  ::  type  "), Ok(UserTypeRef {
          path: vec!["some", "type"],
          args: vec![],
        }));
      }

      #[test]
      fn with_args() {
        assert_eq!(parse("some::type(1+2,data)"), Ok(UserTypeRef {
          path: vec!["some", "type"],
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1)),
              right: Box::new(Int(2)),
            },
            Name("data"),
          ],
        }));
      }

      #[test]
      #[should_panic]//TODO: https://github.com/kaitai-io/kaitai_struct/issues/792
      fn with_args_and_spaces() {
        assert_eq!(parse(" some :: type ( 1 + 2 , data ) "), Ok(UserTypeRef {
          path: vec!["some", "type"],
          args: vec![
            Binary {
              op:    Add,
              left:  Box::new(Int(1)),
              right: Box::new(Int(2)),
            },
            Name("data"),
          ],
        }));
      }
    }
  }
}

#[cfg(test)]
mod convert {
  use super::*;

  #[test]
  fn from_null() {
    assert!(OwningNode::try_from(Scalar::Null).is_err());
  }

  #[test]
  fn from_true() {
    assert_eq!(OwningNode::try_from(Scalar::Bool(true)), Ok(OwningNode::Bool(true)));
  }

  #[test]
  fn from_false() {
    assert_eq!(OwningNode::try_from(Scalar::Bool(false)), Ok(OwningNode::Bool(false)));
  }

  mod integer {
    use super::*;

    #[test]
    fn from_zero() {
      assert_eq!(OwningNode::try_from(Scalar::Number(0u64.into())), Ok(OwningNode::Int(0)));
    }

    #[test]
    fn from_positive() {
      assert_eq!(OwningNode::try_from(Scalar::Number(42u64.into())), Ok(OwningNode::Int(42)));
    }

    #[test]
    fn from_negative() {
      assert_eq!(OwningNode::try_from(Scalar::Number((-42i64).into())), Ok(OwningNode::Unary {
        op: UnaryOp::Neg,
        expr: Box::new(OwningNode::Int(42))
      }));
    }
  }

  mod float {
    use super::*;

    #[test]
    fn from_zero() {
      assert_eq!(OwningNode::try_from(Scalar::Number(0.0.into())), Ok(OwningNode::Float(0.0.into())));
    }

    #[test]
    fn from_positive() {
      assert_eq!(OwningNode::try_from(Scalar::Number(4.2.into())), Ok(OwningNode::Float(4.2.into())));
    }

    #[test]
    fn from_negative() {
      assert_eq!(OwningNode::try_from(Scalar::Number((-4.2).into())), Ok(OwningNode::Float((-4.2).into())));
    }
  }

  #[test]
  fn from_string() {
    assert_eq!(OwningNode::try_from(Scalar::String("_".into())), Ok(OwningNode::Name("_".into())));
    assert_eq!(OwningNode::try_from(Scalar::String("1 + 2".into())), Ok(OwningNode::Binary {
      op: BinaryOp::Add,
      left:  Box::new(OwningNode::Int(1)),
      right: Box::new(OwningNode::Int(2)),
    }));
  }
}
