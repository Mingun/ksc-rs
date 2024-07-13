//! Validated AST of expressions from a [parser] module.
//!
//! [parser]: ../parser/expressions/index.html

use std::convert::TryFrom;

use bigdecimal::num_bigint::BigInt;
use bigdecimal::BigDecimal;
use serde_yml::Number;

use crate::error::ModelError;
use crate::model::{EnumName, EnumValueName, FieldName, TypeName as TName};
use crate::parser::expressions::{
  parse_single, BinaryOp, Node, Scope, SpecialName, TypeName, TypeRef, UnaryOp,
};
use crate::parser::Scalar;

/// Owning counterpart of an AST [`Node`].
///
/// [`Node`]: ./enum.Node.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwningNode {
  /// String constant
  Str(String),
  /// Integral constant
  Int(BigInt),
  /// Floating-point constant
  Float(BigDecimal),
  /// Boolean constant
  Bool(bool),

  /// Name of field of the type in which attribute expression is defined
  Attr(FieldName),
  /// Built-in variable
  SpecialName(SpecialName),
  /// Reference to an enum value.
  EnumValue {
    /// A type that defines this enum.
    scope: OwningScope,
    /// An enum name.
    name: EnumName,
    /// An enum value.
    value: EnumValueName,
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
    attr: FieldName,
  },

  /// The unary prefix operator, such as unary `-` or logical `not`.
  Unary {
    /// Operation to apply
    op: UnaryOp,
    /// Expression for applying operator
    expr: Box<OwningNode>,
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
impl OwningNode {
  /// Parses and validates an expression
  ///
  /// # Parameters
  /// - `expr`: Kaitai struct language expression. See [module level documentation]
  ///   for syntax
  ///
  /// [module level documentation]: ./index.html
  pub fn parse(expr: &str) -> Result<Self, ModelError> {
    Ok(parse_single(expr)?.into())
  }
  /// Performs validation of all nodes in an argument
  ///
  /// # Parameters
  /// - `nodes`: List of nodes for validation
  pub fn validate_all(nodes: Vec<Node>) -> Vec<Self> {
    nodes.into_iter().map(Into::into).collect()
  }
}
impl<'input> From<Node<'input>> for OwningNode {
  fn from(reference: Node<'input>) -> Self {
    use OwningNode::*;

    match reference {
      Node::Str(val)  => Str(val),
      Node::Int(val)  => Int(val),
      Node::Float(val)=> Float(val),
      Node::Bool(val) => Bool(val),

      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      Node::Attr(val) => Attr(FieldName::valid(val)),
      Node::SpecialName(val) => SpecialName(val),
      //TODO: Names already contains only valid symbols, but need to check that they is really exists
      Node::EnumValue { scope, name, value } => EnumValue {
        scope: scope.into(),
        name:  EnumName::valid(name),
        value: EnumValueName::valid(value),
      },

      Node::List(val) => List(Self::validate_all(val)),

      Node::SizeOf { type_, bit } => SizeOf { type_: type_.into(), bit },

      Node::Call { callee, args } => Call {
        callee: Box::new((*callee).into()),
        args: Self::validate_all(args),
      },
      Node::Cast { expr, to_type } => Cast {
        expr: Box::new((*expr).into()),
        to_type: to_type.into(),
      },
      Node::Index { expr, index } => Index {
        expr:  Box::new((*expr).into()),
        index: Box::new((*index).into()),
      },
      Node::Access { expr, attr } => Access {
        expr: Box::new((*expr).into()),
        //TODO: Name already contains only valid symbols, but need to check that it is really exists
        attr: FieldName::valid(attr),
      },

      Node::Unary { op, expr } => {
        use UnaryOp::*;

        match (op, (*expr).into()) {
          // Remove doubled operators
          (first, Unary { op, expr }) if first == op => *expr,

          // Constant evaluations
          (Neg, Int(value)) => Int(-value),
          (Neg, Float(value)) => Float(-value),

          (Not, Bool(value)) => Bool(!value),
          (Inv, Int(value))  => Int(!value),

          //TODO: check that operator is compatible with operand types in generic path

          // Generic path
          (_, expr) => Unary { op, expr: Box::new(expr) },
        }
      }
      Node::Binary { op, left, right } => Binary {
        op,
        left:  Box::new((*left).into()),
        right: Box::new((*right).into()),
      },
      Node::Branch { condition, if_true, if_false } => {
        let condition = (*condition).into();
        let if_true   = (*if_true).into();
        let if_false  = (*if_false).into();

        match condition {
          Bool(true)  => if_true,
          Bool(false) => if_false,
          _ => Branch {
            condition: Box::new(condition),
            if_true:   Box::new(if_true),
            if_false:  Box::new(if_false),
          },
        }
      }
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
      String(val) => Ok(Self::parse(&val)?),
    }
  }
}

macro_rules! from_int {
  ($($ty:ty,)*) => {$(
    impl From<$ty> for OwningNode {
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
impl From<bool> for OwningNode {
  #[inline]
  fn from(value: bool) -> Self {
    Self::Bool(value)
  }
}
impl<'a> From<&'a str> for OwningNode {
  #[inline]
  fn from(string: &'a str) -> Self {
    Self::Str(string.into())
  }
}
impl From<String> for OwningNode {
  #[inline]
  fn from(string: String) -> Self {
    Self::Str(string)
  }
}

/// Owning counterpart of a [`Scope`].
///
/// [`Scope`]: ./struct.Scope.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OwningScope {
  /// Path starts from a top-level type of the current KSY file.
  pub absolute: bool,
  /// Names of types defining this scope.
  pub path: Vec<TName>,
}
impl<'input> From<Scope<'input>> for OwningScope {
  fn from(reference: Scope<'input>) -> Self {
    Self {
      absolute: reference.absolute,
      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      path:     reference.path.into_iter().map(TName::valid).collect(),
    }
  }
}

/// Owning counterpart of a [`TypeName`].
///
/// [`TypeName`]: ./struct.TypeName.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OwningTypeName {
  /// A scope in which type is defined
  pub scope: OwningScope,
  /// A local name of the referenced type
  pub name: TName,
}
impl<'input> From<TypeName<'input>> for OwningTypeName {
  fn from(reference: TypeName<'input>) -> Self {
    Self {
      scope: reference.scope.into(),
      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      name:  TName::valid(reference.name),
    }
  }
}

/// Owning counterpart of a [`TypeRef`].
///
/// [`TypeRef`]: ./struct.TypeRef.html
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OwningTypeRef {
  /// A possible qualified type name of the type used
  pub name: OwningTypeName,
  /// If `true` then reference represents an array of the specified type.
  pub array: bool,
}
impl<'input> From<TypeRef<'input>> for OwningTypeRef {
  fn from(reference: TypeRef<'input>) -> Self {
    Self {
      name:  reference.name.into(),
      array: reference.array,
    }
  }
}

#[cfg(test)]
mod convert {
  use super::*;
  use pretty_assertions::assert_eq;
  use OwningNode::*;

  #[test]
  fn from_null() {
    assert!(OwningNode::try_from(Scalar::Null).is_err());
  }

  #[test]
  fn from_true() {
    assert_eq!(OwningNode::try_from(Scalar::Bool(true)), Ok(Bool(true)));
  }

  #[test]
  fn from_false() {
    assert_eq!(OwningNode::try_from(Scalar::Bool(false)), Ok(Bool(false)));
  }

  mod integer {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn from_zero() {
      assert_eq!(OwningNode::try_from(Scalar::Number(0u64.into())), Ok(Int(0.into())));
    }

    #[test]
    fn from_positive() {
      assert_eq!(OwningNode::try_from(Scalar::Number(42u64.into())), Ok(Int(42.into())));
    }

    #[test]
    fn from_negative() {
      assert_eq!(OwningNode::try_from(Scalar::Number((-42i64).into())), Ok(Int((-42).into())));
    }
  }

  mod float {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn from_zero() {
      assert_eq!(OwningNode::try_from(Scalar::Number(0.0.into())), Ok(Float(0.into())));
    }

    #[test]
    fn from_positive() {
      assert_eq!(OwningNode::try_from(Scalar::Number(4.5.into())), Ok(Float((45, 1).into())));
    }

    #[test]
    fn from_negative() {
      assert_eq!(OwningNode::try_from(Scalar::Number((-4.5).into())), Ok(Float((-45, 1).into())));
    }
  }

  #[test]
  fn from_string() {
    assert_eq!(OwningNode::try_from(Scalar::String("id".into())), Ok(Attr(FieldName::valid("id"))));
    assert_eq!(OwningNode::try_from(Scalar::String("x + 2".into())), Ok(Binary {
      op: BinaryOp::Add,
      left:  Box::new(Attr(FieldName::valid("x"))),
      right: Box::new(Int(2.into())),
    }));
  }
}

#[cfg(test)]
mod evaluation {
  use super::*;
  use pretty_assertions::assert_eq;
  use OwningNode::*;

  /// Check that the unary operators behaves correctly
  mod unary {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn double_neg() {
      assert_eq!(OwningNode::parse("-(-x)"), Ok(Attr(FieldName::valid("x"))));
    }

    #[test]
    fn double_not() {
      assert_eq!(OwningNode::parse("not not x"), Ok(Attr(FieldName::valid("x"))));
    }

    #[test]
    fn double_inv() {
      assert_eq!(OwningNode::parse("~~x"), Ok(Attr(FieldName::valid("x"))));
    }
  }

  #[test]
  fn branch() {
    assert_eq!(OwningNode::parse("true  ? a : b"), Ok(Attr(FieldName::valid("a"))));
    assert_eq!(OwningNode::parse("false ? a : b"), Ok(Attr(FieldName::valid("b"))));
    assert_eq!(OwningNode::parse("condition ? a : b"), Ok(Branch {
      condition: Box::new(Attr(FieldName::valid("condition"))),
      if_true:   Box::new(Attr(FieldName::valid("a"))),
      if_false:  Box::new(Attr(FieldName::valid("b"))),
    }));
  }
}
