//! Validated AST of expressions from a [parser] module.
//!
//! [parser]: crate::parser::expressions

use std::convert::TryFrom;

use bigdecimal::num_bigint::BigInt;
use bigdecimal::BigDecimal;
use serde_yml::Number;

use crate::error::ModelError;
use crate::model::{EnumName, EnumValueName, FieldName, TypeName as TName};
use crate::parser::expressions::{
  parse_name, parse_single, Attr, BinaryOp, ContextVar, Node, Scope, TypeName, TypeRef, UnaryOp,
};
use crate::parser::Scalar;

/// Owning counterpart of an AST [`Node`].
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

  /// String with embedded expressions (interpolated string, f-string).
  ///
  /// Literal parts represented by [`OwningNode::Str`] node, interpolated parts
  /// represented by any other nodes.
  InterpolatedStr(Vec<OwningNode>),

  /// Built-in variable
  ContextVar(ContextVar),

  /// Name of field of the type in which attribute expression is defined
  Attr(OwningAttr),
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
    Self::validate(parse_single(expr)?)
  }
  /// Performs a semantic validation of raw parsed expression
  pub fn validate(node: Node) -> Result<Self, ModelError> {
    use OwningNode::*;

    Ok(match node {
      Node::Str(val)  => Str(val),
      Node::Int(val)  => Int(val),
      Node::Float(val)=> Float(val),
      Node::Bool(val) => Bool(val),
      Node::InterpolatedStr(val) => InterpolatedStr(Self::validate_all(val)?),

      Node::ContextVar(val) => ContextVar(val),

      //TODO: Need to check that attribute is really exists in the type
      Node::Attr(val) => Attr(val.try_into()?),
      //TODO: Names already contains only valid symbols, but need to check that they is really exists
      Node::EnumValue { scope, name, value } => EnumValue {
        scope: scope.into(),
        name:  EnumName::valid(name),
        value: EnumValueName::valid(value),
      },

      Node::List(val) => List(Self::validate_all(val)?),

      Node::SizeOf { type_, bit } => SizeOf { type_: type_.into(), bit },

      Node::Call { callee, args } => Call {
        callee: Box::new(Self::validate(*callee)?),
        args: Self::validate_all(args)?,
      },
      Node::Cast { expr, to_type } => Cast {
        expr: Box::new(Self::validate(*expr)?),
        to_type: to_type.into(),
      },
      Node::Index { expr, index } => Index {
        expr:  Box::new(Self::validate(*expr)?),
        index: Box::new(Self::validate(*index)?),
      },
      Node::Access { expr, attr } => Access {
        expr: Box::new(Self::validate(*expr)?),
        //TODO: Name already contains only valid symbols, but need to check that it is really exists
        attr: FieldName::valid(attr),
      },

      Node::Unary { op, expr } => {
        use UnaryOp::*;

        match (op, Self::validate(*expr)?) {
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
        left:  Box::new(Self::validate(*left)?),
        right: Box::new(Self::validate(*right)?),
      },
      Node::Branch { condition, if_true, if_false } => {
        let condition = Self::validate(*condition)?;
        let if_true   = Self::validate(*if_true)?;
        let if_false  = Self::validate(*if_false)?;

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
    })
  }
  /// Performs validation of all nodes in an argument and returns a validated
  /// AST node or the first error.
  ///
  /// # Parameters
  /// - `nodes`: List of nodes for validation
  pub fn validate_all(nodes: Vec<Node>) -> Result<Vec<Self>, ModelError> {
    nodes.into_iter().map(Self::validate).collect::<Result<_, _>>()
  }
}
impl From<Number> for OwningNode {
  #[inline]
  fn from(number: Number) -> Self {
    // SAFETY: conversion from numerical Node into OwningNode always successful
    Self::validate(Node::from(number)).expect("Number -> Node conversion should be always success")
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

/// Owning counterpart of an [`Attr`]. Contains validated user-defined field of a type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OwningAttr {
  /// Built-in attribute `_io`: stream associated with this object of user-defined type.
  Stream,
  /// Built-in attribute `_root`: top-level user-defined structure in the current file.
  Root,
  /// Built-in attribute `_parent`: structure that produced this particular instance of the
  /// user-defined type.
  Parent,
  /// Built-in attribute `_sizeof`: used as an attribute of the struct to get a compile-time size
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
  /// User-defined attribute of the type
  User(FieldName),
}
impl<'input> TryFrom<Attr<'input>> for OwningAttr {
  type Error = ModelError;

  #[inline]
  fn try_from(reference: Attr<'input>) -> Result<Self, Self::Error> {
    Ok(match reference {
      Attr::Stream  => Self::Stream,
      Attr::Root    => Self::Root,
      Attr::Parent  => Self::Parent,
      Attr::SizeOf  => Self::SizeOf,
      Attr::User(m) => Self::User(FieldName::valid(parse_name(m)?)),
    })
  }
}
impl<'input> From<FieldName> for OwningAttr {
  #[inline]
  fn from(name: FieldName) -> Self {
    Self::User(name)
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
    assert_eq!(OwningNode::try_from(Scalar::String("id".into())), Ok(Attr(FieldName::valid("id").into())));
    assert_eq!(OwningNode::try_from(Scalar::String("x + 2".into())), Ok(Binary {
      op: BinaryOp::Add,
      left:  Box::new(Attr(FieldName::valid("x").into())),
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
      assert_eq!(OwningNode::parse("-(-x)"), Ok(Attr(FieldName::valid("x").into())));
    }

    #[test]
    fn double_not() {
      assert_eq!(OwningNode::parse("not not x"), Ok(Attr(FieldName::valid("x").into())));
    }

    #[test]
    fn double_inv() {
      assert_eq!(OwningNode::parse("~~x"), Ok(Attr(FieldName::valid("x").into())));
    }
  }

  #[test]
  fn branch() {
    assert_eq!(OwningNode::parse("true  ? a : b"), Ok(Attr(FieldName::valid("a").into())));
    assert_eq!(OwningNode::parse("false ? a : b"), Ok(Attr(FieldName::valid("b").into())));
    assert_eq!(OwningNode::parse("condition ? a : b"), Ok(Branch {
      condition: Box::new(Attr(FieldName::valid("condition").into())),
      if_true:   Box::new(Attr(FieldName::valid("a").into())),
      if_false:  Box::new(Attr(FieldName::valid("b").into())),
    }));
  }
}
