//! Validated AST of expressions from a [parser] module.
//!
//! [parser]: ../parser/expressions/index.html

use std::convert::TryFrom;
use std::hint::unreachable_unchecked;

use bigdecimal::num_bigint::BigInt;
use bigdecimal::num_traits::{One, Zero};
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

      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      Node::Attr(val) => Attr(FieldName::valid(val)),
      Node::SpecialName(val) => SpecialName(val),
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
      Node::Binary { op, left, right } => {
        use BinaryOp::*;

        let left  = Self::validate(*left)?;
        let right = Self::validate(*right)?;

        macro_rules! arm {
          (
            $l1:ident, $r1:ident, $r2:ident;
            $l:ident, $r:ident;
            $op1:ident, $op2:ident;
            $res1:ident($expr1:expr);
            $res2:ident($expr2:expr);
          ) => {
            match (&*$l1, &*$r1, &$r2) {
              (_, Int($l),   Int($r)  ) => Binary { op: $res1, left: Box::new(Int  ($expr1)), right: $l1 },
              (_, Float($l), Float($r)) => Binary { op: $res1, left: Box::new(Float($expr1)), right: $l1 },

              (Int($l),   _, Int($r)  ) => Binary { op: $res2, left: Box::new(Int  ($expr2)), right: $r1 },
              (Float($l), _, Float($r)) => Binary { op: $res2, left: Box::new(Float($expr2)), right: $r1 },

              _ => Binary {
                op: $op1,
                left:  Box::new(Binary { op: $op2, left: $l1, right: $r1 }),
                right: Box::new($r2),
              },
            }
          };
        }

        match (op, left, right) {
          //TODO: Check types before simplification
          (Add, Str(l), r) if l.is_empty() => r,
          (Add, l, Str(r)) if r.is_empty() => l,

          (Add, Int(l), r) if l.is_zero() => r,
          (Add, l, Int(r)) if r.is_zero() => l,
          (Sub, Int(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Int(r)) if r.is_zero() => l,

          (Add, Float(l), r) if l.is_zero() => r,
          (Add, l, Float(r)) if r.is_zero() => l,
          (Sub, Float(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Float(r)) if r.is_zero() => l,

          //---------------------------------------------------------------------------------------
          (Mul, Int(l), _) if l.is_zero() => Int(0.into()),// 0 * x = 0
          (Mul, _, Int(r)) if r.is_zero() => Int(0.into()),// x * 0 = 0
          (Div, Int(l), _) if l.is_zero() => Int(0.into()),// 0 / x = 0

          (Mul, Float(l), _) if l.is_zero() => Int(0.into()),// 0 * x = 0
          (Mul, _, Float(r)) if r.is_zero() => Int(0.into()),// x * 0 = 0
          (Div, Float(r), _) if r.is_zero() => Int(0.into()),// 0 / x = 0

          (Mul, Int(l), r) if l.is_one() => r,// 1 * x = x
          (Mul, l, Int(r)) if r.is_one() => l,// x * 1 = x
          (Div, l, Int(r)) if r.is_one() => l,// x / 1 = x

          (Mul, Float(l), r) if l.is_one() => r,// 1 * x = x
          (Mul, l, Float(r)) if r.is_one() => l,// x * 1 = x
          (Div, l, Float(r)) if r.is_one() => l,// x / 1 = x

          //=======================================================================================
          // _ + L + R      L + _ + R  =>  SUM + _
          //     +              +            +
          //    / \            / \          / \
          //   +   R    OR    +   R      SUM   _
          //  / \            / \        (L+R)
          // _   L          L   _
          (Add, Binary { op: Add, left: l1, right: r1 }, r2) => match (&*l1, &*r1, &r2) {
            (_, Str(l),   Str(r)  ) => Binary { op: Add, left: l1, right: Box::new(Str(l.to_owned() + r)) },

            (_, Int(l),   Int(r)  ) => Binary { op: Add, left: Box::new(Int  (l + r)), right: l1 },
            (_, Float(l), Float(r)) => Binary { op: Add, left: Box::new(Float(l + r)), right: l1 },

            (Int(l),   _, Int(r)  ) => Binary { op: Add, left: Box::new(Int  (l + r)), right: r1 },
            (Float(l), _, Float(r)) => Binary { op: Add, left: Box::new(Float(l + r)), right: r1 },

            _ => Binary {
              op: Add,
              left:  Box::new(Binary { op: Add, left: l1, right: r1 }),
              right: Box::new(r2),
            },
          },
          (Mul, Binary { op: Mul, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Mul, Mul;
            Mul(l * r);
            Mul(l * r);
          ),
          //---------------------------------------------------------------------------------------
          // _ - L + R  =>  SUB + _            L - _ + R  =>  SUM - _
          //     +              +                  +              -
          //    / \            / \                / \            / \
          //   -   R        SUB   _      OR      -   R        SUM   _
          //  / \          (R-L)                / \          (L+R)
          // _   L                             L   _
          (Add, Binary { op: Sub, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Add, Sub;
            Add(r - l);
            Sub(r + l);
          ),
          (Mul, Binary { op: Div, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Mul, Div;
            Mul(r / l);
            Div(r * l);
          ),
          /*(Add, Binary { op: Sub, left: l1, right: r1 }, r2) => match (&*l1, &*r1, &r2) {
            (_, Int(l),   Int(r)  ) => Binary { op: Add, left: Box::new(Int  (r - l)), right: l1 },
            (_, Float(l), Float(r)) => Binary { op: Add, left: Box::new(Float(r - l)), right: l1 },

            (Int(l),   _, Int(r)  ) => Binary { op: Sub, left: Box::new(Int  (l + r)), right: r1 },
            (Float(l), _, Float(r)) => Binary { op: Sub, left: Box::new(Float(l + r)), right: r1 },

            _ => Binary {
              op: Add,
              left:  Box::new(Binary { op: Sub, left: l1, right: r1 }),
              right: Box::new(r2),
            },
          },*/
          //---------------------------------------------------------------------------------------
          // _ - L - R  =>  SUM + _          L - _ - R  =>  SUB - _
          //     -            +                  -              -
          //    / \          / \                / \            / \
          //   -   R      SUM   _      OR      -   R        SUB   _
          //  / \       (-L-R)                / \          (L-R)
          // _   L                           L   _
          (Sub, Binary { op: Sub, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Sub, Sub;
            Add(-l - r);
            Sub( l - r);
          ),
          (Div, Binary { op: Div, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Div, Div;
            Mul(1/(l * r));
            Div(l / r);
          ),
          /*(Sub, Binary { op: Sub, left: l1, right: r1 }, r2) => match (&*l1, &*r1, &r2) {
            (_, Int(l),   Int(r)  ) => Binary { op: Sub, left: l1, right: Box::new(Int  (l + r)) },
            (_, Float(l), Float(r)) => Binary { op: Sub, left: l1, right: Box::new(Float(l + r)) },

            (Int(l),   _, Int(r)  ) => Binary { op: Sub, left: Box::new(Int  (l - r)), right: r1 },
            (Float(l), _, Float(r)) => Binary { op: Sub, left: Box::new(Float(l - r)), right: r1 },

            _ => Binary {
              op: Sub,
              left:  Box::new(Binary { op: Sub, left: l1, right: r1 }),
              right: Box::new(r2),
            },
          },*/
          //---------------------------------------------------------------------------------------
          // _ + L - R        L + _ - R  =>  SUB + _
          //     -                -              +
          //    / \              / \            / \
          //   +   R    OR      +   R        SUB   _
          //  / \              / \          (L-R)
          // _   L            L   _
          (Sub, Binary { op: Add, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Sub, Add;
            Add(l - r);
            Add(l - r);
          ),
          (Div, Binary { op: Mul, left: l1, right: r1 }, r2) => arm!(
            l1, r1, r2;
            l, r;
            Div, Mul;
            Mul(l / r);
            Mul(l / r);
          ),
          /*(Sub, Binary { op: Add, left: l1, right: r1 }, r2) => match (&*l1, &*r1, &r2) {
            (_, Int(l),   Int(r)  ) => Binary { op: Add, left: Box::new(Int  (l - r)), right: l1 },
            (_, Float(l), Float(r)) => Binary { op: Add, left: Box::new(Float(l - r)), right: l1 },

            (Int(l),   _, Int(r)  ) => Binary { op: Add, left: Box::new(Int  (l - r)), right: r1 },
            (Float(l), _, Float(r)) => Binary { op: Add, left: Box::new(Float(l - r)), right: r1 },

            _ => Binary {
              op: Sub,
              left:  Box::new(Binary { op: Add, left: l1, right: r1 }),
              right: Box::new(r2),
            },
          },*/
          //=======================================================================================
          (Add, Str(l), Str(r)) => Str(l + &r),

          (Le, Str(l), Str(r)) => Bool(l <= r),
          (Ge, Str(l), Str(r)) => Bool(l >= r),
          (Lt, Str(l), Str(r)) => Bool(l < r),
          (Gt, Str(l), Str(r)) => Bool(l > r),

          //---------------------------------------------------------------------------------------
          (Add, Int(l), r) if l.is_zero() => r,
          (Add, l, Int(r)) if r.is_zero() => l,
          (Sub, Int(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Int(r)) if r.is_zero() => l,

          (Add, Float(l), r) if l.is_zero() => r,
          (Add, l, Float(r)) if r.is_zero() => l,
          (Sub, Float(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Float(r)) if r.is_zero() => l,

          (Mul, Int(l), r) if l.is_one() => r,
          (Mul, l, Int(r)) if r.is_one() => l,
          (Div, l, Int(r)) if r.is_one() => l,

          (Mul, Float(l), r) if l.is_one() => r,
          (Mul, l, Float(r)) if r.is_one() => l,
          (Div, l, Float(r)) if r.is_one() => l,
          //---------------------------------------------------------------------------------------

          (Add, Int(l), Int(r)) => Int(l + r),
          (Sub, Int(l), Int(r)) => Int(l - r),
          (Mul, Int(l), Int(r)) => Int(l * r),
          (Div, Int(l), Int(r)) => Int(l / r),
          // Rust `%` uses modulo operation (negative result for negative `l`), but Kaitai Struct
          // uses remainder operation (always positive result): https://doc.kaitai.io/user_guide.html#_operators
          // (Rem, Int(l), Int(r)) => Int(l.rem_euclid(r)),

          // (Shl, Int(l), Int(r)) => Int(l << r),
          // (Shr, Int(l), Int(r)) => Int(l >> r),

          (Le, Int(l), Int(r)) => Bool(l <= r),
          (Ge, Int(l), Int(r)) => Bool(l >= r),
          (Lt, Int(l), Int(r)) => Bool(l < r),
          (Gt, Int(l), Int(r)) => Bool(l > r),

          (BitAnd, Int(l), Int(r)) => Int(l & r),
          (BitOr,  Int(l), Int(r)) => Int(l | r),
          (BitXor, Int(l), Int(r)) => Int(l ^ r),
          //---------------------------------------------------------------------------------------

          (Add, Float(l), Float(r)) => Float(l + r),
          (Sub, Float(l), Float(r)) => Float(l - r),
          (Mul, Float(l), Float(r)) => Float(l * r),
          (Div, Float(l), Float(r)) => Float(l / r),

          (Le, Float(l), Float(r)) => Bool(l <= r),
          (Ge, Float(l), Float(r)) => Bool(l >= r),
          (Lt, Float(l), Float(r)) => Bool(l < r),
          (Gt, Float(l), Float(r)) => Bool(l > r),
          //---------------------------------------------------------------------------------------

          (And, Bool(l), Bool(r)) => Bool(l && r),
          (Or,  Bool(l), Bool(r)) => Bool(l || r),

          //---------------------------------------------------------------------------------------
          (Eq, l, r) if l == r => Bool(true),
          (Ne, l, r) if l != r => Bool(false),

          //---------------------------------------------------------------------------------------
          (_, l, r) => Binary {
            op,
            left:  Box::new(l),
            right: Box::new(r),
          },
        }
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
    match Self::validate(Node::from(number)) {
      Ok(node) => node,
      // SAFETY: conversion from numerical Node into OwningNode always successful
      Err(_) => unsafe { unreachable_unchecked() },
    }
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
  use ModelError::*;
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

  /// Checks that the binary operators behaves correctly
  mod binary {
    use super::*;

    /// Checks that the `+` operator behaves correctly
    mod add {
      use super::*;
      use BinaryOp::Add;

      /// Checks that adding to int behaves correctly
      mod int {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn and_int() {
          assert_eq!(OwningNode::parse(r#" 0 +  0"#), Ok(Int(0.into())));
          assert_eq!(OwningNode::parse(r#" 0 + 42"#), Ok(Int(42.into())));
          assert_eq!(OwningNode::parse(r#"42 +  0"#), Ok(Int(42.into())));
          assert_eq!(OwningNode::parse(r#"21 + 21"#), Ok(Int(42.into())));
        }

        /// Adding floating-point should change type of expression to float
        #[test]
        fn and_float() {
          assert_eq!(OwningNode::parse(r#" 0 +  0.0"#), Ok(Float(0.into())));
          assert_eq!(OwningNode::parse(r#" 0 + 42.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"42 +  0.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"21 + 21.0"#), Ok(Float(42.into())));
        }

        /// Adding bool to the int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_bool() {
          assert_eq!(OwningNode::parse(r#" 0 +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0 + false"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 + false"#), Err(Validation("".into())));
        }

        /// Adding string to the int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_str() {
          assert_eq!(OwningNode::parse(r#" 0 + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0 + 'a'"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 + 'a'"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#" 0 + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0 + "a""#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42 + "a""#), Err(Validation("".into())));
        }

        #[test]
        fn add_field() {//TODO: result depends on the type of field - int and float are acceptable
          assert_eq!(OwningNode::parse(r#" 0 + x"#), Ok(Attr(FieldName::valid("x"))));
          assert_eq!(OwningNode::parse(r#"42 + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Int(42.into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }));
        }
      }

      /// Checks that adding to int behaves correctly
      mod float {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn and_int() {
          assert_eq!(OwningNode::parse(r#" 0.0 +  0"#), Ok(Float(0.into())));
          assert_eq!(OwningNode::parse(r#" 0.0 + 42"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"42.0 +  0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"21.0 + 21"#), Ok(Float(42.into())));
        }

        #[test]
        fn and_float() {
          assert_eq!(OwningNode::parse(r#" 0.0 +  0.0"#), Ok(Float(0.into())));
          assert_eq!(OwningNode::parse(r#" 0.0 + 42.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"42.0 +  0.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"21.0 + 21.0"#), Ok(Float(42.into())));
        }

        /// Adding bool to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_bool() {
          assert_eq!(OwningNode::parse(r#" 0.0 +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0.0 + false"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 + false"#), Err(Validation("".into())));
        }

        /// Adding string to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_str() {
          assert_eq!(OwningNode::parse(r#" 0.0 + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0.0 + 'a'"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 + 'a'"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#" 0.0 + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" 0.0 + "a""#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"42.0 + "a""#), Err(Validation("".into())));
        }

        #[test]
        fn add_field() {//TODO: result depends on the type of field - float and int are acceptable
          assert_eq!(OwningNode::parse(r#" 0.0 + x"#), Ok(Attr(FieldName::valid("x"))));
          assert_eq!(OwningNode::parse(r#"42.0 + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Float(42.into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }));
        }
      }

      /// Checks that adding to int behaves correctly
      mod bool {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Adding int to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_int() {
          assert_eq!(OwningNode::parse(r#" true +  0"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" true + 42"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false +  0"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + 42"#), Err(Validation("".into())));
        }

        /// Adding floating-point to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_float() {
          assert_eq!(OwningNode::parse(r#" 0 +  0.0"#), Ok(Float(0.into())));
          assert_eq!(OwningNode::parse(r#" 0 + 42.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"42 +  0.0"#), Ok(Float(42.into())));
          assert_eq!(OwningNode::parse(r#"21 + 21.0"#), Ok(Float(42.into())));
        }

        /// Adding bool to the bool should be an error and suggestion of using the `and`
        /// operator is expected
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_bool() {
          assert_eq!(OwningNode::parse(r#" true +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" true + false"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + false"#), Err(Validation("".into())));
        }

        /// Adding string to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_str() {
          assert_eq!(OwningNode::parse(r#" true + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" true + 'a'"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + '' "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + 'a'"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#" true + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#" true + "a""#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + "" "#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + "a""#), Err(Validation("".into())));
        }

        /// Adding bool should be an error and suggestion of using the `and`
        /// operator is expected
        #[test]
        #[ignore]//TODO: implement type checking
        fn add_field() {//TODO: result depends on the type of field
          assert_eq!(OwningNode::parse(r#" true + x"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"false + x"#), Err(Validation("".into())));
        }
      }

      /// Checks that string concatenation with other types behaves correctly
      mod str {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Adding int to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_int() {
          assert_eq!(OwningNode::parse(r#"''  + 42"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"'a' + 42"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#"""  + 42"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#""a" + 42"#), Err(Validation("".into())));
        }

        /// Adding float to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_float() {
          assert_eq!(OwningNode::parse(r#"''  + 4.2"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"'a' + 4.2"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#"""  + 4.2"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#""a" + 4.2"#), Err(Validation("".into())));
        }

        /// Adding bool to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_bool() {
          assert_eq!(OwningNode::parse(r#"''  +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"''  + false"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"'a' +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"'a' + false"#), Err(Validation("".into())));

          assert_eq!(OwningNode::parse(r#"""  +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#"""  + false"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#""a" +  true"#), Err(Validation("".into())));
          assert_eq!(OwningNode::parse(r#""a" + false"#), Err(Validation("".into())));
        }

        /// Adding string should produce concatenated string
        #[test]
        fn and_str() {
          // single quotes
          assert_eq!(OwningNode::parse(r#"''  + '' "#), Ok(Str("".into())));
          assert_eq!(OwningNode::parse(r#"''  + 'a'"#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#"'a' + '' "#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#"'a' + 'b'"#), Ok(Str("ab".into())));

          // double quotes
          assert_eq!(OwningNode::parse(r#"""  + "" "#), Ok(Str("".into())));
          assert_eq!(OwningNode::parse(r#"""  + "a""#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#""a" + "" "#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#""a" + "b""#), Ok(Str("ab".into())));

          // mixed quotes - '' + ""
          assert_eq!(OwningNode::parse(r#"''  + "" "#), Ok(Str("".into())));
          assert_eq!(OwningNode::parse(r#"''  + "a""#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#"'a' + "" "#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#"'a' + "b""#), Ok(Str("ab".into())));

          // mixed quotes - "" - ''
          assert_eq!(OwningNode::parse(r#"""  + '' "#), Ok(Str("".into())));
          assert_eq!(OwningNode::parse(r#"""  + 'a'"#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#""a" + '' "#), Ok(Str("a".into())));
          assert_eq!(OwningNode::parse(r#""a" + 'b'"#), Ok(Str("ab".into())));
        }

        #[test]
        fn and_field() {//TODO: result depends on the type of field
          assert_eq!(OwningNode::parse(r#"''  + x"#), Ok(Attr(FieldName::valid("x"))));
          assert_eq!(OwningNode::parse(r#"'a' + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }));

          assert_eq!(OwningNode::parse(r#"""  + x"#), Ok(Attr(FieldName::valid("x"))));
          assert_eq!(OwningNode::parse(r#""a" + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }));
        }
      }
    }

    mod triplets {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;
      use BinaryOp::Add;

      #[test]
      fn int() {
        assert_eq!(OwningNode::parse("x + 1 + 2").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
        assert_eq!(OwningNode::parse("1 + x + 2").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
        assert_eq!(OwningNode::parse("1 + 2 + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });

        assert_eq!(OwningNode::parse("1 + 2 + 3 + x + 4 + 5 + 6").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(21.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
      }

      #[test]
      fn float() {
        assert_eq!(OwningNode::parse("x + 1.0 + 2.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
        assert_eq!(OwningNode::parse("1.0 + x + 2.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
        assert_eq!(OwningNode::parse("1.0 + 2.0 + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });

        assert_eq!(OwningNode::parse("1.0 + 2.0 + 3.0 + x + 4.0 + 5.0 + 6.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(21.into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });
      }

      #[test]
      fn str() {
        assert_eq!(OwningNode::parse("x + 'a' + 'b'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Attr(FieldName::valid("x"))),
          right: Box::new(Str("ab".into())),
        });
        assert_eq!(OwningNode::parse("'a' + x + 'b'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }),
          right: Box::new(Str("b".into())),
        });
        assert_eq!(OwningNode::parse("'a' + 'b' + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Str("ab".into())),
          right: Box::new(Attr(FieldName::valid("x"))),
        });

        assert_eq!(OwningNode::parse("'a' + 'b' + 'c' + x + 'd' + 'e' + 'f'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Binary {
            op: Add,
            left:  Box::new(Str("abc".into())),
            right: Box::new(Attr(FieldName::valid("x"))),
          }),
          right: Box::new(Str("def".into())),
        });
      }
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

  #[test]
  #[ignore]
  fn index() {//TODO: Index validation
    assert_eq!(OwningNode::parse("[3, 1, 4][-1]"), Ok(Int(4.into())));
    assert_eq!(OwningNode::parse("[3, 1, 4][ 2]"), Ok(Int(4.into())));
    assert_eq!(OwningNode::parse("[3, 1, x][ 2]"), Ok(Attr(FieldName::valid("x"))));
    assert_eq!(OwningNode::parse("[3, 1, 4][ x]"), Ok(Index {
      expr:  Box::new(List(vec![
        Int(3.into()),
        Int(1.into()),
        Int(4.into()),
      ])),
      index: Box::new(Attr(FieldName::valid("x"))),
    }));

    assert_eq!(OwningNode::parse("[3, 1, 4][ 3]"), Err(Validation("".into())));
  }
}
