//! Validated AST of expressions from a [parser] module.
//!
//! [parser]: crate::parser::expressions

use std::convert::TryFrom;

use bigdecimal::num_bigint::BigInt;
use bigdecimal::num_traits::{One, Zero};
use bigdecimal::BigDecimal;
use serde_yml::Number;

use crate::error::ModelError;
use crate::model::{EnumName, EnumVariantName, FieldName, TypeContext, TypeName as TName};
use crate::parser::expressions::{
  parse_enum_ref, parse_name, parse_single, Attr, BinaryOp, ContextVar, EnumRef, Node, Scope,
  TypeName, TypeRef, UnaryOp,
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
  /// Reference to an enum variant.
  EnumVariant {
    /// A reference to an enum, optionally with the surrounding types.
    enum_: OwningEnumRef,
    /// An enum variant.
    variant: EnumVariantName,
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
    attr: OwningAttr,
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
  pub fn parse(expr: &str, ctx: &TypeContext) -> Result<Self, ModelError> {
    Self::validate(parse_single(expr)?, ctx)
  }
  /// Converts scalar YAML value into expression node. [`Scalar::Null`] translated
  /// into an error, [`Scalar::String`] parsed as [expression].
  ///
  /// [expression]: crate::model::expressions
  pub fn from_scalar(scalar: &Scalar, ctx: &TypeContext) -> Result<Self, ModelError> {
    match scalar {
      Scalar::Null => Err(ModelError::Validation(
        "Expected expression, but null found (note that `null` literal in YAML is \
         equivalent of absence of any value, use 'null' if you want to refer to name `null`)".into()
      )),
      Scalar::Bool(val) => Ok(Self::Bool(*val)),
      Scalar::Number(n) => Ok(n.into()),
      Scalar::String(val) => Ok(Self::parse(val, ctx)?),
    }
  }
  /// Performs a semantic validation of raw parsed expression
  pub fn validate(node: Node, ctx: &TypeContext) -> Result<Self, ModelError> {
    use OwningNode::*;

    Ok(match node {
      Node::Str(val)  => Str(val),
      Node::Int(val)  => Int(val),
      Node::Float(val)=> Float(val),
      Node::Bool(val) => Bool(val),
      Node::InterpolatedStr(val) => InterpolatedStr(Self::validate_all(val, ctx)?),

      Node::ContextVar(val) => ContextVar(val),

      //TODO: Need to check that attribute is really exists in the type
      Node::Attr(val) => Attr(val.try_into()?),
      //TODO: Names already contains only valid symbols, but need to check that they is really exists
      Node::EnumVariant { enum_, variant } => EnumVariant {
        enum_: enum_.into(),
        variant: EnumVariantName::valid(variant),
      },

      Node::List(val) => List(Self::validate_all(val, ctx)?),

      Node::SizeOf { type_, bit } => SizeOf { type_: type_.into(), bit },

      Node::Call { callee, args } => Call {
        callee: Box::new(Self::validate(*callee, ctx)?),
        args: Self::validate_all(args, ctx)?,
      },
      Node::Cast { expr, to_type } => Cast {
        expr: Box::new(Self::validate(*expr, ctx)?),
        to_type: to_type.into(),
      },
      Node::Index { expr, index } => Index {
        expr:  Box::new(Self::validate(*expr, ctx)?),
        index: Box::new(Self::validate(*index, ctx)?),
      },
      Node::Access { expr, attr } => Access {
        expr: Box::new(Self::validate(*expr, ctx)?),
        //TODO: Need to check that attribute is really exists in the type
        attr: attr.try_into()?,
      },

      Node::Unary { op, expr } => {
        use UnaryOp::*;

        match (op, Self::validate(*expr, ctx)?) {
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

        let left  = Self::validate(*left, ctx)?;
        let right = Self::validate(*right, ctx)?;

        macro_rules! fold_constants {
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
          (Add, Str(l), Str(r)) => Str(l + &r),
          //TODO: Check types before simplification
          (Add, Str(l), r) if l.is_empty() => r,
          (Add, l, Str(r)) if r.is_empty() => l,

          (Add, Int(l), Int(r)) => Int(l + r),
          (Add, Int(l), Float(r)) => Float(BigDecimal::from(l) + r),
          //TODO: Check types before simplification
          (Add, Int(l), r) if l.is_zero() => r,
          (Add, l, Int(r)) if r.is_zero() => l,

          (Add, Float(l), Int(r)) => Float(l + BigDecimal::from(r)),
          (Add, Float(l), Float(r)) => Float(l + r),
          //TODO: Check types before simplification
          (Add, Float(l), r) if l.is_zero() => r,
          (Add, l, Float(r)) if r.is_zero() => l,

          //----------------------------------------------------------------------------------------
          (Sub, Int(l), Int(r)) => Int(l - r),
          (Sub, Int(l), Float(r)) => Float(BigDecimal::from(l) - r),
          //TODO: Check types before simplification
          (Sub, Int(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Int(r)) if r.is_zero() => l,

          (Sub, Float(l), Int(r)) => Float(l - BigDecimal::from(r)),
          (Sub, Float(l), Float(r)) => Float(l - r),
          //TODO: Check types before simplification
          (Sub, Float(l), r) if l.is_zero() => Unary { op: UnaryOp::Neg, expr: Box::new(r) },
          (Sub, l, Float(r)) if r.is_zero() => l,

          //----------------------------------------------------------------------------------------
          (Mul, Int(l), Int(r)) => Int(l * r),
          (Mul, Int(l), Float(r)) => Float(l * r),
          //TODO: Check types before simplification
          (Mul, Int(l), _) if l.is_zero() => Int(0.into()),// 0 * x = 0
          (Mul, Int(l), r) if l.is_one() => r,// 1 * x = x
          (Mul, _, Int(r)) if r.is_zero() => Int(0.into()),// x * 0 = 0
          (Mul, l, Int(r)) if r.is_one() => l,// x * 1 = x

          (Mul, Float(l), Int(r)) => Float(l * r),
          (Mul, Float(l), Float(r)) => Float(l * r),
          //TODO: Check types before simplification
          (Mul, Float(l), _) if l.is_zero() => Float(0.into()),// 0 * x = 0
          (Mul, Float(l), r) if l.is_one() => r,// 1 * x = x
          (Mul, _, Float(r)) if r.is_zero() => Float(0.into()),// x * 0 = 0
          (Mul, l, Float(r)) if r.is_one() => l,// x * 1 = x

          //----------------------------------------------------------------------------------------
          (Div, Float(l), Int(r)) => Float(l / BigDecimal::from(r)),
          (Div, Float(l), Float(r)) => Float(l / r),
          (Div, l, Int(r)) if r.is_one() => l,// x / 1 = x
          (Div, l, Float(r)) if r.is_one() => l,// x / 1 = x

          //========================================================================================
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
          (Mul, Binary { op: Mul, left: l1, right: r1 }, r2) => fold_constants!(
            l1, r1, r2;
            l, r;
            Mul, Mul;
            Mul(l * r);
            Mul(l * r);
          ),
          //----------------------------------------------------------------------------------------
          // _ - L + R  =>  SUB + _            L - _ + R  =>  SUM - _
          //     +              +                  +              -
          //    / \            / \                / \            / \
          //   -   R        SUB   _      OR      -   R        SUM   _
          //  / \          (R-L)                / \          (L+R)
          // _   L                             L   _
          (Add, Binary { op: Sub, left: l1, right: r1 }, r2) => fold_constants!(
            l1, r1, r2;
            l, r;
            Add, Sub;
            Add(r - l);
            Sub(r + l);
          ),
          (Mul, Binary { op: Div, left: l1, right: r1 }, r2) => fold_constants!(
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
          //----------------------------------------------------------------------------------------
          // _ - L - R  =>  SUM + _          L - _ - R  =>  SUB - _
          //     -            +                  -              -
          //    / \          / \                / \            / \
          //   -   R      SUM   _      OR      -   R        SUB   _
          //  / \       (-L-R)                / \          (L-R)
          // _   L                           L   _
          (Sub, Binary { op: Sub, left: l1, right: r1 }, r2) => fold_constants!(
            l1, r1, r2;
            l, r;
            Sub, Sub;
            Add(-l - r);
            Sub( l - r);
          ),
          (Div, Binary { op: Div, left: l1, right: r1 }, r2) => fold_constants!(
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
          //----------------------------------------------------------------------------------------
          // _ + L - R        L + _ - R  =>  SUB + _
          //     -                -              +
          //    / \              / \            / \
          //   +   R    OR      +   R        SUB   _
          //  / \              / \          (L-R)
          // _   L            L   _
          (Sub, Binary { op: Add, left: l1, right: r1 }, r2) => fold_constants!(
            l1, r1, r2;
            l, r;
            Sub, Add;
            Add(l - r);
            Add(l - r);
          ),
          (Div, Binary { op: Mul, left: l1, right: r1 }, r2) => fold_constants!(
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
          //========================================================================================
          (Le, Str(l), Str(r)) => Bool(l <= r),
          (Ge, Str(l), Str(r)) => Bool(l >= r),
          (Lt, Str(l), Str(r)) => Bool(l < r),
          (Gt, Str(l), Str(r)) => Bool(l > r),

          //----------------------------------------------------------------------------------------
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
          //----------------------------------------------------------------------------------------

          (Le, Float(l), Float(r)) => Bool(l <= r),
          (Ge, Float(l), Float(r)) => Bool(l >= r),
          (Lt, Float(l), Float(r)) => Bool(l < r),
          (Gt, Float(l), Float(r)) => Bool(l > r),
          //----------------------------------------------------------------------------------------

          (And, Bool(l), Bool(r)) => Bool(l && r),
          (Or,  Bool(l), Bool(r)) => Bool(l || r),

          //----------------------------------------------------------------------------------------
          // If two primitives are not equal after normalization,
          // then the result is known at compile-time
          (Eq, Str(l), Str(r)) => Bool(l == r),
          (Eq, Int(l), Int(r)) => Bool(l == r),
          (Eq, Int(l), Float(r)) => Bool(r == l.into()),
          (Eq, Float(l), Int(r)) => Bool(l == r.into()),
          (Eq, Float(l), Float(r)) => Bool(l == r),
          (Eq, Bool(l), Bool(r)) => Bool(l == r),
          // Symbolic calculations: if two subtrees are equal after normalization,
          // then the result is known at compile-time
          (Eq, l, r) if l == r => Bool(true),

          //----------------------------------------------------------------------------------------
          // If two primitives are not equal after normalization,
          // then the result is known at compile-time
          (Ne, Str(l), Str(r)) => Bool(l != r),
          (Ne, Int(l), Int(r)) => Bool(l != r),
          (Ne, Int(l), Float(r)) => Bool(r != l.into()),
          (Ne, Float(l), Int(r)) => Bool(l != r.into()),
          (Ne, Float(l), Float(r)) => Bool(l != r),
          (Ne, Bool(l), Bool(r)) => Bool(l != r),

          //----------------------------------------------------------------------------------------
          (_, l, r) => Binary {
            op,
            left:  Box::new(l),
            right: Box::new(r),
          },
        }
      },
      Node::Branch { condition, if_true, if_false } => {
        let condition = Self::validate(*condition, ctx)?;
        let if_true   = Self::validate(*if_true, ctx)?;
        let if_false  = Self::validate(*if_false, ctx)?;

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
  pub fn validate_all(nodes: Vec<Node>, ctx: &TypeContext) -> Result<Vec<Self>, ModelError> {
    nodes.into_iter().map(|n| Self::validate(n, ctx)).collect()
  }
}
impl From<Number> for OwningNode {
  #[inline]
  fn from(number: Number) -> Self {
    From::from(&number)
  }
}
impl<'a> From<&'a Number> for OwningNode {
  #[inline]
  fn from(number: &'a Number) -> Self {
    match Node::from(number) {
      Node::Int(n) => Self::Int(n),
      Node::Float(n) => Self::Float(n),
      // SAFETY: conversion from number returns only numerical Nodes
      _ => unreachable!("Number -> Node conversion produces only Int and Float"),
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

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Owning counterpart of a [`Scope`].
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
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

/// Path to the enum name, used to describe `enum` in attributes and parameters.
/// Owning counterpart of a [`EnumRef`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OwningEnumRef {
  /// A scope in which enum is defined
  pub scope: OwningScope,
  /// Name of enum inside type
  pub name: EnumName,
}
impl<'input> OwningEnumRef {
  /// Parses and validates a reference to an enum
  ///
  /// # Parameters
  /// - `enum_`: Path to an enum definition, for example, `::absolute::path::to::enum`
  /// - `ctx`: context for validation and reporting errors
  pub fn validate(enum_: &crate::parser::EnumRef, ctx: &TypeContext) -> Result<Self, ModelError> {
    Ok(parse_enum_ref(&enum_.0)?.into())
  }
}
impl<'input> From<EnumRef<'input>> for OwningEnumRef {
  fn from(reference: EnumRef<'input>) -> Self {
    Self {
      scope: reference.scope.into(),
      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      name:  EnumName::valid(reference.name),
    }
  }
}
impl<'input> From<EnumName> for OwningEnumRef {
  fn from(name: EnumName) -> Self {
    Self {
      scope: OwningScope::default(),
      name,
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

////////////////////////////////////////////////////////////////////////////////////////////////////

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
  use crate::model::{Package, PackageContext};
  use crate::parser::Ksy;
  use pretty_assertions::assert_eq;
  use OwningNode::*;

  fn from_scalar(scalar: Scalar) -> Result<OwningNode, ModelError> {
    // TypeContext not used in those tests so can be created from empty KSY
    let pkg = Package::test(Ksy::default());
    let ksy = pkg.files.values().next().unwrap();
    let ctx = PackageContext::new(&pkg);
    let ctx = ctx.for_file(ksy);
    OwningNode::from_scalar(&scalar, &ctx.for_type(&ksy.root))
  }

  #[test]
  fn from_null() {
    assert!(from_scalar(Scalar::Null).is_err());
  }

  #[test]
  fn from_true() {
    assert_eq!(from_scalar(Scalar::Bool(true)), Ok(Bool(true)));
  }

  #[test]
  fn from_false() {
    assert_eq!(from_scalar(Scalar::Bool(false)), Ok(Bool(false)));
  }

  mod integer {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn from_zero() {
      assert_eq!(from_scalar(Scalar::Number(0u64.into())), Ok(Int(0.into())));
    }

    #[test]
    fn from_positive() {
      assert_eq!(from_scalar(Scalar::Number(42u64.into())), Ok(Int(42.into())));
    }

    #[test]
    fn from_negative() {
      assert_eq!(from_scalar(Scalar::Number((-42i64).into())), Ok(Int((-42).into())));
    }
  }

  mod float {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn from_zero() {
      assert_eq!(from_scalar(Scalar::Number(0.0.into())), Ok(Float(0.into())));
    }

    #[test]
    fn from_positive() {
      assert_eq!(from_scalar(Scalar::Number(4.5.into())), Ok(Float((45, 1).into())));
    }

    #[test]
    fn from_negative() {
      assert_eq!(from_scalar(Scalar::Number((-4.5).into())), Ok(Float((-45, 1).into())));
    }
  }

  #[test]
  fn from_string() {
    assert_eq!(from_scalar(Scalar::String("id".into())), Ok(Attr(FieldName::valid("id").into())));
    assert_eq!(from_scalar(Scalar::String("x + 2".into())), Ok(Binary {
      op: BinaryOp::Add,
      left:  Box::new(Attr(FieldName::valid("x").into())),
      right: Box::new(Int(2.into())),
    }));
  }
}

#[cfg(test)]
mod evaluation {
  use super::*;
  use crate::model::{Package, PackageContext};
  use crate::parser::Ksy;
  use pretty_assertions::assert_eq;
  use ModelError::*;
  use OwningNode::*;

  fn parse(expr: &str) -> Result<OwningNode, ModelError> {
    // TypeContext not used in those tests so can be created from empty KSY
    let pkg = Package::test(Ksy::default());
    let ksy = pkg.files.values().next().unwrap();
    let ctx = PackageContext::new(&pkg);
    let ctx = ctx.for_file(ksy);
    OwningNode::parse(expr, &ctx.for_type(&ksy.root))
  }

  /// Check that the unary operators behaves correctly
  mod unary {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn double_neg() {
      assert_eq!(parse("-(-x)"), Ok(Attr(FieldName::valid("x").into())));
    }

    #[test]
    fn double_not() {
      assert_eq!(parse("not not x"), Ok(Attr(FieldName::valid("x").into())));
    }

    #[test]
    fn double_inv() {
      assert_eq!(parse("~~x"), Ok(Attr(FieldName::valid("x").into())));
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
        fn int() {
          assert_eq!(parse(" 0 +  0"), Ok(Int(0.into())));
          assert_eq!(parse(" 0 + 42"), Ok(Int(42.into())));
          assert_eq!(parse("42 +  0"), Ok(Int(42.into())));
          assert_eq!(parse("21 + 21"), Ok(Int(42.into())));
        }

        /// Adding floating-point should change type of expression to float
        #[test]
        fn float() {
          assert_eq!(parse(" 0 +  0.0"), Ok(Float(0.into())));
          assert_eq!(parse(" 0 + 42.0"), Ok(Float(42.into())));
          assert_eq!(parse("42 +  0.0"), Ok(Float(42.into())));
          assert_eq!(parse("21 + 21.0"), Ok(Float(42.into())));
        }

        /// Adding bool to the int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" 0 +  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0 + false"), Err(Validation("".into())));
          assert_eq!(parse("42 +  true"), Err(Validation("".into())));
          assert_eq!(parse("42 + false"), Err(Validation("".into())));
        }

        /// Adding string to the int should be an error.
        /// `.to_s` should be used to convert value to the string first
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0 + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 + 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 + 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0 + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 + "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 + "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field - int and float are acceptable
          assert_eq!(parse(" 0 + x"), Ok(Attr(FieldName::valid("x").into())));
          assert_eq!(parse("42 + x"), Ok(Binary {
            op: Add,
            left:  Box::new(Int(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      /// Checks that adding to int behaves correctly
      mod float {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn int() {
          assert_eq!(parse(" 0.0 +  0"), Ok(Float(0.into())));
          assert_eq!(parse(" 0.0 + 42"), Ok(Float(42.into())));
          assert_eq!(parse("42.0 +  0"), Ok(Float(42.into())));
          assert_eq!(parse("21.0 + 21"), Ok(Float(42.into())));
        }

        #[test]
        fn float() {
          assert_eq!(parse(" 0.0 +  0.0"), Ok(Float(0.into())));
          assert_eq!(parse(" 0.0 + 42.0"), Ok(Float(42.into())));
          assert_eq!(parse("42.0 +  0.0"), Ok(Float(42.into())));
          assert_eq!(parse("21.0 + 21.0"), Ok(Float(42.into())));
        }

        /// Adding bool to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn and_bool() {
          assert_eq!(parse(" 0.0 +  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0.0 + false"), Err(Validation("".into())));
          assert_eq!(parse("42.0 +  true"), Err(Validation("".into())));
          assert_eq!(parse("42.0 + false"), Err(Validation("".into())));
        }

        /// Adding string to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0.0 + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 + 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 + 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0.0 + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 + "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 + "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field - float and int are acceptable
          assert_eq!(parse(" 0.0 + x"), Ok(Attr(FieldName::valid("x").into())));
          assert_eq!(parse("42.0 + x"), Ok(Binary {
            op: Add,
            left:  Box::new(Float(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      /// Checks that adding to bool behaves correctly
      mod bool {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Adding int to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn int() {
          assert_eq!(parse(" true +  0"), Err(Validation("".into())));
          assert_eq!(parse(" true + 42"), Err(Validation("".into())));
          assert_eq!(parse("false +  0"), Err(Validation("".into())));
          assert_eq!(parse("false + 42"), Err(Validation("".into())));
        }

        /// Adding floating-point to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(" 0 +  0.0"), Ok(Float(0.into())));
          assert_eq!(parse(" 0 + 42.0"), Ok(Float(42.into())));
          assert_eq!(parse("42 +  0.0"), Ok(Float(42.into())));
          assert_eq!(parse("21 + 21.0"), Ok(Float(42.into())));
        }

        /// Adding bool to the bool should be an error.
        /// Suggestion to use the `and` operator should be emitted
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" true +  true"), Err(Validation("".into())));
          assert_eq!(parse(" true + false"), Err(Validation("".into())));
          assert_eq!(parse("false +  true"), Err(Validation("".into())));
          assert_eq!(parse("false + false"), Err(Validation("".into())));
        }

        /// Adding string to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" true + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true + 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"false + '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false + 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" true + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true + "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"false + "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false + "a""#), Err(Validation("".into())));
        }

        /// Adding field to the bool should be an error.
        /// Suggestion to use the `and` operator should be emitted
        #[test]
        #[ignore]//TODO: implement type checking
        fn field() {//TODO: check for suggestion
          assert_eq!(parse(" true + x"), Err(Validation("".into())));
          assert_eq!(parse("false + x"), Err(Validation("".into())));
        }
      }

      /// Checks that string concatenation with other types behaves correctly
      mod str {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Adding int to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn int() {
          assert_eq!(parse(r#"''  + 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' + 42"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  + 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" + 42"#), Err(Validation("".into())));
        }

        /// Adding float to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(r#"''  + 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' + 4.2"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  + 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" + 4.2"#), Err(Validation("".into())));
        }

        /// Adding bool to the string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(r#"''  +  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"''  + false"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' +  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' + false"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  +  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"""  + false"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" +  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" + false"#), Err(Validation("".into())));
        }

        /// Adding string should produce concatenated string
        #[test]
        fn str() {
          // single quotes
          assert_eq!(parse(r#"''  + '' "#), Ok(Str("".into())));
          assert_eq!(parse(r#"''  + 'a'"#), Ok(Str("a".into())));
          assert_eq!(parse(r#"'a' + '' "#), Ok(Str("a".into())));
          assert_eq!(parse(r#"'a' + 'b'"#), Ok(Str("ab".into())));

          // double quotes
          assert_eq!(parse(r#"""  + "" "#), Ok(Str("".into())));
          assert_eq!(parse(r#"""  + "a""#), Ok(Str("a".into())));
          assert_eq!(parse(r#""a" + "" "#), Ok(Str("a".into())));
          assert_eq!(parse(r#""a" + "b""#), Ok(Str("ab".into())));

          // mixed quotes - '' + ""
          assert_eq!(parse(r#"''  + "" "#), Ok(Str("".into())));
          assert_eq!(parse(r#"''  + "a""#), Ok(Str("a".into())));
          assert_eq!(parse(r#"'a' + "" "#), Ok(Str("a".into())));
          assert_eq!(parse(r#"'a' + "b""#), Ok(Str("ab".into())));

          // mixed quotes - "" - ''
          assert_eq!(parse(r#"""  + '' "#), Ok(Str("".into())));
          assert_eq!(parse(r#"""  + 'a'"#), Ok(Str("a".into())));
          assert_eq!(parse(r#""a" + '' "#), Ok(Str("a".into())));
          assert_eq!(parse(r#""a" + 'b'"#), Ok(Str("ab".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse(r#"''  + x"#), Ok(Attr(FieldName::valid("x").into())));
          assert_eq!(parse(r#"'a' + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));

          assert_eq!(parse(r#"""  + x"#), Ok(Attr(FieldName::valid("x").into())));
          assert_eq!(parse(r#""a" + x"#), Ok(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }
    }

    /// Checks that the `!=` operator behaves correctly
    mod eq {
      use super::*;
      use BinaryOp::Eq;

      /// Checks that compare to int behaves correctly
      mod int {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn int() {
          assert_eq!(parse(" 0 ==  0"), Ok(Bool(true)));
          assert_eq!(parse(" 0 == 42"), Ok(Bool(false)));
          assert_eq!(parse("42 ==  0"), Ok(Bool(false)));
          assert_eq!(parse("21 == 21"), Ok(Bool(true)));
        }

        #[test]
        fn float() {
          assert_eq!(parse(" 0 ==  0.0"), Ok(Bool(true)));
          assert_eq!(parse(" 0 == 42.0"), Ok(Bool(false)));
          assert_eq!(parse("42 ==  0.0"), Ok(Bool(false)));
          assert_eq!(parse("21 == 21.0"), Ok(Bool(true)));
        }

        /// Compare bool with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" 0 ==  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0 == false"), Err(Validation("".into())));
          assert_eq!(parse("42 ==  true"), Err(Validation("".into())));
          assert_eq!(parse("42 == false"), Err(Validation("".into())));
        }

        /// Compare string with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0 == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 == 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 == 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0 == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 == "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 == "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse("42 == x"), Ok(Binary {
            op: Eq,
            left:  Box::new(Int(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      mod float {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn int() {
          assert_eq!(parse(" 0.0 ==  0"), Ok(Bool(true)));
          assert_eq!(parse(" 0.0 == 42"), Ok(Bool(false)));
          assert_eq!(parse("42.0 ==  0"), Ok(Bool(false)));
          assert_eq!(parse("21.0 == 21"), Ok(Bool(true)));
        }

        #[test]
        fn float() {
          assert_eq!(parse(" 0.0 ==  0.0"), Ok(Bool(true)));
          assert_eq!(parse(" 0.0 == 42.0"), Ok(Bool(false)));
          assert_eq!(parse("42.0 ==  0.0"), Ok(Bool(false)));
          assert_eq!(parse("21.0 == 21.0"), Ok(Bool(true)));
        }

        /// Adding bool to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" 0.0 ==  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0.0 == false"), Err(Validation("".into())));
          assert_eq!(parse("42.0 ==  true"), Err(Validation("".into())));
          assert_eq!(parse("42.0 == false"), Err(Validation("".into())));
        }

        /// Adding string to the float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0.0 == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 == 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 == 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0.0 == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 == "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 == "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse(r#"42.0 == x"#), Ok(Binary {
            op: Eq,
            left:  Box::new(Float(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
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
        fn int() {
          assert_eq!(parse(" true == 42"), Err(Validation("".into())));
          assert_eq!(parse("false == 42"), Err(Validation("".into())));
        }

        /// Adding floating-point to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(" true == 42.0"), Err(Validation("".into())));
          assert_eq!(parse("false == 42.0"), Err(Validation("".into())));
        }

        #[test]
        fn bool() {
          assert_eq!(parse(" true ==  true"), Ok(Bool(true)));
          assert_eq!(parse(" true == false"), Ok(Bool(false)));
          assert_eq!(parse("false ==  true"), Ok(Bool(false)));
          assert_eq!(parse("false == false"), Ok(Bool(true)));
        }

        /// Adding string to the bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" true == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true == 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"false == '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false == 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" true == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true == "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"false == "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false == "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse("true == x"), Ok(Binary {
            op: Eq,
            left:  Box::new(Bool(true)),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
          assert_eq!(parse("false == x"), Ok(Binary {
            op: Eq,
            left:  Box::new(Bool(false)),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      mod str {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        #[ignore]//TODO: implement type checking
        fn int() {
          assert_eq!(parse(r#"''  == 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' == 42"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  == 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" == 42"#), Err(Validation("".into())));
        }

        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(r#"''  == 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' == 4.2"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  == 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" == 4.2"#), Err(Validation("".into())));
        }

        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(r#"''  ==  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"''  == false"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' ==  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' == false"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  ==  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"""  == false"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" ==  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" == false"#), Err(Validation("".into())));
        }

        #[test]
        fn str() {
          // single quotes
          assert_eq!(parse(r#"''  == '' "#), Ok(Bool(true)));
          assert_eq!(parse(r#"''  == 'a'"#), Ok(Bool(false)));
          assert_eq!(parse(r#"'a' == '' "#), Ok(Bool(false)));
          assert_eq!(parse(r#"'a' == 'b'"#), Ok(Bool(false)));

          // double quotes
          assert_eq!(parse(r#"""  == "" "#), Ok(Bool(true)));
          assert_eq!(parse(r#"""  == "a""#), Ok(Bool(false)));
          assert_eq!(parse(r#""a" == "" "#), Ok(Bool(false)));
          assert_eq!(parse(r#""a" == "b""#), Ok(Bool(false)));

          // mixed quotes - '' == ""
          assert_eq!(parse(r#"''  == "" "#), Ok(Bool(true)));
          assert_eq!(parse(r#"''  == "a""#), Ok(Bool(false)));
          assert_eq!(parse(r#"'a' == "" "#), Ok(Bool(false)));
          assert_eq!(parse(r#"'a' == "b""#), Ok(Bool(false)));

          // mixed quotes - "" == ''
          assert_eq!(parse(r#"""  == '' "#), Ok(Bool(true)));
          assert_eq!(parse(r#"""  == 'a'"#), Ok(Bool(false)));
          assert_eq!(parse(r#""a" == '' "#), Ok(Bool(false)));
          assert_eq!(parse(r#""a" == 'b'"#), Ok(Bool(false)));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse(r#"'a' == x"#), Ok(Binary {
            op: Eq,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));

          assert_eq!(parse(r#""a" == x"#), Ok(Binary {
            op: Eq,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }
    }

    /// Checks that the `!=` operator behaves correctly
    mod ne {
      use super::*;
      use BinaryOp::Ne;

      /// Checks that compare to int behaves correctly
      mod int {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn int() {
          assert_eq!(parse(" 0 !=  0"), Ok(Bool(false)));
          assert_eq!(parse(" 0 != 42"), Ok(Bool(true)));
          assert_eq!(parse("42 !=  0"), Ok(Bool(true)));
          assert_eq!(parse("21 != 21"), Ok(Bool(false)));
        }

        #[test]
        fn float() {
          assert_eq!(parse(" 0 !=  0.0"), Ok(Bool(false)));
          assert_eq!(parse(" 0 != 42.0"), Ok(Bool(true)));
          assert_eq!(parse("42 !=  0.0"), Ok(Bool(true)));
          assert_eq!(parse("21 != 21.0"), Ok(Bool(false)));
        }

        /// Compare bool with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" 0 !=  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0 != false"), Err(Validation("".into())));
          assert_eq!(parse("42 !=  true"), Err(Validation("".into())));
          assert_eq!(parse("42 != false"), Err(Validation("".into())));
        }

        /// Compare string with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0 != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 != 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 != 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0 != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0 != "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42 != "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse("42 != x"), Ok(Binary {
            op: Ne,
            left:  Box::new(Int(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      /// Checks that compare to int behaves correctly
      mod float {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn int() {
          assert_eq!(parse(" 0.0 !=  0"), Ok(Bool(false)));
          assert_eq!(parse(" 0.0 != 42"), Ok(Bool(true)));
          assert_eq!(parse("42.0 !=  0"), Ok(Bool(true)));
          assert_eq!(parse("21.0 != 21"), Ok(Bool(false)));
        }

        #[test]
        fn float() {
          assert_eq!(parse(" 0.0 !=  0.0"), Ok(Bool(false)));
          assert_eq!(parse(" 0.0 != 42.0"), Ok(Bool(true)));
          assert_eq!(parse("42.0 !=  0.0"), Ok(Bool(true)));
          assert_eq!(parse("21.0 != 21.0"), Ok(Bool(false)));
        }

        /// Compare bool with float should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(" 0.0 !=  true"), Err(Validation("".into())));
          assert_eq!(parse(" 0.0 != false"), Err(Validation("".into())));
          assert_eq!(parse("42.0 !=  true"), Err(Validation("".into())));
          assert_eq!(parse("42.0 != false"), Err(Validation("".into())));
        }

        /// Compare bool with string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" 0.0 != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 != 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 != 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" 0.0 != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" 0.0 != "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"42.0 != "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse(r#"42.0 != x"#), Ok(Binary {
            op: Ne,
            left:  Box::new(Float(42.into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      /// Checks that compare to bool behaves correctly
      mod bool {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Compare bool with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn int() {
          assert_eq!(parse(" true != 42"), Err(Validation("".into())));
          assert_eq!(parse("false != 42"), Err(Validation("".into())));
        }

        /// Compare bool with floating-point number should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(" true != 42.0"), Err(Validation("".into())));
          assert_eq!(parse("false != 42.0"), Err(Validation("".into())));
        }

        #[test]
        fn bool() {
          assert_eq!(parse(" true !=  true"), Ok(Bool(false)));
          assert_eq!(parse(" true != false"), Ok(Bool(true)));
          assert_eq!(parse("false !=  true"), Ok(Bool(true)));
          assert_eq!(parse("false != false"), Ok(Bool(false)));
        }

        /// Compare bool with string should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn str() {
          assert_eq!(parse(r#" true != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true != 'a'"#), Err(Validation("".into())));
          assert_eq!(parse(r#"false != '' "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false != 'a'"#), Err(Validation("".into())));

          assert_eq!(parse(r#" true != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#" true != "a""#), Err(Validation("".into())));
          assert_eq!(parse(r#"false != "" "#), Err(Validation("".into())));
          assert_eq!(parse(r#"false != "a""#), Err(Validation("".into())));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse("true != x"), Ok(Binary {
            op: Ne,
            left:  Box::new(Bool(true)),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));

          assert_eq!(parse("false != x"), Ok(Binary {
            op: Ne,
            left:  Box::new(Bool(false)),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }

      mod str {
        use super::*;
        use pretty_assertions::assert_eq;

        /// Compare string with int should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn int() {
          assert_eq!(parse(r#"''  != 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' != 42"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  != 42"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" != 42"#), Err(Validation("".into())));
        }

        /// Compare string with floating-point number should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn float() {
          assert_eq!(parse(r#"''  != 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' != 4.2"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  != 4.2"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" != 4.2"#), Err(Validation("".into())));
        }

        /// Compare string with bool should be an error
        #[test]
        #[ignore]//TODO: implement type checking
        fn bool() {
          assert_eq!(parse(r#"''  !=  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"''  != false"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' !=  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"'a' != false"#), Err(Validation("".into())));

          assert_eq!(parse(r#"""  !=  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#"""  != false"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" !=  true"#), Err(Validation("".into())));
          assert_eq!(parse(r#""a" != false"#), Err(Validation("".into())));
        }

        #[test]
        fn str() {
          // single quotes
          assert_eq!(parse(r#"''  != '' "#), Ok(Bool(false)));
          assert_eq!(parse(r#"''  != 'a'"#), Ok(Bool(true)));
          assert_eq!(parse(r#"'a' != '' "#), Ok(Bool(true)));
          assert_eq!(parse(r#"'a' != 'b'"#), Ok(Bool(true)));

          // double quotes
          assert_eq!(parse(r#"""  != "" "#), Ok(Bool(false)));
          assert_eq!(parse(r#"""  != "a""#), Ok(Bool(true)));
          assert_eq!(parse(r#""a" != "" "#), Ok(Bool(true)));
          assert_eq!(parse(r#""a" != "b""#), Ok(Bool(true)));

          // mixed quotes - '' != ""
          assert_eq!(parse(r#"''  != "" "#), Ok(Bool(false)));
          assert_eq!(parse(r#"''  != "a""#), Ok(Bool(true)));
          assert_eq!(parse(r#"'a' != "" "#), Ok(Bool(true)));
          assert_eq!(parse(r#"'a' != "b""#), Ok(Bool(true)));

          // mixed quotes - "" != ''
          assert_eq!(parse(r#"""  != '' "#), Ok(Bool(false)));
          assert_eq!(parse(r#"""  != 'a'"#), Ok(Bool(true)));
          assert_eq!(parse(r#""a" != '' "#), Ok(Bool(true)));
          assert_eq!(parse(r#""a" != 'b'"#), Ok(Bool(true)));
        }

        #[test]
        fn field() {//TODO: result depends on the type of field
          assert_eq!(parse(r#"'a' != x"#), Ok(Binary {
            op: Ne,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));

          assert_eq!(parse(r#""a" != x"#), Ok(Binary {
            op: Ne,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }));
        }
      }
    }

    /// Checks that folding constants in triplets behaves correctly
    mod triplets {
      use super::*;
      use pretty_assertions::assert_eq;
      use BinaryOp::Add;

      /// Tests folding of the integral numbers' constants
      #[test]
      fn int() {
        assert_eq!(parse("x + 1 + 2").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
        assert_eq!(parse("1 + x + 2").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
        assert_eq!(parse("1 + 2 + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });

        assert_eq!(parse("1 + 2 + 3 + x + 4 + 5 + 6").unwrap(), Binary {
          op: Add,
          left:  Box::new(Int(21.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
      }

      /// Tests folding of the floating-points' constants
      #[test]
      fn float() {
        assert_eq!(parse("x + 1.0 + 2.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
        assert_eq!(parse("1.0 + x + 2.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
        assert_eq!(parse("1.0 + 2.0 + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(3.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });

        assert_eq!(parse("1.0 + 2.0 + 3.0 + x + 4.0 + 5.0 + 6.0").unwrap(), Binary {
          op: Add,
          left:  Box::new(Float(21.into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });
      }

      /// Tests folding of the string constants
      #[test]
      fn str() {
        assert_eq!(parse("x + 'a' + 'b'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Attr(FieldName::valid("x").into())),
          right: Box::new(Str("ab".into())),
        });
        assert_eq!(parse("'a' + x + 'b'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Binary {
            op: Add,
            left:  Box::new(Str("a".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }),
          right: Box::new(Str("b".into())),
        });
        assert_eq!(parse("'a' + 'b' + x").unwrap(), Binary {
          op: Add,
          left:  Box::new(Str("ab".into())),
          right: Box::new(Attr(FieldName::valid("x").into())),
        });

        assert_eq!(parse("'a' + 'b' + 'c' + x + 'd' + 'e' + 'f'").unwrap(), Binary {
          op: Add,
          left:  Box::new(Binary {
            op: Add,
            left:  Box::new(Str("abc".into())),
            right: Box::new(Attr(FieldName::valid("x").into())),
          }),
          right: Box::new(Str("def".into())),
        });
      }
    }
  }

  #[test]
  fn branch() {
    assert_eq!(parse("true  ? a : b"), Ok(Attr(FieldName::valid("a").into())));
    assert_eq!(parse("false ? a : b"), Ok(Attr(FieldName::valid("b").into())));
    assert_eq!(parse("condition ? a : b"), Ok(Branch {
      condition: Box::new(Attr(FieldName::valid("condition").into())),
      if_true:   Box::new(Attr(FieldName::valid("a").into())),
      if_false:  Box::new(Attr(FieldName::valid("b").into())),
    }));
  }

  #[test]
  #[ignore]
  fn index() {//TODO: Index validation
    assert_eq!(parse("[3, 1, 4][-1]"), Ok(Int(4.into())));
    assert_eq!(parse("[3, 1, 4][ 2]"), Ok(Int(4.into())));
    assert_eq!(parse("[3, 1, x][ 2]"), Ok(Attr(FieldName::valid("x").into())));
    assert_eq!(parse("[3, 1, 4][ x]"), Ok(Index {
      expr:  Box::new(List(vec![
        Int(3.into()),
        Int(1.into()),
        Int(4.into()),
      ])),
      index: Box::new(Attr(FieldName::valid("x").into())),
    }));

    assert_eq!(parse("[3, 1, 4][ 3]"), Err(Validation("".into())));
  }
}
