//! Validated AST of expressions from a [parser] module.
//!
//! [parser]: ../parser/expressions/index.html

use std::convert::TryFrom;

use ordered_float::OrderedFloat;
use serde_yaml::Number;

use crate::error::ModelError;
use crate::model::{FieldName, EnumName, EnumValueName, TypeName as TName};
use crate::parser::Scalar;
use crate::parser::expressions::{BinaryOp, Node, Scope, SpecialName, TypeName, TypeRef, UnaryOp};
use crate::parser::expressions::parser::parse_single;

/// Owning counterpart of an AST [`Node`].
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
    use Node::*;

    match reference {
      Str(val)  => Self::Str(val),
      Int(val)  => Self::Int(val),
      Float(val)=> Self::Float(val),
      Bool(val) => Self::Bool(val),

      //TODO: Name already contains only valid symbols, but need to check that it is really exists
      Attr(val) => Self::Attr(FieldName::valid(val)),
      SpecialName(val) => Self::SpecialName(val),
      //TODO: Names already contains only valid symbols, but need to check that they is really exists
      EnumValue { scope, name, value } => Self::EnumValue {
        scope: scope.into(),
        name:  EnumName::valid(name),
        value: EnumValueName::valid(value),
      },

      List(val) => Self::List(Self::validate_all(val)),

      SizeOf { type_, bit } => Self::SizeOf { type_: type_.into(), bit },

      Call { callee, args } => Self::Call {
        callee: Box::new((*callee).into()),
        args: Self::validate_all(args),
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
        //TODO: Name already contains only valid symbols, but need to check that it is really exists
        attr: FieldName::valid(attr),
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
      String(val) => Ok(Self::parse(&val)?),
    }
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
  // Colorful diffs in assertions
  use pretty_assertions::assert_eq;
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
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
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
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
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
    assert_eq!(OwningNode::try_from(Scalar::String("id".into())), Ok(OwningNode::Attr(FieldName::valid("id"))));
    assert_eq!(OwningNode::try_from(Scalar::String("1 + 2".into())), Ok(OwningNode::Binary {
      op: BinaryOp::Add,
      left:  Box::new(OwningNode::Int(1)),
      right: Box::new(OwningNode::Int(2)),
    }));
  }
}
