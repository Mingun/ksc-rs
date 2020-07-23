//! Contains kaitai struct model, used by compiler to generate code.
//! Unlike structures from [`parser`] module that module contains validated
//! structures, that represent only valid constructs of kaitai struct language.
//!
//! [`parser`]: ./parser/index.html

use std::convert::{TryFrom, TryInto};

use crate::error::ModelError;
use crate::expressions::OwningNode;
use crate::expressions::parser::parse_single;
use crate::parser as p;

/// Expression, that used in boolean contexts.
///
/// Contains AST of expression language, that evaluated to boolean expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Condition(OwningNode);
impl TryFrom<p::Condition> for Condition {
  type Error = ModelError;

  fn try_from(data: p::Condition) -> Result<Self, Self::Error> {
    Ok(match data {
      p::Condition::Expr(expr)   => Self(parse_single(&expr)?.into()),
      p::Condition::Value(value) => Self(OwningNode::Bool(value)),
    })
  }
}

macro_rules! usize_expr {
  ($(#[$meta:meta])* $from:ty => $to:ident) => {
    $(#[$meta])*
    #[derive(Clone, Debug, PartialEq)]
    pub struct $to(OwningNode);
    impl TryFrom<$from> for $to {
      type Error = ModelError;

      fn try_from(data: $from) -> Result<Self, Self::Error> {
        Ok(match data {
          p::Expression::Expr(expr)   => Self(parse_single(&expr)?.into()),
          p::Expression::Value(value) => Self(OwningNode::Int(value)),
        })
      }
    }
  };
}

usize_expr!(
  /// Expression used to represent repetition count.
  ///
  /// Contains AST of expression language, that evaluated to integer expression.
  p::Count => Count
);

usize_expr!(
  /// Expression used to represent instance position.
  ///
  /// Contains AST of expression language, that evaluated to integer expression.
  p::Position => Position
);

/// Defines way of reading attribute in a structure.
#[derive(Clone, Debug, PartialEq)]
pub enum Repeat {
  /// Attribute not repeated
  None,
  /// Specify, that attribute repeated until end-of-stream of current type will
  /// be reached.
  Eos,
  /// Specify number of repetitions for repeated attribute.
  Count(Count),
  /// Specifies a condition to be checked **after** each parsed item, repeating
  /// while the expression is `false`.
  Until(Condition),
}
impl TryFrom<(Option<p::Repeat>, Option<p::Count>, Option<p::Condition>)> for Repeat {
  type Error = ModelError;

  fn try_from(data: (Option<p::Repeat>, Option<p::Count>, Option<p::Condition>)) -> Result<Self, Self::Error> {
    use p::Repeat::*;
    use ModelError::*;

    match (data.0, data.1, data.2) {
      (None,        None,        None) => Ok(Self::None),
      (Some(Eos),   None,        None) => Ok(Self::Eos),
      (Some(Expr),  Some(count), None) => Ok(Self::Count(count.try_into()?)),
      (Some(Until), None, Some(until)) => Ok(Self::Until(until.try_into()?)),

      // (None, Some(count), None) => Ok(Self::Count(count.try_into()?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776
      // (None, None, Some(until)) => Ok(Self::Until(until.try_into()?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776

      (None, Some(_), None) => Err(Validation("missed `repeat: expr`")),
      (None, None, Some(_)) => Err(Validation("missed `repeat: until`")),

      (Some(Expr), None,  _) => Err(Validation("missed `repeat-expr`")),
      (Some(Until), _, None) => Err(Validation("missed `repeat-until`")),

      (_, Some(_), Some(_)) => Err(Validation("either `repeat-expr` or `repeat-until` must be specified")),
      (Some(_), _, Some(_)) => Err(Validation("`repeat-until` requires `repeat: until`")),
      (Some(_), Some(_), _) => Err(Validation("`repeat-expr` requires `repeat: expr`")),
    }
  }
}
