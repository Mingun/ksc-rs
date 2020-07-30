//! Contains errors that can occurs when creating kaitai struct model

use std::borrow::Cow;
use std::fmt::{Display, Formatter, Result};
use std::error::Error;

use peg::error::ParseError;
use peg::str::LineCol;

/// Possible errors when creating kaitai struct model from YAML representation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelError {
  /// Parser error of incorrect expression in field
  Expression(ParseError<LineCol>),//TODO: Add information about field
  /// Error of validating schema rules, such as absence of mandatory fields or
  /// excess fields.
  Validation(Cow<'static, str>),
}
impl From<ParseError<LineCol>> for ModelError {
  fn from(error: ParseError<LineCol>) -> Self { Self::Expression(error) }
}

impl Display for ModelError {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result {
    use ModelError::*;

    match self {
      Expression(err) => write!(f, "incorrect expression: {}", err),
      Validation(err) => write!(f, "invalid schema: {}", err),
    }
  }
}

impl Error for ModelError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    use ModelError::*;

    match self {
      Expression(err) => Some(err),
      Validation(_) => None,
    }
  }
}
