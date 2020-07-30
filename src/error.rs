//! Contains errors that can occurs when creating kaitai struct model

use std::borrow::Cow;
use std::convert::{Infallible, TryInto};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

use peg::error::ParseError;
use peg::str::LineCol;

/// Path to attribute in YAML
#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct YamlPath(Vec<String>);
impl YamlPath {
  pub fn extend<I: IntoIterator>(&self, segments: I) -> Self
    where I::Item: Into<String>,
  {
    let mut path = self.0.clone();
    path.extend(segments.into_iter().map(Into::into));
    Self(path)
  }
  pub fn validate<T, R>(self, value: T) -> Result<R, ModelError>
    where T: TryInto<R, Error = Cow<'static, str>>
  {
    value.try_into().map_err(|e| ModelError::Validation(self, e))
  }
}
impl Display for YamlPath {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
    for segment in &self.0 {
      write!(fmt, "/{}", segment)?;
    }
    Ok(())
  }
}

pub type ValidationError = Cow<'static, str>;

/// Possible errors when creating kaitai struct model from YAML representation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelError {
  /// Parser error of incorrect expression in field
  Expression(ParseError<LineCol>),//TODO: Add information about field
  /// Error of validating schema rules, such as absence of mandatory fields or
  /// excess fields.
  Validation(YamlPath, ValidationError),
}
impl From<ParseError<LineCol>> for ModelError {
  fn from(error: ParseError<LineCol>) -> Self { Self::Expression(error) }
}
/// Allow to use any `Into` conversions in contexts where required `TryInto<Error=ModelError>`
impl From<Infallible> for ModelError {
  fn from(_error: Infallible) -> Self { unreachable!() }
}

impl Display for ModelError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    use ModelError::*;

    match self {
      Expression(err) => write!(f, "incorrect expression: {}", err),
      Validation(path, err) => write!(f, "{}: invalid schema: {}", path, err),
    }
  }
}

impl Error for ModelError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    use ModelError::*;

    match self {
      Expression(err) => Some(err),
      Validation(..) => None,
    }
  }
}
