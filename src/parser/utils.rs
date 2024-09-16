//! Auxiliary commonly used things

use std::fmt::{Display, Formatter, Result};
use std::hash::{Hash, Hasher};
use std::mem;

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use serde_yml::{Number, Value};

/// Generic wrapper that allow one or more occurrences of specified type.
///
/// In YAML it will presented or as a value, or as an array:
/// ```yaml
/// one: just a string
/// many:
///   - 1st string
///   - 2nd string
/// ```
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum OneOrMany<T> {
  /// Single value
  One(T),
  /// Array of values
  Vec(Vec<T>),
}
impl<T> From<OneOrMany<T>> for Vec<T> {
  fn from(from: OneOrMany<T>) -> Self {
    match from {
      OneOrMany::One(val) => vec![val],
      OneOrMany::Vec(vec) => vec,
    }
  }
}

/// Generic variant wrapper, that allow or fixed value, or describe a set
/// of possible choices selected based on some expression.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Variant<T> {
  /// Statically specified value.
  Fixed(T),
  /// Dynamically calculated value based on some expression.
  #[serde(rename_all = "kebab-case")]
  Choice {
    /// Expression which determines what variant will be used
    switch_on: Scalar,
    /// Variants
    cases: IndexMap<Scalar, T>,
  },
}

/// Generic expression, that used in `T` type contexts.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Expression<T> {
  /// Statically determined value.
  Value(T),
  /// Expression, that should evaluate to `T` value.
  Expr(String),
}

/// Represents any valid scalar YAML value.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, PartialOrd)]
#[serde(rename_all = "kebab-case", untagged)]
pub enum Scalar {
  /// Represents a YAML null value.
  Null,
  /// Represents a YAML boolean.
  Bool(bool),
  /// Represents a YAML numerical value, whether integer or floating point.
  Number(Number),
  /// Represents a YAML string.
  String(String),
}
impl Eq for Scalar {}
impl From<Scalar> for Value {
  fn from(scalar: Scalar) -> Self {
    match scalar {
      Scalar::Null      => Self::Null,
      Scalar::Bool(b)   => Self::Bool(b),
      Scalar::Number(i) => Self::Number(i),
      Scalar::String(s) => Self::String(s),
    }
  }
}
/// Implementation of hash is the same as for `serde_yml::Value`.
impl Hash for Scalar {
  fn hash<H: Hasher>(&self, state: &mut H) {
    mem::discriminant(self).hash(state);
    match self {
      Self::Null      => {}
      Self::Bool(b)   => b.hash(state),
      Self::Number(i) => i.hash(state),
      Self::String(s) => s.hash(state),
    }
  }
}
impl Display for Scalar {
  fn fmt(&self, f: &mut Formatter) -> Result {
    match self {
      Self::Null      => write!(f, "(null)"),
      Self::Bool(b)   => b.fmt(f),
      Self::Number(i) => i.fmt(f),
      Self::String(s) => write!(f, r#""{}""#, s.replace('"', r#"\""#)),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod scalar {
  use super::*;
  use pretty_assertions::assert_eq;
  use std::hash::DefaultHasher;

  /// Checks that hash implementation of the `Scalar` is the same as implementation
  /// for `Value`
  #[test]
  fn hash() {
    macro_rules! assert_hash {
      ($scalar:expr) => {
        let mut hash1 = DefaultHasher::new();
        let mut hash2 = DefaultHasher::new();

        let scalar = $scalar;
        let value = Value::from(scalar.clone());

        scalar.hash(&mut hash1);
        value.hash(&mut hash2);

        assert_eq!(hash1.finish(), hash2.finish());
      };
    }

    assert_hash!(Scalar::Null);
    assert_hash!(Scalar::Number(42.into()));
    assert_hash!(Scalar::Number(4.2.into())); // 4.2 can be only approximately represented in binary form
    assert_hash!(Scalar::Number(4.5.into())); // 4.5 can be exactly represented in binary form
    assert_hash!(Scalar::String("(nu\"ll)".into()));
  }

  #[test]
  fn display() {
    assert_eq!(format!("{}", Scalar::Null),                      "(null)");
    assert_eq!(format!("{}", Scalar::Bool(true)),                "true");
    assert_eq!(format!("{}", Scalar::Number(42.into())),         "42");
    assert_eq!(format!("{}", Scalar::Number(4.2.into())),        "4.2");
    assert_eq!(format!("{}", Scalar::String("(nu\"ll)".into())), r#""(nu\"ll)""#);
  }
}
