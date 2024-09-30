use std::fmt;
use std::hash::Hash;

use serde::de::{Deserializer, Error, Visitor};
use serde::{Deserialize, Serialize};

/// Type for representing names of:
///
/// - [enumerations](crate::parser::Enum)
/// - [enumeration values](crate::parser::EnumValue)
/// - [types](crate::parser::TypeSpec)
/// - [instances](crate::parser::Instance)
/// - [attributes](crate::parser::Attribute)
/// - [parameters](crate::parser::Param)
/// - [KSY file](crate::parser::Ksy)
///
/// Pattern: `^[a-z][a-z0-9_]*$`.
#[derive(Clone, Debug, Default, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct Name(pub String);
impl<'de> Deserialize<'de> for Name {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct NameVisitor;
    impl<'de> Visitor<'de> for NameVisitor {
      type Value = Name;

      fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a string or a bool")
      }

      fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(Name(v.to_string()))
      }

      fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(Name(v))
      }

      fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(Name(v.to_string()))
      }
      // Numbers are not allowed, because +123 we can convert only to "123".
      // Although they are forbidden in names, we would like to parse them anyway to be able
      // to report as many errors as possible, but with the current approach numeric input
      // in import will prevent us from parsing the rest
    }
    deserializer.deserialize_any(NameVisitor)
  }
}

/// Path to enum name, used to describe `enum` in attributes and parameters.
///
/// Pattern: `^([a-z][a-z0-9_]*::)*[a-z][a-z0-9_]*$`.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(from = "&str", into = "String")]
pub struct Path(pub Vec<Name>);
impl<'a> From<&'a str> for Path {
  fn from(path: &'a str) -> Self {
    Self(path.split("::").map(|s| Name(s.to_owned())).collect())
  }
}
impl From<Path> for String {
  fn from(path: Path) -> Self {
    let mut string = String::new();
    let mut iter = path.0.into_iter();

    if let Some(first) = iter.next() {
      string.push_str(&first.0);
      for s in iter {
        string.push_str("::");
        string.push_str(&s.0);
      }
    }

    string
  }
}

/// Name of user-defined attribute in:
///
/// - [meta](crate::parser::MetaSpec)
/// - [attribute](crate::parser::Attribute)
/// - [parameter](crate::parser::Param)
/// - [type](crate::parser::TypeSpec)
///
/// User-defined attributes can contains any data and completely ignored by compiler.
///
/// Pattern: `^-.*$`.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct UserName(pub String);

/// Algorithm for process byte stream before run actual parsing code.
///
/// Pattern: `^zlib|(xor|rol|ror)\(.*\)$`.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct ProcessAlgo(pub String);

/// Relative or absolute path to another `.ksy` file to import
/// (**without** the `.ksy` extension).
///
/// Pattern: `^(.*/)?[a-z][a-z0-9_]*$`.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct Import(pub Name);

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod name {
  use super::*;

  #[test]
  fn str() {
    let name: Name = serde_yml::from_str("string").unwrap();
    assert_eq!(name.0, "string");
  }

  #[test]
  fn int() {
    // Currently YAML parser will interpret input and try to guess numbers and booleans in the strings
    // TODO: if https://github.com/acatton/serde-yaml-ng/issues/13 will be implemented,
    // switch to serde-yaml-ng and enable failsafe schema
    serde_yml::from_str::<Name>("123").unwrap_err();
    serde_yml::from_str::<Name>("-456").unwrap_err();
    serde_yml::from_str::<Name>("+789").unwrap_err();
  }

  #[test]
  fn float() {
    // Currently YAML parser will interpret input and try to guess numbers and booleans in the strings
    // TODO: if https://github.com/acatton/serde-yaml-ng/issues/13 will be implemented,
    // switch to serde-yaml-ng and enable failsafe schema
    serde_yml::from_str::<Name>("1.23").unwrap_err();
    serde_yml::from_str::<Name>("-4.56").unwrap_err();
    serde_yml::from_str::<Name>("+7.89").unwrap_err();
  }

  #[test]
  fn bool() {
    let name: Name = serde_yml::from_str("true").unwrap();
    assert_eq!(name.0, "true");

    let name: Name = serde_yml::from_str("false").unwrap();
    assert_eq!(name.0, "false");
  }
}

#[test]
fn path() {
  use pretty_assertions::assert_eq;

  let single: Path = "one".into();
  assert_eq!(single, Path(vec![Name("one".to_owned())]));
  assert_eq!(String::from(single), "one");

  let many: Path = "some::path".into();
  assert_eq!(many, Path(vec![
    Name("some".to_owned()),
    Name("path".to_owned()),
  ]));
  assert_eq!(String::from(many), "some::path");
}
