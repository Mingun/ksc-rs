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
