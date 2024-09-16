use serde::{Deserialize, Serialize};
use std::hash::Hash;

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
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct Name(pub String);

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

/// Identifier, used for:
///
/// - name of KSY file
/// - enumeration value
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Identifier {
  /// Identifier represented as a string.
  Name(Name),
  /// Identifier, represented as a boolean constant in YAML, ie. `true` or `false`.
  ///
  /// When that type is used in format name or parameter name, processed as a symbolic
  /// name; this is done for convenience of writing such name -- it does not need to be
  /// enclosed in quotation marks so that the YAML parser recognizes it as a string.
  ///
  /// In enumeration values processed as corresponding logical constant.
  Bool(bool),
}

////////////////////////////////////////////////////////////////////////////////////////////////////

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
