use std::ops::{Deref, DerefMut};

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use serde_yml::Value;

use crate::parser::{Doc, Identifier, Name, OneOrMany, Scalar, UserName};

/// Represents one enumerated value, `value` in:
///
/// ```yaml
/// enums:
///   enum_name:
///     1: value
/// ```
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case", untagged)]
pub enum EnumValue {
  /// Symbolic alias for numeric constant.
  Name(Name),
  /// Boolean alias for numeric constant.
  Bool(bool),
  /// Definition of value with additional meta-information.
  Desc {
    /// Symbolic or boolean alias for numeric constant.
    id: Identifier,
    /// Documentation for constant.
    #[serde(flatten)]
    doc: Doc,

    /// Original constant identifier(s) in the format specification.
    /// Uses, if that identifier can't be expressed in the `id` field.
    ///
    /// Not used by the compiler.
    #[serde(rename = "-orig-id")]
    #[serde(skip_serializing_if = "Option::is_none")]
    orig_id: Option<OneOrMany<String>>,

    /// Additional arbitrary values.
    #[serde(flatten)]
    other: IndexMap<UserName, Value>,
  },
}

/// Enumeration definition
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(transparent)]
pub struct Enum(pub IndexMap<Scalar, EnumValue>);
impl Deref for Enum {
  type Target = IndexMap<Scalar, EnumValue>;

  fn deref(&self) -> &Self::Target { &self.0 }
}
impl DerefMut for Enum {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}
