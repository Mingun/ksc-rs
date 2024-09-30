use std::fmt;

use indexmap::IndexMap;
use serde::de::value::MapAccessDeserializer;
use serde::de::{Deserializer, Error, MapAccess, Visitor};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};
use serde_yml::{Number, Value};

use crate::parser::{Doc, Name, OneOrMany, Scalar, UserName};

/// Detailed information about enum variant
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct EnumVariant {
  /// Symbolic or boolean alias for numeric constant.
  pub id: Name,
  /// Documentation for constant.
  #[serde(flatten)]
  pub doc: Doc,

  /// Original constant identifier(s) in the format specification.
  /// Uses, if that identifier can't be expressed in the `id` field.
  ///
  /// Not used by the compiler.
  #[serde(rename = "-orig-id")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub orig_id: Option<OneOrMany<String>>,

  /// Additional arbitrary values.
  #[serde(flatten)]
  pub other: IndexMap<UserName, Value>,
}

/// Represents one enumerated value, `value` in:
///
/// ```yaml
/// enums:
///   enum_name:
///     1: value
/// ```
#[derive(Clone, Debug, PartialEq)]
pub enum EnumValue {
  /// Symbolic alias for numeric constant.
  Name(Name),
  /// Definition of value with additional meta-information.
  Full(EnumVariant),
}
impl<'de> Deserialize<'de> for EnumValue {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct ValueVisitor;
    impl<'de> Visitor<'de> for ValueVisitor {
      type Value = EnumValue;

      fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a string or a map")
      }

      fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v)))
      }

      fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      // Other signed numbers delegates to i64
      fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      // Other unsigned numbers delegates to u64
      fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(EnumValue::Name(Name(v.to_string())))
      }

      fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
      where
        A: MapAccess<'de>,
      {
        EnumVariant::deserialize(MapAccessDeserializer::new(map)).map(EnumValue::Full)
      }
    }
    deserializer.deserialize_any(ValueVisitor)
  }
}
impl Serialize for EnumValue {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    match self {
      EnumValue::Name(name) => {
        // If name looks like boolean or number, serialize it without quotes because we want
        // identifier and `true` and `false` a valid identifiers in kaitai struct.
        // Apply the same rules for numbers for consistency although they are not valid identifiers.
        if let Ok(b) = name.0.parse::<bool>() {
          return b.serialize(serializer);
        }
        if let Ok(n) = name.0.parse::<Number>() {
          return n.serialize(serializer);
        }
        name.serialize(serializer)
      },
      EnumValue::Full(info) => info.serialize(serializer),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Enumeration definition. Map stored as vector of key-value pairs to be able to be checked for
/// duplicates on validation phase.
///
/// This type in the serialized form represented as a map.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Enum(pub Vec<(Scalar, EnumValue)>);
impl<'de> Deserialize<'de> for Enum {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct MapVisitor;
    impl<'de> Visitor<'de> for MapVisitor {
      type Value = Enum;

      fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a map")
      }

      fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
      where
        A: MapAccess<'de>,
      {
        let mut result = Vec::with_capacity(map.size_hint().unwrap_or(0));
        while let Some(entry) = map.next_entry()? {
          result.push(entry);
        }
        Ok(Enum(result))
      }
    }
    deserializer.deserialize_map(MapVisitor)
  }
}
impl Serialize for Enum {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    let mut iter = self.0.iter();
    let mut map = serializer.serialize_map(Some(self.0.len()))?;
    iter.try_for_each(|(key, value)| map.serialize_entry(&key, &value))?;
    map.end()
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Checks that duplicates are available in parsed model
#[test]
fn duplicates() {
  use pretty_assertions::assert_eq;

  let ksy: Enum = serde_yml::from_str("
    1: one
    2: two
    1: dup
    true: true
    true: false
    false: false
    false: true
    str: 1
    str: 2
    null: 1
    null: 2
  ").unwrap();

  assert_eq!(ksy, Enum(vec![
    (Scalar::Number(1.into()), EnumValue::Name(Name("one".into()))),
    (Scalar::Number(2.into()), EnumValue::Name(Name("two".into()))),
    (Scalar::Number(1.into()), EnumValue::Name(Name("dup".into()))),
    (Scalar::Bool(true), EnumValue::Name(Name("true".into()))),
    (Scalar::Bool(true), EnumValue::Name(Name("false".into()))),
    (Scalar::Bool(false), EnumValue::Name(Name("false".into()))),
    (Scalar::Bool(false), EnumValue::Name(Name("true".into()))),
    (Scalar::String("str".into()), EnumValue::Name(Name("1".into()))),
    (Scalar::String("str".into()), EnumValue::Name(Name("2".into()))),
    (Scalar::Null, EnumValue::Name(Name("1".into()))),
    (Scalar::Null, EnumValue::Name(Name("2".into()))),
  ]));
}

#[cfg(test)]
mod ser {
  use super::*;
  use pretty_assertions::assert_eq;

  #[test]
  fn numbers() {
    let data = Enum(vec![
      (Scalar::Number(1.into()), EnumValue::Name(Name("one".into()))),
      (Scalar::Number(2.into()), EnumValue::Name(Name("two".into()))),
      (Scalar::Number(1.into()), EnumValue::Name(Name("dup".into()))),
    ]);

    assert_eq!(serde_yml::to_string(&data).unwrap(), "\
      1: one\n\
      2: two\n\
      1: dup\n\
    ");
  }

  #[test]
  fn booleans() {
    let data = Enum(vec![
      (Scalar::Bool(true), EnumValue::Name(Name("true".into()))),
      (Scalar::Bool(true), EnumValue::Name(Name("false".into()))),
      (Scalar::Bool(false), EnumValue::Name(Name("true".into()))),
      (Scalar::Bool(false), EnumValue::Name(Name("false".into()))),
    ]);

    assert_eq!(serde_yml::to_string(&data).unwrap(), "\
      true: true\n\
      true: false\n\
      false: true\n\
      false: false\n\
    ");
  }

  #[test]
  fn strings() {
    let data = Enum(vec![
      (Scalar::String("str".into()), EnumValue::Name(Name("1".into()))),
      (Scalar::String("str".into()), EnumValue::Name(Name("2".into()))),
    ]);

    assert_eq!(serde_yml::to_string(&data).unwrap(), "\
      str: 1\n\
      str: 2\n\
    ");
  }

  #[test]
  fn nulls() {
    let data = Enum(vec![
      (Scalar::Null, EnumValue::Name(Name("1".into()))),
      (Scalar::Null, EnumValue::Name(Name("2".into()))),
    ]);

    assert_eq!(serde_yml::to_string(&data).unwrap(), "\
      null: 1\n\
      null: 2\n\
    ");
  }
}
