//! Contains model of enumerations used by code generator.

use std::collections::HashSet;
use std::ops::Deref;

use indexmap::map::Entry;
use indexmap::IndexMap;

use crate::error::ModelError;
use crate::error::ModelError::Validation;
use crate::model::EnumValueName;
use crate::parser as p;

/// Enumeration definition. Contains a map of enumerated values in order of their
/// definition in the KSY.
///
/// To get a list of enumerated values `Enum` can be coerced to `IndexMap<i64, EnumVariant>`.
#[derive(Clone, Debug, PartialEq)]
pub struct Enum(IndexMap<i64, EnumVariant>);
impl Enum {
  /// Creates definition of enumeration by validating a data structure from a [`parser`] module.
  ///
  /// [`parser`]: crate::parser
  pub fn validate(spec: &p::Enum) -> Result<Self, ModelError> {
    let iter = spec.0.iter();
    let cap = iter.size_hint().1.unwrap_or(0);
    let mut result = IndexMap::with_capacity(cap);
    let mut names = HashSet::with_capacity(cap);

    for (k, v) in iter {
      let k = Self::validate_key(k)?;
      let v = EnumVariant::validate(&v)?;

      if !names.insert(v.name.clone()) {
        return Err(Validation(format!("name `{}` was previously defined", v.name).into()));
      }

      match result.entry(k) {
        Entry::Vacant(e) => e.insert(v),
        Entry::Occupied(e) => return Err(Validation(format!(
          "value `{}` was previously defined",
          e.key()).into(),
        )),
      };
    }
    Ok(Self(result))
  }

  fn validate_key(key: &p::Scalar) -> Result<i64, ModelError> {
    match key {
      p::Scalar::Null => Err(Validation(format!(
        "expected integral constant in range [{}, {}], found null",
        i64::MIN, i64::MAX,
      ).into())),
      p::Scalar::Bool(b) => Err(Validation(format!(
        "expected integral constant in range [{}, {}], found boolean `{}`",
        i64::MIN, i64::MAX, b,
      ).into())),
      p::Scalar::Number(n) => match n.as_i64() {
        Some(int) => Ok(int),
        None => Err(Validation(format!(
          "expected integral constant in range [{}, {}], found number `{}`",
          i64::MIN, i64::MAX, n,
        ).into())),
      },
      // NOTE: Original compiler uses YAML 1.1. In YAML 1.2 underscores in numbers was removed.
      // serde_yml implements YAML 1.2, numbers with underscores will be reported as strings.
      // See https://yaml.org/spec/1.2.2/ext/changes/#changes-in-version-12-revision-120-2009-07-21
      //
      // Also original compiler additionally parses string content that matched the following
      // regexps:
      // - ^(-?[0-9]+)$
      // - ^0x([0-9a-fA-F]+)$
      // The intention was to accept JS objects that represents result of YAML parsing.
      // Because in JS object keys can only be strings, numeric values implicitly converted
      // to strings corresponding to the first RegExp. It is unknown why the hexadecimal
      // RegExp even exists.
      // Anyway, new modern YAML libraries should use Map to represent mappings
      // which can use numeric keys and that special handling could be removed from
      // original compiler. We consider its behavior as bug and do not replicate it here.
      // See https://github.com/kaitai-io/kaitai_struct/issues/1132
      p::Scalar::String(s) => Err(Validation(format!(
        "expected integral constant in range [{}, {}], found string `{}`",
        i64::MIN, i64::MAX, s,
      ).into())),
    }
  }
}
impl Deref for Enum {
  type Target = IndexMap<i64, EnumVariant>;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

/// Enumeration variant definition. Contains a name and any additional information
/// about individual variant of an enumeration.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumVariant {
  /// Name of the enumeration variant
  pub name: EnumValueName,
}
impl EnumVariant {
  /// Creates definition of enumeration by validating a data structure from a [`parser`] module.
  ///
  /// [`parser`]: crate::parser
  pub fn validate(value: &p::EnumValue) -> Result<Self, ModelError> {
    let name = match value {
      p::EnumValue::Name(name) => EnumValueName::validate(name)?,
      p::EnumValue::Full(info) => EnumValueName::validate(&info.id)?,
    };
    Ok(Self { name })
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// NOTE: Original compiler uses YAML 1.1. In YAML 1.2 underscores in numbers was [removed].
///
/// [removed]: https://yaml.org/spec/1.2.2/ext/changes/#changes-in-version-12-revision-120-2009-07-21
#[cfg(test)]
mod tests {
  use super::*;
  use indexmap::indexmap;
  use pretty_assertions::assert_eq;

  /// Creates a new validated variant for tests
  fn variant(name: &str) -> EnumVariant {
    EnumVariant {
      name: EnumValueName::valid(name),
    }
  }

  #[test]
  fn dec() {
    let ksy: p::Enum = serde_yml::from_str("
      1: true
      2: false
      3: name
    ").unwrap();

    assert_eq!(
      Enum::validate(&ksy),
      Ok(Enum(indexmap![
        1 => variant("true"),
        2 => variant("false"),
        3 => variant("name"),
      ])),
    );
  }

  #[test]
  fn hex() {
    let ksy: p::Enum = serde_yml::from_str("
      0x1: true
      0x2: false
      0x3: name
    ").unwrap();

    assert_eq!(
      Enum::validate(&ksy),
      Ok(Enum(indexmap![
        0x1 => variant("true"),
        0x2 => variant("false"),
        0x3 => variant("name"),
      ])),
    );
  }

  #[test]
  fn duplicated_names() {
    let ksy: p::Enum = serde_yml::from_str("
      1: one
      2: one
    ").unwrap();

    assert_eq!(
      Enum::validate(&ksy),
      Err(Validation("name `one` was previously defined".into())),
    );
  }

  /// Checks that mapping the same values to the different names is an error,
  /// even when values literally does not the same, for example `11` and `1_1`.
  mod duplicated_values {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn dec() {
      let ksy: p::Enum = serde_yml::from_str("
        1: one
        1: two
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("value `1` was previously defined".into())),
      );
    }

    #[test]
    fn oct() {
      let ksy: p::Enum = serde_yml::from_str("
        0o1: one
        0o1: two
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("value `1` was previously defined".into())),
      );
    }

    #[test]
    fn hex() {
      let ksy: p::Enum = serde_yml::from_str("
        0x1: one
        0x1: two
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("value `1` was previously defined".into())),
      );
    }

    #[test]
    fn dec_hex() {
      let ksy: p::Enum = serde_yml::from_str("
        1: one
        0x1: two
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("value `1` was previously defined".into())),
      );
    }

    #[test]
    fn underscores() {
      let ksy: p::Enum = serde_yml::from_str("
        11: one
        1_1: two
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found string `1_1`".into())),
      );
    }
  }

  mod min {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn dec() {
      let ksy: p::Enum = serde_yml::from_str(&format!("
        {}: one
      ", i64::MIN)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Ok(Enum(indexmap![i64::MIN => variant("one")])),
      );
    }

    #[test]
    fn hex() {
      let ksy: p::Enum = serde_yml::from_str(&dbg!(format!("
        -{:#x}: one
      ", i64::MIN))).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Ok(Enum(indexmap![i64::MIN => variant("one")])),
      );
    }

    #[test]
    fn with_underscores() {
      let ksy: p::Enum = serde_yml::from_str("
        -9_223_372_036_854_775_808: one
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found string `-9_223_372_036_854_775_808`".into())),
      );
    }
  }

  mod max {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn dec() {
      let ksy: p::Enum = serde_yml::from_str(&format!("
        {}: one
      ", i64::MAX)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Ok(Enum(indexmap![i64::MAX => variant("one")])),
      );
    }

    #[test]
    fn hex() {
      let ksy: p::Enum = serde_yml::from_str(&format!("
        {:#x}: one
      ", i64::MAX)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Ok(Enum(indexmap![i64::MAX => variant("one")])),
      );
    }

    #[test]
    fn with_underscores() {
      let ksy: p::Enum = serde_yml::from_str("
        9_223_372_036_854_775_807: one
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found string `9_223_372_036_854_775_807`".into())),
      );
    }
  }

  mod too_big {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    #[ignore = "TODO: serde_yml cannot handle BigIntegers yet, this YAML failed to parse"]
    fn less_then_min() {
      let ksy: p::Enum = serde_yml::from_str(&format!("
        {}: one
      ", i64::MIN as i128 - 1)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found -9223372036854775809".into())),
      );
    }

    #[test]
    fn more_than_max() {
      let ksy: p::Enum = serde_yml::from_str(&format!("
        {}: one
      ", i64::MAX as i128 + 1)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found number `9223372036854775808`".into())),
      );

      // TODO: serde_yml cannot handle BigIntegers yet, this YAML failed to parse
      /*let ksy: p::Enum = serde_yml::from_str(&format!("
        {}: one
      ", u64::MAX as i128 + 1)).unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found 18446744073709551616".into())),
      );*/
    }

    #[test]
    fn with_underscores() {
      let ksy: p::Enum = serde_yml::from_str("
        111_111_111_111_111_111_111_111_111: one
      ").unwrap();

      assert_eq!(
        Enum::validate(&ksy),
        Err(Validation("expected integral constant in range [-9223372036854775808, 9223372036854775807], found string `111_111_111_111_111_111_111_111_111`".into())),
      );
    }
  }
}
