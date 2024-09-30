use std::fmt::{self, Write};
use std::hash::Hash;

use serde::de::{Deserialize, Deserializer, Error, Visitor};
use serde::ser::{Serialize, Serializer};

/// Relative or absolute path to another `.ksy` file to import
/// (**without** the `.ksy` extension).
///
/// Pattern: `^(.*/)?[a-z][a-z0-9_]*$`.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Import {
  /// Determines if the path starts with the `/`.
  pub absolute: bool,
  /// Components of the path, parts between `/`.
  pub components: Vec<String>,
}
impl fmt::Display for Import {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.absolute {
      f.write_char('/')?;
    }
    for comp in &self.components {
      f.write_str(comp)?;
      f.write_char('/')?;
    }
    Ok(())
  }
}
impl<'de> Deserialize<'de> for Import {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct ImportVisitor;
    impl<'de> Visitor<'de> for ImportVisitor {
      type Value = Import;

      fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a string or a bool")
      }

      fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
      where
        E: Error,
      {
        let (absolute, path) = if let Some(path) = v.strip_prefix('/') {
          (true, path)
        } else {
          (false, v)
        };
        Ok(Import {
          absolute,
          components: path.split('/').map(|comp| comp.to_owned()).collect(),
        })
      }

      fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Ok(Import {
          absolute: false,
          components: vec![v.to_string()],
        })
      }
      // Numbers are not allowed, because +123 we can convert only to "123".
      // Although they are forbidden in names, we would like to parse them anyway to be able
      // to report as many errors as possible, but with the current approach numeric input
      // in import will prevent us from parsing the rest
    }
    deserializer.deserialize_any(ImportVisitor)
  }
}
impl Serialize for Import {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
  use super::*;
  use crate::parser::MetaSpec;

  mod relative {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn str() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - single1
          - single2
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: false,
          components: vec!["single1".into()],
        },
        Import {
          absolute: false,
          components: vec!["single2".into()],
        },
      ]));
    }

    #[test]
    fn int() {
      // Currently YAML parser will interpret input and try to guess numbers and booleans in the strings
      // TODO: if https://github.com/acatton/serde-yaml-ng/issues/13 will be implemented,
      // switch to serde-yaml-ng and enable failsafe schema
      serde_yml::from_str::<MetaSpec>("
        imports:
          - 123
          - -456
          - +789
      ").unwrap_err();
    }

    #[test]
    fn float() {
      // Currently YAML parser will interpret input and try to guess numbers and booleans in the strings
      // TODO: if https://github.com/acatton/serde-yaml-ng/issues/13 will be implemented,
      // switch to serde-yaml-ng and enable failsafe schema
      serde_yml::from_str::<MetaSpec>("
        imports:
          - 1.23
          - -4.56
          - +7.89
      ").unwrap_err();
    }

    #[test]
    fn bool() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - true
          - false
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: false,
          components: vec!["true".into()],
        },
        Import {
          absolute: false,
          components: vec!["false".into()],
        },
      ]));
    }

    #[test]
    fn path() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - true/false/123/-456/+789/file.ext
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: false,
          components: vec![
            "true".into(),
            "false".into(),
            "123".into(),
            "-456".into(),
            "+789".into(),
            "file.ext".into(),
          ],
        },
      ]));
    }
  }

  mod absolute {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn str() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - /single1
          - /single2
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: true,
          components: vec!["single1".into()],
        },
        Import {
          absolute: true,
          components: vec!["single2".into()],
        },
      ]));
    }

    #[test]
    fn int() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - /123
          - /-456
          - /+789
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: true,
          components: vec!["123".into()],
        },
        Import {
          absolute: true,
          components: vec!["-456".into()],
        },
        Import {
          absolute: true,
          components: vec!["+789".into()],
        },
      ]));
    }

    #[test]
    fn float() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - /1.23
          - /-4.56
          - /+7.89
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: true,
          components: vec!["1.23".into()],
        },
        Import {
          absolute: true,
          components: vec!["-4.56".into()],
        },
        Import {
          absolute: true,
          components: vec!["+7.89".into()],
        },
      ]));
    }

    #[test]
    fn bool() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - /true
          - /false
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: true,
          components: vec!["true".into()],
        },
        Import {
          absolute: true,
          components: vec!["false".into()],
        },
      ]));
    }

    #[test]
    fn path() {
      let meta: MetaSpec = serde_yml::from_str("
        imports:
          - /true/false/123/-456/+789/file.ext
      ").unwrap();
      assert_eq!(meta.imports, Some(vec![
        Import {
          absolute: true,
          components: vec![
            "true".into(),
            "false".into(),
            "123".into(),
            "-456".into(),
            "+789".into(),
            "file.ext".into(),
          ],
        },
      ]));
    }
  }
}
