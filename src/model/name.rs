// Colorful diffs in assertions
#[cfg(test)]
use pretty_assertions::assert_eq;

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::Deref;

use indexmap::Equivalent;

use crate::error::ModelError;
use crate::parser as p;
use crate::parser::expressions::parse_name;

/// Contains tags to create distinguish types for each kind of name
/// so it accidentally wouldn't be mixed in one expression.
mod tags {
  /// Tag for name of fields (both sequential and instance attributes)
  pub enum Field {}
  /// Tag for name of user type parameter
  pub enum Param {}

  /// Tag for name of user type
  pub enum Type {}
  /// Tag for name of enumeration
  pub enum Enum {}
  /// Tag for name of enumeration
  pub enum EnumValue {}
}

/// Type-safe wrapper on string to represent names in KSY model.
///
/// Names implements `Deref<Target=str>`, so you can use any read-only
/// methods of string slices to operate with them.
///
/// That type is used for representing names of:
///
/// - [enumerations](./struct.Enum.html)
/// - [enumeration values](./enum.EnumValue.html)
/// - [types](./struct.TypeSpec.html)
/// - [instances](./struct.Instance.html)
/// - [attributes](./struct.Attribute.html)
/// - [parameters](./struct.Param.html)
/// - [KSY file](./struct.Ksy.html)
pub struct Name<Tag>(String, PhantomData<Tag>);
impl<Tag> Name<Tag> {
  /// Creates a new name assumes that it is valid
  pub(crate) fn valid(name: &str) -> Self {
    Self(name.into(), PhantomData)
  }
  /// Checks that the name contains only valid characters and creates a new one.
  ///
  /// Valid names matches the following regexp: `$[a-zA-Z][a-zA-Z0-9_]*^`.
  pub fn validate(name: p::Name) -> Result<Self, ModelError> {
    Ok(Self::valid(parse_name(&name.0)?))
  }
}
impl<Tag> Clone for Name<Tag> {
  #[inline]
  fn clone(&self) -> Self { Name(self.0.clone(), PhantomData) }
}
impl<Tag> Debug for Name<Tag> {
  #[inline]
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "Name({})", self.0)
  }
}
impl<Tag> Display for Name<Tag> {
  #[inline]
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    <String as Display>::fmt(&self.0, f)
  }
}
impl<Tag> Default for Name<Tag> {
  #[inline]
  fn default() -> Self { Name(Default::default(), PhantomData) }
}
impl<Tag> PartialEq for Name<Tag> {
  #[inline]
  fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
}
impl<Tag> Eq for Name<Tag> {}
impl<Tag> PartialOrd for Name<Tag> {
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.0.partial_cmp(&other.0) }
}
impl<Tag> Ord for Name<Tag> {
  #[inline]
  fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
}
impl<Tag> Hash for Name<Tag> {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    // Because we want to search in the IndexMap<FieldName, ...> by InstanceName
    // the hashes should be the same. Hash of the `value` and `&value` the same,
    // so just calculate hash from the wrapper
    (0, &self.0).hash(state);
  }
}
impl<Tag> Deref for Name<Tag> {
  type Target = str;

  #[inline]
  fn deref(&self) -> &Self::Target { &self.0 }
}
impl<Tag> TryFrom<p::Name> for Name<Tag> {
  type Error = ModelError;

  fn try_from(name: p::Name) -> Result<Self, Self::Error> {
    Self::validate(name)
  }
}

/// Represents name, that can be manually specified or automatically generated one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptionalName<T> {
  /// Name, given to element
  Named(T),
  /// Automatically generated name for unnamed element.
  /// Name is derived from sequential index starting from zero.
  Unnamed(usize),
}
impl<'a, T: TryFrom<p::Name>> OptionalName<T> {
  /// Checks that the name contains only valid characters and creates a new one.
  ///
  /// If name is not defined, creates new auto-generated name based on the index.
  /// index must be unique for owner.
  ///
  /// Valid names matches following regexp: `$[a-zA-Z][a-zA-Z0-9_]*^`.
  pub(crate) fn validate(index: usize, name: Option<p::Name>) -> Result<Self, T::Error> {
    Ok(match name {
      Some(name) => Self::Named(TryFrom::try_from(name)?),
      None       => Self::Unnamed(index),
    })
  }
}
impl<T: Display> Display for OptionalName<T> {
  #[inline]
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      OptionalName::Named(val) => <T as Display>::fmt(&val, f),
      OptionalName::Unnamed(i) => write!(f, "<unnamed_{}>", i),
    }
  }
}
impl<Tag> Hash for OptionalName<Name<Tag>> {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    match self {
      // Because we want to search in the IndexMap<FieldName, ...> by InstanceName
      // the hashes should be the same
      OptionalName::Named(val) => val.hash(state),
      OptionalName::Unnamed(i) => (1, i).hash(state),
    }
  }
}
impl<Tag> Equivalent<OptionalName<Name<Tag>>> for Name<Tag> {
  fn equivalent(&self, key: &OptionalName<Name<Tag>>) -> bool {
    match key {
      OptionalName::Named(val) => val == self,
      OptionalName::Unnamed(_) => false,
    }
  }
}

/// Name of attributes that can be parsed not in strict order and defined in the
/// `instances` map
pub type FieldName = Name<tags::Field>;

/// Name of attributes that parsed sequentially and defined in the `seq` list
pub type SeqName = OptionalName<FieldName>;

/// Name of user type parameter
pub type ParamName = OptionalName<Name<tags::Param>>;

/// Name of type
pub type TypeName = Name<tags::Type>;

/// Name of enumeration
pub type EnumName = Name<tags::Enum>;

/// Name of enumeration value
pub type EnumValueName = Name<tags::EnumValue>;


/// Path to enum name, used to describe `type` in attributes and parameters.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumPath {
  /// Path to type with enum definition
  path: Vec<TypeName>,
  /// Name of enum inside type
  name: EnumName,
}
impl EnumPath {
  /// Checks that the names in path contains only valid characters and creates
  /// a new path to enum.
  ///
  /// If `data` is empty, error is returned.
  ///
  /// Valid names in path matches following regexp: `$[a-zA-Z][a-zA-Z0-9_]*^`.
  pub fn validate(mut data: p::Path) -> Result<Self, ModelError> {
    let len = data.0.len();
    if len < 1 {
      return Err(ModelError::Validation("enum name is empty".into()));
    }

    let len = len - 1;
    let name = data.0.remove(len);
    let mut path = Vec::with_capacity(len);
    for name in data.0.into_iter() {
      path.push(TypeName::validate(name)?);
    }
    Ok(Self { path, name: EnumName::validate(name)? })
  }
}
impl From<EnumName> for EnumPath {
  fn from(name: EnumName) -> Self {
    Self { path: vec![], name }
  }
}

#[cfg(test)]
enum Tag {}

#[test]
fn ascii() {
  assert_eq!(Name::<Tag>::validate(p::Name("valid".into())),       Ok(Name::valid("valid")));
  assert_eq!(Name::<Tag>::validate(p::Name("also_valid_".into())), Ok(Name::valid("also_valid_")));
}

#[test]
fn with_numbers() {
  assert_eq!(Name::<Tag>::validate(p::Name("val1d".into())),       Ok(Name::valid("val1d")));
  assert_eq!(Name::<Tag>::validate(p::Name("als0_val1d_".into())), Ok(Name::valid("als0_val1d_")));
}

#[test]
fn start_with_number() {
  Name::<Tag>::validate(p::Name("1-not-a-name".into())).unwrap_err();
}

#[test]
fn start_with_underscore() {
  Name::<Tag>::validate(p::Name("_not_valid".into())).unwrap_err();
}

#[test]
fn empty() {
  Name::<Tag>::validate(p::Name("".into())).unwrap_err();
}

#[test]
fn equivalency() {
  fn calculate_hash<T: Hash>(t: &T) -> u64 {
      let mut s = std::collections::hash_map::DefaultHasher::new();
      t.hash(&mut s);
      s.finish()
  }
  let name: Name<Tag> = Name::valid("field");
  let opt: OptionalName<Name<Tag>> = OptionalName::Named(Name::valid("field"));

  assert_eq!(
    calculate_hash(&name),
    calculate_hash(&opt),
  );

  assert!(name.equivalent(&opt));
}
