//! Common types, used both in serialized and model representations of KSY.

// use std::convert::{TryFrom, TryInto};
use std::hash::Hash;

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

use Variant::*;

/// Generic variant wrapper, that allow or fixed value, or describe a set
/// of possible choices selected based on some expression.
///
/// `Condition`: type used to represent condition to select
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum Variant<Condition, Key, T>
  where Key: Eq + Hash,
{
  /// Statically specified value.
  Fixed(T),
  /// Dynamically calculated value based on some expression.
  #[serde(rename_all = "kebab-case")]
  Choice {
    /// Expression which determines what variant will be used
    switch_on: Condition,
    /// Variants
    cases: IndexMap<Key, T>,
  }
}
impl<C, K, T> Variant<C, K, T>
  where K: Eq + Hash,
{
  /// Convert all values inside this variant to another type
  pub fn map_value<U, F>(self, mut f: F) -> Variant<C, K, U>
    where F: FnMut(T) -> U,
  {
    match self {
      Fixed(val) => Fixed(f(val)),
      Choice { switch_on, cases } => {
        Variant::Choice {
          switch_on,
          cases: cases.into_iter().map(|(k, v)| (k, f(v))).collect()
        }
      },
    }
  }
}
/*
impl<C1, K1, T1, C2, K2, T2, E> TryFrom<Variant<C2, K2, T2>> for Variant<C1, K1, T1>
  where K1: Eq + Hash,
        C2: TryInto<C1>,
        K2: TryInto<K1> + Eq + Hash,
        T2: TryInto<T1>,
        C2::Error: Into<E>,
        K2::Error: Into<E>,
        T2::Error: Into<E>,
{
  type Error = E;

  fn try_from(data: Variant<C2, K2, T2>) -> Result<Self, Self::Error> {
    match data {
      Fixed(val) => Ok(Fixed(val.try_into().map_err(Into::into)?)),
      Choice { switch_on, cases } => {
        let mut new_cases = IndexMap::with_capacity(cases.len());
        for (k, v) in cases.into_iter() {
          new_cases.insert(k.try_into().map_err(Into::into)?, v.try_into().map_err(Into::into)?);
        }
        Ok(Choice {
          switch_on: switch_on.try_into().map_err(Into::into)?,
          cases: new_cases
        })
      },
    }
  }
}*/
