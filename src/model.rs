//! Contains kaitai struct model, used by compiler to generate code.
//! Unlike structures from [`parser`] module that module contains validated
//! structures, that represent only valid constructs of kaitai struct language.
//!
//! [`parser`]: ./parser/index.html

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

use crate::error::ModelError;
use crate::expressions::OwningNode;
use crate::expressions::parser::{parse_single, parse_name, parse_type_ref, parse_process};
use crate::parser as p;

/// Contains helper structures for implementing `TryFrom`.
///
/// `TryFrom` takes ownership of large parser structures, but not all fields
/// of that structure used in every single `TryFrom` implementation. This module
/// contains helper structures, that contains only necessary subset of fields.
/// Advantages over just unnamed tuples is names of fields.
mod helpers {
  use crate::parser as p;

  /// Transitional structure, that contains all data, affecting size of field.
  /// That structure will be cloned for each case in switch-on types.
  #[derive(Clone)]
  pub struct Size {
    pub size: Option<p::Count>,
    pub size_eos: Option<bool>,

    pub terminator: Option<u8>,
    pub consume: Option<bool>,
    pub include: Option<bool>,
    pub eos_error: Option<bool>,

    pub pad_right: Option<u8>,
  }
}

/// Type for representing names of:
///
/// - [enumerations](./struct.Enum.html)
/// - [enumeration values](./enum.EnumValue.html)
/// - [types](./struct.TypeSpec.html)
/// - [instances](./struct.Instance.html)
/// - [attributes](./struct.Attribute.html)
/// - [parameters](./struct.Param.html)
/// - [KSY file](./struct.Ksy.html)
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(String);
impl Name {
  fn validate(data: p::Name) -> Result<Self, ModelError> {
    Ok(Self(parse_name(&data.0)?.into()))
  }
}

/// Path to enum name, used to describe `type` in attributes and parameters.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Path(Vec<Name>);
impl Path {
  fn validate(data: p::Path) -> Result<Self, ModelError> {
    let mut path = Vec::with_capacity(data.0.len());
    for name in data.0.into_iter() {
      path.push(Name::validate(name)?);
    }
    Ok(Self(path))
  }
}

/// Reference to user-defined type name with optional parameters.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UserTypeRef {
  /// Absolute path to type definition
  pub path: Path,
  /// Optional arguments for type
  pub args: Vec<OwningNode>,
}
impl UserTypeRef {
  fn validate(path: String) -> Result<Self, ModelError> {
    let r = parse_type_ref(&path)?;
    Ok(Self {
      path: Path(r.path.into_iter().map(|n| Name(n.to_owned())).collect()),
      args: r.args.into_iter().map(Into::into).collect(),
    })
  }
}

/// Name and parameters of process routine.
#[derive(Clone, Debug, PartialEq)]
pub struct ProcessAlgo {
  /// Name of process routine
  pub name: String,
  /// Optional arguments for type
  pub args: Vec<OwningNode>,
}
impl ProcessAlgo {
  fn validate(algo: p::ProcessAlgo) -> Result<Self, ModelError> {
    let r = parse_process(&algo.0)?;
    Ok(Self {
      name: r.name.into(),
      args: r.args.into_iter().map(Into::into).collect(),
    })
  }
}

/// Expression, that used in boolean contexts.
///
/// Contains AST of expression language, that evaluated to boolean expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Condition(OwningNode);
impl TryFrom<p::Condition> for Condition {
  type Error = ModelError;

  fn try_from(data: p::Condition) -> Result<Self, Self::Error> {
    Ok(match data {
      p::Condition::Expr(expr)   => Self(parse_single(&expr)?.into()),
      p::Condition::Value(value) => Self(OwningNode::Bool(value)),
    })
  }
}

macro_rules! usize_expr {
  ($(#[$meta:meta])* $from:ty => $to:ident) => {
    $(#[$meta])*
    #[derive(Clone, Debug, PartialEq)]
    pub struct $to(OwningNode);
    impl TryFrom<$from> for $to {
      type Error = ModelError;

      fn try_from(data: $from) -> Result<Self, Self::Error> {
        Ok(match data {
          p::Expression::Expr(expr)   => Self(parse_single(&expr)?.into()),
          p::Expression::Value(value) => Self(OwningNode::Int(value)),
        })
      }
    }
  };
}

usize_expr!(
  /// Expression used to represent repetition count.
  ///
  /// Contains AST of expression language, that evaluated to integer expression.
  p::Count => Count
);

usize_expr!(
  /// Expression used to represent instance position.
  ///
  /// Contains AST of expression language, that evaluated to integer expression.
  p::Position => Position
);

/// Generic variant wrapper, that allow or fixed value, or describe a set
/// of possible choices selected based on some expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Variant<T> {
  /// Statically specified value.
  Fixed(T),
  /// Dynamically calculated value based on some expression.
  Choice {
    /// Expression which determines what variant will be used
    switch_on: OwningNode,
    /// Variants
    cases: HashMap<OwningNode, T>,
  }
}
impl<T, U: TryInto<T>> TryFrom<p::Variant<U>> for Variant<T>
  where U::Error: Into<ModelError>,
{
  type Error = ModelError;

  fn try_from(data: p::Variant<U>) -> Result<Self, Self::Error> {
    use p::Variant::*;

    match data {
      Fixed(val) => Ok(Variant::Fixed(val.try_into().map_err(Into::into)?)),
      Choice { switch_on, cases } => {
        let mut new_cases = HashMap::with_capacity(cases.len());
        for (k, v) in cases.into_iter() {
          new_cases.insert(k.try_into()?, v.try_into().map_err(Into::into)?);
        }
        Ok(Variant::Choice {
          switch_on: switch_on.try_into()?,
          cases: new_cases
        })
      },
    }
  }
}

/// Defines way of reading attribute in a structure.
#[derive(Clone, Debug, PartialEq)]
pub enum Repeat {
  /// Attribute not repeated
  None,
  /// Specify, that attribute repeated until end-of-stream of current type will
  /// be reached.
  Eos,
  /// Specify number of repetitions for repeated attribute.
  Count(Count),
  /// Specifies a condition to be checked **after** each parsed item, repeating
  /// while the expression is `false`.
  Until(Condition),
}
impl Repeat {
  fn validate(repeat: Option<p::Repeat>,
              repeat_expr: Option<p::Count>,
              repeat_until: Option<p::Condition>,
  ) -> Result<Self, ModelError> {
    use p::Repeat::*;
    use ModelError::*;

    match (repeat, repeat_expr, repeat_until) {
      (None,        None,        None) => Ok(Self::None),
      (Some(Eos),   None,        None) => Ok(Self::Eos),
      (Some(Expr),  Some(count), None) => Ok(Self::Count(count.try_into()?)),
      (Some(Until), None, Some(until)) => Ok(Self::Until(until.try_into()?)),

      // (None, Some(count), None) => Ok(Self::Count(count.try_into()?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776
      // (None, None, Some(until)) => Ok(Self::Until(until.try_into()?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776

      (None, Some(_), None) => Err(Validation("missed `repeat: expr`".into())),
      (None, None, Some(_)) => Err(Validation("missed `repeat: until`".into())),

      (Some(Expr), None,  _) => Err(Validation("missed `repeat-expr`".into())),
      (Some(Until), _, None) => Err(Validation("missed `repeat-until`".into())),

      (_, Some(_), Some(_)) => Err(Validation("either `repeat-expr` or `repeat-until` must be specified".into())),
      (Some(_), _, Some(_)) => Err(Validation("`repeat-until` requires `repeat: until`".into())),
      (Some(_), Some(_), _) => Err(Validation("`repeat-expr` requires `repeat: expr`".into())),
    }
  }
}

/// Defines "working" sub-stream, as beginning part of full stream.
/// All data after terminator byte is ignored and not available for parsing.
#[derive(Clone, Debug, PartialEq)]
pub struct Terminator {
  /// Byte at which stop reading stream.
  pub value: u8,
  /// Specify if terminator byte should be "consumed" when reading.
  ///
  /// If `true`: the stream pointer will point to the byte after the terminator byte
  /// If `false`: the stream pointer will point to the terminator byte itself
  pub consume: bool,
  /// Specifies if terminator byte should be included in the final value.
  pub include: bool,
  /// If `true`, terminator must be present in the input stream, otherwise
  /// reaching end of stream before encountering terminator also possible.
  ///
  /// Corresponds to `eos-error` key.
  pub mandatory: bool,
}

/// Defines the way of determining size of stream for reading user type.
/// This is size, that attribute is occupied in the stream, but not all
/// bytes can be used for parsing. Some bytes can stay unused.
#[derive(Clone, Debug, PartialEq)]
pub enum Size {
  /// Read all remaining bytes in a stream. Optionally terminator
  /// can define actually available slice for parsing. In that case
  /// only bytes in range `[0; terminator]` will be used to parse data.
  /// All remaining bytes will be unavailable.
  ///
  /// Corresponds to `size-eos: true`.
  Eos(Option<Terminator>),
  /// Read all bytes in a stream until terminator byte is reached.
  ///
  /// Corresponds to `terminator: x`.
  Until(Terminator),
  /// Read exactly specified count of bytes (can be fixed or variable).
  Exact {
    /// Number of bytes which sub-stream occupies in the parent stream.
    ///
    /// Corresponds to `size: count-expr`.
    count: Count,
    /// Defines readable region of stream. If specified, field will take
    /// `size` bytes, but only bytes in range `[0; terminator]` will be
    /// used to parse data. All remaining bytes will be unavailable.
    until: Option<Terminator>,
  },
}
impl Size {
  /// Performs validation of parsed parameters and create structure, that
  /// describe size of field.
  ///
  /// # Parameters
  /// - `type_size`:
  ///   If not `Unsized`, field type has natural size and any size attribute
  ///   is not required; compiler won't complain about that
  /// - `size`:
  ///   Size parameters from parser
  fn validate(type_size: NaturalSize, size: helpers::Size) -> Result<Self, ModelError> {
    use ModelError::*;
    use NaturalSize::*;

    let terminator = match (size.terminator, size.consume, size.include, size.eos_error) {
      (None, None, None, None) => None,
      (Some(value), consume, include, mandatory) => Some(Terminator {
        value,
        consume: consume.unwrap_or(true),
        include: include.unwrap_or(false),
        mandatory: mandatory.unwrap_or(true),
      }),
      // TODO: Emit warning instead here, but error also an option until warnings is not implemented
      //(None, ..) => return Err(Validation("`consume`, `include` or `eos-error` has no effect without `terminator`".into())),
      (None, ..) => None,
    };

    match (size.size, size.size_eos.unwrap_or(false), terminator) {
      (None,        true,   until) => Ok(Self::Eos(until)),
      (None,       false, Some(t)) => Ok(Self::Until(t)),
      // TODO: Warning or even error, if natural type size is less that size
      (Some(size), false,   until) => Ok(Self::Exact { count: size.try_into()?, until }),
      (Some(_),     true,       _) => Err(Validation("only one of `size` or `size-eos: true` must be specified".into())),
      (None,       false,    None) => match type_size {
        // For unknown sized types use all remaining input
        Unknown => Ok(Self::Eos(None)),
        Unsized => Err(Validation("`size`, `size-eos: true` or `terminator` must be specified".into())),
        Sized(size) => Ok(Self::Exact { count: Count(OwningNode::Int(size as u64)), until: None }),
      },
    }
  }
}

/// Natural size of the type.
pub enum NaturalSize {
  /// Type has specific size. That includes all built-in sized types
  /// (all types, except byte arrays and strings).
  Sized(usize),
  /// Type has no natural size. it occupies all the space provided.
  /// Some explicit size definition (as `size`, `size-eos` or `terminator`)
  /// is required.
  Unsized,
  /// Size of type is unknown. That variant is used for external types
  /// and for local user types until compiler will be smart enough to
  /// calculate their sizes.
  Unknown,
}

#[cfg(test)]
mod name {
  use super::*;

  #[test]
  fn ascii() {
    assert_eq!(Name::validate(p::Name("valid".into())), Ok(Name("valid".into())));
    assert_eq!(Name::validate(p::Name("also_valid_".into())), Ok(Name("also_valid_".into())));
  }

  #[test]
  fn with_numbers() {
    assert_eq!(Name::validate(p::Name("val1d".into())), Ok(Name("val1d".into())));
    assert_eq!(Name::validate(p::Name("als0_val1d_".into())), Ok(Name("als0_val1d_".into())));
  }

  #[test]
  fn start_with_number() {
    Name::validate(p::Name("1-not-a-name".into())).unwrap_err();
  }

  #[test]
  fn start_with_underscore() {
    Name::validate(p::Name("_not_valid".into())).unwrap_err();
  }

  #[test]
  fn empty() {
    Name::validate(p::Name("".into())).unwrap_err();
  }
}

