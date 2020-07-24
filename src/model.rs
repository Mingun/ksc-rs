//! Contains kaitai struct model, used by compiler to generate code.
//! Unlike structures from [`parser`] module that module contains validated
//! structures, that represent only valid constructs of kaitai struct language.
//!
//! [`parser`]: ./parser/index.html

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

use lazy_static::lazy_static;
use regex::Regex;

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

  /// Wrapper for inheritable values
  #[derive(Clone)]
  pub enum Inheritable<T> {
    /// Value nor defined in attribute nor inherited
    Undefined,
    /// Value is defined in attribute
    Defined(T),
    /// Value is inherited
    Default(T),
  }
  impl<T> Inheritable<T> {
    /// Constructs three-state from value and its default
    pub fn from(own: Option<T>, def: Option<T>) -> Self {
      match (own, def) {
        (Some(enc), _) => Inheritable::Defined(enc),
        (_, Some(enc)) => Inheritable::Default(enc),
        (None, None)   => Inheritable::Undefined,
      }
    }
    /// Return `Some` for defined value and `None` for undefined or default value
    pub fn own_value(&self) -> Option<&T> {
      match self {
        Inheritable::Undefined |
        Inheritable::Default(_)   => None,
        Inheritable::Defined(val) => Some(val),
      }
    }
  }

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

  /// Transitional structure, that contains all data from parser structure,
  /// used to determine type for model.
  #[derive(Clone)]
  pub struct TypeProps {
    pub enum_:    Option<p::Path>,
    pub contents: Option<p::Contents>,
    pub encoding: Inheritable<String>,
    pub endian:   Option<p::Variant<p::Endian>>,
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

/// Byte order, used for reading built-in numeric types
pub type ByteOrder = Variant<p::Endian>;

/// Types that can be used as base for enumerations.
#[derive(Clone, Debug, PartialEq)]
pub enum Enumerable {
  /// 1-byte unsigned integer.
  U8,
  /// 1-byte signed integer.
  I8,

  /// 2-byte unsigned integer in specified byte order.
  U16(ByteOrder),
  /// 4-byte unsigned integer in specified byte order.
  U32(ByteOrder),
  /// 8-byte unsigned integer in specified byte order.
  U64(ByteOrder),

  /// 2-byte signed integer in specified byte order.
  I16(ByteOrder),
  /// 4-byte signed integer in specified byte order.
  I32(ByteOrder),
  /// 8-byte signed integer in specified byte order.
  I64(ByteOrder),

  /// Number with specified number of bits.
  Bits(usize),
}
impl Enumerable {
  /// Return natural size of type in bytes, or `None`, if type is unsized
  /// (byte arrays and strings) or size is unknown (user types).
  pub fn natural_size(&self) -> NaturalSize {
    use Enumerable::*;
    use NaturalSize::*;

    match self {
      U8 | I8 => Sized(1),
      U16(_) | I16(_) => Sized(2),
      U32(_) | I32(_) => Sized(4),
      U64(_) | I64(_) => Sized(8),

      Bits(size) => Sized(size.saturating_add(7) >> 3),// convert bit count to byte count
    }
  }
}

/// Reference to type definition - built-in or user-defined.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeRef {
  /// Possible enumerable types
  Enum {
    /// Type on which enumeration is based
    base: Enumerable,
    /// Path to enumeration definition. If specified, type should be represented
    /// as enumeration
    enum_: Option<Path>,
  },

  /// 4-byte floating point format that follows [IEEE 754] standard in specified byte order.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  F32(ByteOrder),
  /// 8-byte floating point format that follows [IEEE 754] standard in specified byte order.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  F64(ByteOrder),

  /// Byte array from input sequence
  Bytes,

  /// String in specified encoding
  String(String),

  /// Reference to user-defined type
  User(UserTypeRef),

  /// Attribute has type of byte array which content must be equal this value
  Fixed(Vec<u8>),
}
impl TypeRef {
  /// Return natural size of type in bytes, or `None`, if type is unsized
  /// (byte arrays and strings) or size is unknown (user types).
  pub fn natural_size(&self) -> NaturalSize {
    use TypeRef::*;
    use NaturalSize::*;

    match self {
      Enum { base, .. } => base.natural_size(),

      F32(_) => Sized(4),
      F64(_) => Sized(8),

      Fixed(contents) => Sized(contents.len()),

      Bytes | String(_) => Unsized,
      User(_) => Unknown,// TODO: Get size of user type
    }
  }

  fn validate(type_ref: Option<p::TypeRef>, props: helpers::TypeProps) -> Result<Self, ModelError> {
    lazy_static! {
      static ref BITS: Regex = Regex::new("^b([0-9]+)$").expect("incorrect BITS regexp");
    }

    use ModelError::*;
    use Enumerable::*;
    use TypeRef::{Enum, F32, F64};
    use p::Builtin::*;
    use p::TypeRef::*;
    use p::Endian::*;
    use helpers::Inheritable::*;

    let endian = props.endian;
    let endian = |t| match endian {
      Some(e) => Ok(ByteOrder::try_from(e)?),
      None => Err(Validation(format!("unable to use type `{:?}` without default endianness", t).into())),
    };
    // Extract encoding of string
    let encoding = |e: helpers::Inheritable<String>| match e {
      Undefined    => Err(Validation("string requires encoding".into())),
      Default(enc) => Ok(enc),
      Defined(enc) => Ok(enc),
    };
    // Produces error of illegal use of enum
    let enum_err = || Err(Validation("`enum` can be used only with integral (`u*`, `s*` and `b*`) types".into()));

    let enum_ = props.enum_.map(Path::validate);
    match (type_ref, props.encoding.own_value(), props.contents, enum_) {
      (Some(Builtin(s1)),   None, None, e) => Ok(Enum { base: I8, enum_: e.transpose()? }),
      (Some(Builtin(u1)),   None, None, e) => Ok(Enum { base: U8, enum_: e.transpose()? }),

      (Some(Builtin(u2)),   None, None, e) => Ok(Enum { base: U16(endian(u2)?),          enum_: e.transpose()? }),
      (Some(Builtin(u2be)), None, None, e) => Ok(Enum { base: U16(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(u2le)), None, None, e) => Ok(Enum { base: U16(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(s2)),   None, None, e) => Ok(Enum { base: I16(endian(s2)?),          enum_: e.transpose()? }),
      (Some(Builtin(s2be)), None, None, e) => Ok(Enum { base: I16(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(s2le)), None, None, e) => Ok(Enum { base: I16(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(u4)),   None, None, e) => Ok(Enum { base: U32(endian(u4)?),          enum_: e.transpose()? }),
      (Some(Builtin(u4be)), None, None, e) => Ok(Enum { base: U32(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(u4le)), None, None, e) => Ok(Enum { base: U32(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(s4)),   None, None, e) => Ok(Enum { base: I32(endian(s4)?),          enum_: e.transpose()? }),
      (Some(Builtin(s4be)), None, None, e) => Ok(Enum { base: I32(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(s4le)), None, None, e) => Ok(Enum { base: I32(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(u8)),   None, None, e) => Ok(Enum { base: U64(endian(u8)?),          enum_: e.transpose()? }),
      (Some(Builtin(u8be)), None, None, e) => Ok(Enum { base: U64(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(u8le)), None, None, e) => Ok(Enum { base: U64(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(s8)),   None, None, e) => Ok(Enum { base: I64(endian(s8)?),          enum_: e.transpose()? }),
      (Some(Builtin(s8be)), None, None, e) => Ok(Enum { base: I64(ByteOrder::Fixed(Be)), enum_: e.transpose()? }),
      (Some(Builtin(s8le)), None, None, e) => Ok(Enum { base: I64(ByteOrder::Fixed(Le)), enum_: e.transpose()? }),

      (Some(Builtin(f4)),   None, None, None) => Ok(F32(endian(f4)?)),
      (Some(Builtin(f4be)), None, None, None) => Ok(F32(ByteOrder::Fixed(Be))),
      (Some(Builtin(f4le)), None, None, None) => Ok(F32(ByteOrder::Fixed(Le))),

      (Some(Builtin(f8)),   None, None, None) => Ok(F64(endian(f8)?)),
      (Some(Builtin(f8be)), None, None, None) => Ok(F64(ByteOrder::Fixed(Be))),
      (Some(Builtin(f8le)), None, None, None) => Ok(F64(ByteOrder::Fixed(Le))),

      (Some(Builtin(str)),     _, None, None) => Ok(TypeRef::String(encoding(props.encoding)?)),
      (Some(Builtin(strz)),    _, None, None) => Ok(TypeRef::String(encoding(props.encoding)?)),

      (Some(User(name)), None, None, e) => if let Some(caps) = BITS.captures(&name) {
        Ok(Enum { base: Bits(caps[1].parse().unwrap()), enum_: e.transpose()? })
      } else
      if let None = e {
        Ok(TypeRef::User(UserTypeRef::validate(name)?))
      } else {
        enum_err()
      },

      (None, None, Some(content), None) => Ok(TypeRef::Fixed(content.into())),
      (None, None, None, None)          => Ok(TypeRef::Bytes),

      (_, Some(_), _, _) => Err(Validation("`encoding` can be specified only for `type: str` or `type: strz`".into())),
      (_, _, Some(_), _) => Err(Validation("`contents` don't require type, its always byte array".into())),
      (_, _, _, Some(_)) => enum_err(),
    }
  }
}

/// A pack of reference to type and size of occupied space in stream
#[derive(Clone, Debug, PartialEq)]
pub struct Chunk {
  /// Reference to type of this attribute. Type can be fixed or calculated
  pub type_ref: TypeRef,//TODO: resolve references, check, that all types exist

  /// Size of stream from which this attribute will be readed. That size of one element,
  /// so if attribute repeated many times, that field determines size of each element,
  /// not the size of sequence.
  pub size: Size,
}
impl Chunk {
  fn validate(type_ref: Option<p::TypeRef>,
              props: helpers::TypeProps,
              mut size: helpers::Size,
  ) -> Result<Self, ModelError> {
    use p::Builtin::strz;
    use p::TypeRef::Builtin;

    // Special case for strz - define default terminator
    if let Some(Builtin(strz)) = type_ref {
      size.terminator = size.terminator.or(Some(0));
    }

    let type_ref = TypeRef::validate(type_ref, props)?;
    let size = Size::validate(type_ref.natural_size(), size)?;
    Ok(Self { type_ref, size })
  }
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

