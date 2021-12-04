//! Contains kaitai struct model, used by compiler to generate code.
//! Unlike structures from [`parser`] module that module contains validated
//! structures, that represent only valid constructs of kaitai struct language.
//!
//! [`parser`]: ./parser/index.html

use std::convert::{TryFrom, TryInto};
use std::cmp;
use std::fmt::Display;
use std::hash::Hash;
use std::ops::{Add, Deref};

use bigdecimal::num_bigint::{BigInt, BigUint};
use indexmap::{indexmap, IndexMap};
use indexmap::map::Entry;
use lazy_static::lazy_static;
use regex::Regex;

use crate::error::ModelError;
use crate::model::expressions::OwningNode;
use crate::parser as p;
use crate::parser::expressions::{parse_type_ref, parse_process};

pub mod expressions;
mod name;
pub use name::*;

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
    /// If that value if defined, make it inherited. Otherwise returns the same value
    pub fn to_inherited(self) -> Self {
      match self {
        Inheritable::Defined(val) => Inheritable::Default(val),
        x => x,
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

/// Reference to a user-defined type name with an optional parameters.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UserTypeRef {
  /// Absolute path to type definition
  pub path: Vec<TypeName>,
  /// A local name of the referenced type
  pub name: TypeName,
  /// Optional arguments for type
  pub args: Vec<OwningNode>,
}
impl UserTypeRef {
  fn validate(path: String) -> Result<Self, ModelError> {
    let r = parse_type_ref(&path)?;
    Ok(Self {
      //TODO: resolve relative types
      path: r.name.scope.path.into_iter().map(TypeName::valid).collect(),
      name: TypeName::valid(r.name.name),
      args: OwningNode::validate_all(r.args),
    })
  }
}

/// Name and parameters of the process routine.
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
      args: OwningNode::validate_all(r.args),
    })
  }
}

/// An expression used in boolean contexts.
///
/// Contains AST of the expression language that evaluated to a boolean value.
#[derive(Clone, Debug, PartialEq)]
pub struct Condition(OwningNode);
impl Condition {
  fn validate(data: p::Condition) -> Result<Self, ModelError> {
    Ok(match data {
      p::Condition::Expr(expr)   => Self(OwningNode::parse(&expr)?),
      p::Condition::Value(value) => Self(OwningNode::Bool(value)),
    })
  }
}
impl Deref for Condition {
  type Target = OwningNode;

  #[inline]
  fn deref(&self) -> &OwningNode {
    &self.0
  }
}

macro_rules! usize_expr {
  ($(#[$meta:meta])* $from:ty => $to:ident) => {
    $(#[$meta])*
    #[derive(Clone, Debug, PartialEq)]
    pub struct $to(OwningNode);
    impl $to {
      fn validate(data: $from) -> Result<Self, ModelError> {
        Ok(match data {
          p::Expression::Expr(expr)   => Self(OwningNode::parse(&expr)?),
          p::Expression::Value(value) => Self(OwningNode::Int(value.into())),
        })
      }
    }
    impl Deref for $to {
      type Target = OwningNode;

      #[inline]
      fn deref(&self) -> &OwningNode {
        &self.0
      }
    }
  };
}

usize_expr!(
  /// An expression used to represent repetition count.
  ///
  /// Contains AST of the expression language that evaluated to an integer value.
  p::Count => Count
);

usize_expr!(
  /// An expression used to represent instance position.
  ///
  /// Contains AST of the expression language that evaluated to an integer value.
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
    cases: IndexMap<OwningNode, T>,
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
        let mut new_cases = IndexMap::with_capacity(cases.len());
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
impl Variant<Chunk> {
  /// Calculates combined size of all chunks in this container.
  /// The calculated size is most common size of all variants.
  fn sizeof(&self) -> SizeOf {
    match self {
      Variant::Fixed(chunk) => chunk.sizeof(),
      Variant::Choice { cases, .. } => cases.values().fold(
        Option::<SizeOf>::None,
        |acc, chunk| Some(match acc {
          None => chunk.sizeof(),
          Some(size) => size.or(chunk.sizeof()),
        })
      ).unwrap_or(SizeOf::Unknown),
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
      (Some(Expr),  Some(count), None) => Ok(Self::Count(Count::validate(count)?)),
      (Some(Until), None, Some(until)) => Ok(Self::Until(Condition::validate(until)?)),

      // (None, Some(count), None) => Ok(Self::Count(Count::validate(count)?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776
      // (None, None, Some(until)) => Ok(Self::Until(Condition::validate(until)?)),//TODO https://github.com/kaitai-io/kaitai_struct/issues/776

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
impl From<u8> for Terminator {
  /// Creates a new terminator from the specified terminator byte.
  ///
  /// Terminator will be mandatory and consumed, but not included
  /// (default behavior of the `strz` type and `terminator: value`
  /// key without other options specified)
  fn from(value: u8) -> Self {
    Self {
      value,
      consume: true,
      include: false,
      mandatory: true,
    }
  }
}

/// Defines the way of determining size of stream for reading user type.
/// This is size, that attribute is occupied in the stream, but not all
/// bytes can be used for parsing. Some bytes can stay unused.
#[derive(Clone, Debug, PartialEq)]
pub enum Size {
  /// Size not defined explicitly, natural size should be used for reading
  /// field. Corresponds to not defined size. To get a real size use the
  /// [`sizeof()`] method.
  ///
  /// [`sizeof()`]: ./enum.TypeRef.html#method.sizeof
  Natural,
  /// Read all remaining bytes in a stream. Optionally terminator
  /// can define actually available slice for parsing. In that case
  /// only bytes in range `[0; terminator]` will be used to parse data.
  /// All remaining bytes will be unavailable.
  ///
  /// ```text
  ///          /====\ - actually used data
  /// Stream: [<type>                   <         ]
  ///         0                         until    eos
  ///          \_available for parsing_/         /
  ///           \____________sizeof() of chunk__/
  ///            \________________stream size__/
  /// ```
  ///
  /// - `Eos(None)` corresponds to
  ///   ```yaml
  ///   size-eos: true
  ///   ```
  /// - `Eos(Some(...))` corresponds to
  ///   ```yaml
  ///   size-eos: true
  ///   terminator: ...
  ///   ```
  Eos(Option<Terminator>),
  /// Read all bytes in a stream until terminator byte is reached.
  ///
  /// ```text
  ///          /====\ - actually used data
  /// Stream: [<type>                   ]_________|
  ///         0                         until    eos
  ///          \_available for parsing_/         /
  ///           \__sizeof() of chunk__/         /
  ///            \________________stream size__/
  /// ```
  ///
  /// Corresponds to `terminator: x`.
  Until(Terminator),
  /// Read exactly specified count of bytes (can be fixed or variable).
  ///
  /// ```text
  ///          /====\ - actually used data
  /// Stream: [<type>                   <                     ]_________|
  ///         0                         until             count        eos
  ///          \_available for parsing_/                     /         /
  ///           \________________________sizeof() of chunk__/         /
  ///            \______________________________________stream size__/
  /// ```
  ///
  /// - `Exact { count: ..., until: None }` corresponds to
  ///   ```yaml
  ///   size: ...
  ///   ```
  /// - `Exact { count: ..., until: Some(...) }` corresponds to
  ///   ```yaml
  ///   size: ...
  ///   terminator: ...
  ///   ```
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
  fn validate(type_size: SizeOf, size: helpers::Size) -> Result<Self, ModelError> {
    use ModelError::*;
    use SizeOf::*;

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
      (Some(size), false,   until) => Ok(Self::Exact { count: Count::validate(size)?, until }),
      (Some(_),     true,       _) => Err(Validation("only one of `size` or `size-eos: true` must be specified".into())),
      (None,       false,    None) => match type_size {
        // For unknown sized types use all remaining input
        Unknown => Ok(Self::Eos(None)),
        Unsized(_, _) => Err(Validation("`size`, `size-eos: true` or `terminator` must be specified".into())),
        Sized(_) => Ok(Self::Natural),
      },
    }
  }
}
impl From<u64> for Size {
  /// Creates a new exact-sized `Size` from the specified numeric value.
  /// An equivalent KSY definition would be:
  ///
  /// ```yaml
  /// - size: <value>
  /// ```
  fn from(value: u64) -> Self {
    Self::Exact {
      count: Count(OwningNode::Int(value.into())),
      until: None,
    }
  }
}

/// Natural size of the type.
#[derive(Clone, Debug, PartialEq)]
pub enum SizeOf {
  /// Type has specific size. That includes all built-in sized types
  /// (all types, except byte arrays and strings).
  Sized(BigUint),
  /// Type has no natural size. it occupies all the space provided.
  /// Some explicit size definition (as `size`, `size-eos` or `terminator`)
  /// is required.
  ///
  /// The value contained represents the minimum and the maximum size of the type
  Unsized(BigUint, Option<BigUint>),
  /// Size of type is unknown. That variant is used for external types
  /// and for local user types until compiler will be smart enough to
  /// calculate their sizes.
  Unknown,
}
impl SizeOf {
  fn or(self, other: Self) -> Self {
    use std::cmp::{min, max};
    use SizeOf::*;

    match (self, other) {
      (Unknown, _) => Unknown,
      (_, Unknown) => Unknown,

      (Unsized(l, Some(lm)), Unsized(r, Some(rm))) => Unsized(min(l, r), Some(max(lm, rm))),
      (Unsized(l,        _), Unsized(r,        _)) => Unsized(min(l, r), None),

      (Unsized(l, Some(lm)), Sized(r)) => Unsized(min(l, r.clone()), Some(max(lm, r))),
      (Unsized(l,        _), Sized(r)) => Unsized(min(l, r), None),

      (Sized(l), Unsized(r, Some(rm))) => Unsized(min(l.clone(), r), Some(max(l, rm))),
      (Sized(l), Unsized(r,        _)) => Unsized(min(l, r), None),

      (Sized(l), Sized(r)) if l == r => Sized(l),
      (Sized(l), Sized(r)) if l <  r => Unsized(l, Some(r)),
      (Sized(l), Sized(r))           => Unsized(r, Some(l)),
    }
  }
}
impl Add for SizeOf {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    use SizeOf::*;

    match (self, rhs) {
      (Unknown, _) => Unknown,
      (_, Unknown) => Unknown,

      (Unsized(l, Some(lm)), Unsized(r, Some(rm))) => Unsized(l + r, Some(rm + lm)),
      (Unsized(l,        _), Unsized(r,        _)) => Unsized(l + r, None),

      (Unsized(l, Some(lm)), Sized(r)) => Unsized(l + r.clone(), Some(lm + r)),
      (Unsized(l,        _), Sized(r)) => Unsized(l + r, None),

      (Sized(l), Unsized(r, Some(rm))) => Unsized(l.clone() + r, Some(l + rm)),
      (Sized(l), Unsized(r,        _)) => Unsized(l + r, None),

      (Sized(l), Sized(r)) => Sized(l + r),
    }
  }
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
  /// Returns the size of the type in bytes.
  pub fn size(&self) -> usize {
    use Enumerable::*;

    match self {
      U8 | I8 => 1,
      U16(_) | I16(_) => 2,
      U32(_) | I32(_) => 4,
      U64(_) | I64(_) => 8,

      Bits(size) => size.saturating_add(7) >> 3,// convert bit count to byte count
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
    enum_: Option<EnumPath>,
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
  /// Returns the size of the type in bytes, `Unsized`, if type is unsized
  /// (byte arrays and strings) and `Unknown` if size not calculated yet.
  pub fn sizeof(&self) -> SizeOf {
    use TypeRef::*;
    use SizeOf::*;

    match self {
      Enum { base, .. } => Sized(base.size().into()),

      F32(_) => Sized(4usize.into()),
      F64(_) => Sized(8usize.into()),

      Fixed(contents) => Sized(contents.len().into()),

      Bytes | String(_) => Unsized(0usize.into(), None),
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

    let enum_ = props.enum_.map(EnumPath::validate);
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

/// An untyped space of some size that holds data which may be interpret as a specified type.
/// The size of space can be determined or by the underlying type, or by the direct specification
/// in the KSY `size` or `size-eos` attribute.
#[derive(Clone, Debug, PartialEq)]
pub struct Chunk {
  /// Reference to type of this attribute. Type can be fixed or calculated
  pub type_ref: TypeRef,//TODO: resolve references, check, that all types exist

  /// Size of stream from which this attribute will be read. That size of the one element,
  /// so if attribute repeated many times, that field determines the size of each element,
  /// not the size of sequence.
  pub size: Size,
}
impl Chunk {
  /// Calculates actual size that chunk occupies in the stream
  fn sizeof(&self) -> SizeOf {
    use SizeOf::*;

    let size = self.type_ref.sizeof();
    match &self.size {
      Size::Natural => size,
      //TODO: evaluate constant conditions and check that count is non-negative
      Size::Exact { count: Count(OwningNode::Int(count)), .. } => {
        let (_, count) = cmp::max(count.clone(), BigInt::default()).into_parts();
        Sized(count)
      },
      Size::Eos(_) | Size::Until(_) | Size::Exact { .. } => match size {
        Unknown         => Unknown,
        Unsized(min, _) => Unsized(min, None),
        Sized(size)     => Unsized(size.into(), None),
      },
    }
  }
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
    let size = Size::validate(type_ref.sizeof(), size)?;
    Ok(Self { type_ref, size })
  }
}

/// Defines, how to read and interpret data
#[derive(Clone, Debug, PartialEq)]
pub struct Attribute {
  /// Reference to type and size of this attribute. Type can be fixed or calculated
  pub chunk: Variant<Chunk>,

  /// Specify how many times a given attribute should occur in a stream.
  pub repeat: Repeat,
  /// If specified, attribute will be read only if condition evaluated to `true`.
  pub condition: Option<Condition>,

  /// Algorithm that run on raw byte array before parsing data.
  /// Example of algorithms: encryption, base64/hex encoding etc.
  pub process: Option<ProcessAlgo>,
}
impl Attribute {
  fn validate(attr: p::Attribute, defaults: p::Defaults) -> Result<Self, ModelError> {
    use p::Variant::*;

    let mut props = helpers::TypeProps {
      enum_:    attr.enum_,
      contents: attr.contents,
      encoding: helpers::Inheritable::from(attr.encoding, defaults.encoding),
      endian:   defaults.endian,
    };
    let size = helpers::Size {
      size:       attr.size,
      size_eos:   attr.size_eos,

      terminator: attr.terminator,
      consume:    attr.consume,
      include:    attr.include,
      eos_error:  attr.eos_error,

      pad_right:  attr.pad_right,
    };
    Ok(Self {
      chunk:     match attr.type_ {
        None             => Variant::Fixed(Chunk::validate(None,      props, size)?),
        Some(Fixed(val)) => Variant::Fixed(Chunk::validate(Some(val), props, size)?),
        Some(Choice { switch_on, cases }) => {
          // Because in switch-on expression encoding defined not at the same level, as type
          // (not in `case:` clause), we make it inherited
          props.encoding = props.encoding.to_inherited();
          let mut new_cases = IndexMap::with_capacity(cases.len());
          for (k, val) in cases.into_iter() {
            let chunk = Chunk::validate(Some(val), props.clone(), size.clone())?;
            new_cases.insert(k.try_into()?, chunk);
          }
          Variant::Choice {
            switch_on: switch_on.try_into()?,
            cases: new_cases
          }
        },
      },
      repeat:    Repeat::validate(attr.repeat, attr.repeat_expr, attr.repeat_until)?,
      condition: attr.condition.map(Condition::validate).transpose()?,
      process:   attr.process.map(ProcessAlgo::validate).transpose()?,
    })
  }
}
impl From<Chunk> for Attribute {
  /// Creates a new attribute definition from a chunk definition.
  ///
  /// Attribute created without repetitions, conditions or process routine.
  /// An equivalent KSY definition would be:
  ///
  /// ```yaml
  /// seq:
  ///   - type: ...       # not `switch-on`
  ///     size: ...       # optional
  ///     # size-eos: ... # optional
  ///     terminator: ... # optional
  ///     eos-error: ...  # optional
  /// ```
  fn from(chunk: Chunk) -> Self {
    Self {
      chunk: Variant::Fixed(chunk),
      repeat: Repeat::None,
      condition: None,
      process: None,
    }
  }
}

/// Defines a user-defined type
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Type {
  /// The list of fields that this type consists of. The fields in the data stream
  /// are in the same order as they are declared here.
  pub fields: IndexMap<SeqName, Attribute>,
  // pub getters: IndexMap<InstanceName, Instance>,//TODO: instances
  /// List of used-defined types, defined inside this type.
  pub types: IndexMap<TypeName, Type>,
  // pub enums: IndexMap<EnumName, Enum>,//TODO: Enums
  // pub params: IndexMap<ParamName, Param>,//TODO: Parameters
}
impl Type {
  /// Performs validation of lists for duplicated entries
  ///
  /// # Parameters
  /// - `seq`: sequence of elements from a `parser` module
  /// - `check`: validation function that converts type from a `parser` module into
  ///   type from a `model` module
  fn check_duplicates<I, K, V, F>(seq: Option<I>, mut check: F) -> Result<IndexMap<K, V>, ModelError>
    where I: IntoIterator,
          K: Eq + Hash + Display,
          F: FnMut(I::Item) -> Result<(K, V), ModelError>
  {
    use ModelError::*;

    Ok(match seq {
      None => indexmap![],
      Some(seq) => {
        let iter = seq.into_iter();
        let mut result = IndexMap::with_capacity(iter.size_hint().1.unwrap_or(0));
        for elem in iter {
          let (k, v) = check(elem)?;
          match result.entry(k) {
            Entry::Vacant(e)   => e.insert(v),
            Entry::Occupied(e) => return Err(Validation(format!("duplicated name `{}`", e.key()).into())),
          };
        }
        result
      }
    })
  }
  fn validate(spec: p::TypeSpec, mut defaults: p::Defaults) -> Result<Self, ModelError> {
    // Merge type defaults with inherited defaults
    if let Some(def) = spec.default {
      defaults.endian   = def.endian.or(defaults.endian);
      defaults.encoding = def.encoding.or(defaults.encoding);
    }

    let fields = Self::check_duplicates(spec.seq.map(|s| s.into_iter().enumerate()), |(i, mut spec)| {
      Ok((
        SeqName::validate(i, spec.id.take())?,
        Attribute::validate(spec, defaults.clone())?,
      ))
    })?;
    let types = Self::check_duplicates(spec.types, |(name, spec)| {
      Ok((
        TypeName::validate(name)?,
        Type::validate(spec, defaults.clone())?
      ))
    })?;

    Ok(Self {
      fields,
      types,
    })
  }
}

/// Defines top-level user-defined type
#[derive(Clone, Debug, PartialEq)]
pub struct Root {
  /// Name of top-level type
  pub name: TypeName,
  /// Definition of type
  pub type_: Type,
}
impl TryFrom<p::Ksy> for Root {
  type Error = ModelError;

  fn try_from(data: p::Ksy) -> Result<Self, Self::Error> {
    use p::Identifier::*;

    let name = match data.meta.id {
      None              => TypeName::valid("root"),
      Some(Bool(true))  => TypeName::valid("r#true"),
      Some(Bool(false)) => TypeName::valid("r#false"),
      Some(Name(name))  => TypeName::validate(name)?,
    };
    let type_ = Type::validate(data.root, data.meta.defaults.into())?;

    Ok(Self { name, type_ })
  }
}

#[cfg(test)]
mod size {
  // Colorful diffs in assertions
  use pretty_assertions::assert_eq;
  use super::*;
  use indexmap::indexmap;

  #[test]
  fn size() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: test
    seq:
      - id: field
        size: 5
    "#).unwrap();
    let root = Root::try_from(ksy).expect("`size` defines size");
    assert_eq!(root, Root {
      name: TypeName::valid("test"),
      type_: Type {
        fields: indexmap![
          SeqName::Named(Name::valid("field")) => Chunk {
            type_ref: TypeRef::Bytes,
            size: 5.into(),
          }.into(),
        ],
        ..Default::default()
      }
    });
  }
  #[test]
  fn size_eos() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: test
    seq:
      - id: field
        size-eos: true
    "#).unwrap();
    let root = Root::try_from(ksy).expect("`size-eos` defines size");
    assert_eq!(root, Root {
      name: TypeName::valid("test"),
      type_: Type {
        fields: indexmap![
          SeqName::Named(Name::valid("field")) => Chunk {
            type_ref: TypeRef::Bytes,
            size: Size::Eos(None),
          }.into(),
        ],
        ..Default::default()
      }
    });
  }
  #[test]
  fn terminator() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: test
    seq:
      - id: field
        terminator: 5
    "#).unwrap();
    let root = Root::try_from(ksy).expect("`terminator` defines size");
    assert_eq!(root, Root {
      name: TypeName::valid("test"),
      type_: Type {
        fields: indexmap![
          SeqName::Named(Name::valid("field")) => Chunk {
            type_ref: TypeRef::Bytes,
            size: Size::Until(5.into()),
          }.into(),
        ],
        ..Default::default()
      }
    });
  }
  #[test]
  fn strz() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: test
    seq:
      - id: field
        type: strz
        encoding: UTF-8
    "#).unwrap();
    let root = Root::try_from(ksy).expect("`strz` defines size (because of implicit `terminator=0`)");
    assert_eq!(root, Root {
      name: TypeName::valid("test"),
      type_: Type {
        fields: indexmap![
          SeqName::Named(Name::valid("field")) => Chunk {
            type_ref: TypeRef::String("UTF-8".into()),
            size: Size::Until(0.into()),
          }.into(),
        ],
        ..Default::default()
      }
    });
  }
  #[test]
  fn builtin_types() {
    use p::Endian::*;
    use Enumerable::*;
    use Variant::*;

    macro_rules! test {
      ($builtin:ident, $size:literal, $base:expr) => {
        let ksy: p::Ksy = serde_yaml::from_str(&format!(r#"
        meta:
          id: test
          endian: be
        seq:
          - id: field
            type: {}
        "#, stringify!($builtin))).unwrap();
        let root = Root::try_from(ksy).expect(&format!("`{}` has natural size", stringify!($builtin)));
        assert_eq!(root, Root {
          name: TypeName::valid("test"),
          type_: Type {
            fields: indexmap![
              SeqName::Named(Name::valid("field")) => Chunk {
                type_ref: $base,
                size: Size::Natural,
              }.into(),
            ],
            ..Default::default()
          }
        });
        match &root.type_.fields[&SeqName::Named(FieldName::valid("field"))].chunk {
          Variant::Fixed(chunk) => assert_eq!(chunk.type_ref.sizeof(), SizeOf::Sized($size.into())),
          _ => assert!(false),
        }
      };
    }
    test!(u1, 1usize, TypeRef::Enum { base: U8, enum_: None });
    test!(u2, 2usize, TypeRef::Enum { base: U16(Fixed(Be)), enum_: None });
    test!(u4, 4usize, TypeRef::Enum { base: U32(Fixed(Be)), enum_: None });
    test!(u8, 8usize, TypeRef::Enum { base: U64(Fixed(Be)), enum_: None });

    test!(s1, 1usize, TypeRef::Enum { base: I8, enum_: None });
    test!(s2, 2usize, TypeRef::Enum { base: I16(Fixed(Be)), enum_: None });
    test!(s4, 4usize, TypeRef::Enum { base: I32(Fixed(Be)), enum_: None });
    test!(s8, 8usize, TypeRef::Enum { base: I64(Fixed(Be)), enum_: None });

    test!(f4, 4usize, TypeRef::F32(Fixed(Be)));
    test!(f8, 8usize, TypeRef::F64(Fixed(Be)));
    //----------------------
    test!(u2be, 2usize, TypeRef::Enum { base: U16(Fixed(Be)), enum_: None });
    test!(u4be, 4usize, TypeRef::Enum { base: U32(Fixed(Be)), enum_: None });
    test!(u8be, 8usize, TypeRef::Enum { base: U64(Fixed(Be)), enum_: None });

    test!(s2be, 2usize, TypeRef::Enum { base: I16(Fixed(Be)), enum_: None });
    test!(s4be, 4usize, TypeRef::Enum { base: I32(Fixed(Be)), enum_: None });
    test!(s8be, 8usize, TypeRef::Enum { base: I64(Fixed(Be)), enum_: None });

    test!(f4be, 4usize, TypeRef::F32(Fixed(Be)));
    test!(f8be, 8usize, TypeRef::F64(Fixed(Be)));
    //----------------------
    test!(u2le, 2usize, TypeRef::Enum { base: U16(Fixed(Le)), enum_: None });
    test!(u4le, 4usize, TypeRef::Enum { base: U32(Fixed(Le)), enum_: None });
    test!(u8le, 8usize, TypeRef::Enum { base: U64(Fixed(Le)), enum_: None });

    test!(s2le, 2usize, TypeRef::Enum { base: I16(Fixed(Le)), enum_: None });
    test!(s4le, 4usize, TypeRef::Enum { base: I32(Fixed(Le)), enum_: None });
    test!(s8le, 8usize, TypeRef::Enum { base: I64(Fixed(Le)), enum_: None });

    test!(f4le, 4usize, TypeRef::F32(Fixed(Le)));
    test!(f8le, 8usize, TypeRef::F64(Fixed(Le)));
  }
}

#[cfg(test)]
mod strz {
  use super::*;

  #[test]
  fn fixed() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: strz_without_size
    seq:
      - id: field
        type: strz
        encoding: UTF-8
    "#).unwrap();
    let _ = Root::try_from(ksy).expect("`strz` not requires explicit size");
  }

  #[test]
  fn choice() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: strz_without_size
    seq:
      - id: field
        type:
          switch-on: 1
          cases:
            1: strz
            2: u4be
        encoding: UTF-8
    "#).unwrap();
    let _ = Root::try_from(ksy).expect("`strz` not requires explicit size");
  }
}

#[cfg(test)]
mod encoding {
  macro_rules! tests {
    ($type_name:ident) => {
      mod $type_name {
        #[test]
        fn simple() {
          use std::convert::TryFrom;
          let ksy: crate::parser::Ksy = serde_yaml::from_str(&format!(r#"
          meta:
            id: missing_encoding
          seq:
            - id: field
              type: {}
              size: 1
          "#, stringify!($type_name))).unwrap();
          let _ = crate::model::Root::try_from(ksy).expect_err(&format!("`{}` requires `encoding`", stringify!($type_name)));
        }

        #[test]
        fn choice() {
          use std::convert::TryFrom;
          let ksy: crate::parser::Ksy = serde_yaml::from_str(&format!(r#"
          meta:
            id: missing_encoding
          seq:
            - id: field
              type:
                switch-on: 1
                cases:
                  1: {}
                  2: u1
              size: 1
          "#, stringify!($type_name))).unwrap();
          let _ = crate::model::Root::try_from(ksy).expect_err(&format!("`{}` requires `encoding`", stringify!($type_name)));
        }
      }
    };
  }

  tests!(str);
  tests!(strz);
}

#[cfg(test)]
mod inheritance {
  use super::*;

  macro_rules! test_encoding_and_endian {
    ($name:ident, $template:expr) => {
      #[test]
      fn $name() {
        macro_rules! test {
          ($builtin:expr) => {
            let s = stringify!($builtin);
            let t = &format!($template, s);
            let ksy: p::Ksy = serde_yaml::from_str(t).unwrap();
            let _ = Root::try_from(ksy).expect(&format!("inherited `encoding` and `endian` for `{}`\n{}", s, t));
          };
        }
        test!(u1);
        test!(u2);
        test!(u4);
        test!(u8);

        test!(s1);
        test!(s2);
        test!(s4);
        test!(s8);

        test!(f4);
        test!(f8);
        //----------------------
        test!(u2be);
        test!(u4be);
        test!(u8be);

        test!(s2be);
        test!(s4be);
        test!(s8be);

        test!(f4be);
        test!(f8be);
        //----------------------
        test!(u2le);
        test!(u4le);
        test!(u8le);

        test!(s2le);
        test!(s4le);
        test!(s8le);

        test!(f4le);
        test!(f8le);

        test!(user_type);
      }
    };
  }

  test_encoding_and_endian!(simple, r#"
    meta:
      id: simple
      encoding: UTF-8
      endian: be
    seq:
      - id: field
        type: {}
  "#);

  test_encoding_and_endian!(sub_type, r#"
    meta:
      id: sub_type
      encoding: UTF-8
      endian: be
    types:
      type:
        seq:
          - id: field
            type: {}
  "#);

  test_encoding_and_endian!(meta_in_sub_type, r#"
    meta:
      id: meta_in_sub_type
    types:
      type:
        meta:
          encoding: UTF-8
          endian: be
        seq:
          - id: field
            type: {}
  "#);

  mod switch_on_type {
    use super::*;

    test_encoding_and_endian!(with_sized, r#"
      meta:
        id: switch_on_type
        encoding: UTF-8
        endian: be
      seq:
        - id: field
          type:
            switch-on: 1
            cases:
              1: {}
              2: u1 # sized type
    "#);
    test_encoding_and_endian!(with_unsized, r#"
      meta:
        id: switch_on_type
        encoding: UTF-8
        endian: be
      seq:
        - id: field
          type:
            switch-on: 1
            cases:
              1: {}
              2: strz # unsized type
    "#);
    test_encoding_and_endian!(with_unknown_sized, r#"
      meta:
        id: switch_on_type
        encoding: UTF-8
        endian: be
      seq:
        - id: field
          type:
            switch-on: 1
            cases:
              1: {}
              2: unknown_sized
    "#);
  }
}

#[cfg(test)]
mod duplicate {
  use super::*;

  #[test]
  fn fields() {
    let ksy: p::Ksy = serde_yaml::from_str(r#"
    meta:
      id: duplicate_fields
    seq:
      - id: field
        size: 1
      - id: field
        size: 2
    "#).unwrap();
    let _ = Root::try_from(ksy).expect_err("duplicated fields must raise error");
  }
}

/// Tests for `_sizeof` property / `sizeof<>` property
#[cfg(test)]
mod sizeof {
  // Colorful diffs in assertions
  use pretty_assertions::assert_eq;
  use super::*;
  use SizeOf::*;

  const BE: ByteOrder = ByteOrder::Fixed(p::Endian::Be);
  const LE: ByteOrder = ByteOrder::Fixed(p::Endian::Le);

  #[test]
  fn add() {
    // Unknown + ...
    assert_eq!(
      Unknown + Unknown,
      Unknown
    );
    assert_eq!(
      Unknown + Sized(42usize.into()),
      Unknown
    );
    assert_eq!(
      Unknown + Unsized(42usize.into(), None),
      Unknown
    );
    assert_eq!(
      Unknown + Unsized(42usize.into(), Some(100usize.into())),
      Unknown
    );

    // Sized + ...
    assert_eq!(
      Sized(10usize.into()) + Unknown,
      Unknown
    );
    assert_eq!(// 10 + 42 = 52
      Sized(10usize.into()) + Sized(42usize.into()),
      Sized(52usize.into())
    );
    assert_eq!(// 10 + (42..) = (52..)
      Sized(10usize.into()) + Unsized(42usize.into(), None),
      Unsized(52usize.into(), None)
    );
    assert_eq!(// 10 + (42..=100) = (52..=110)
      Sized(10usize.into()) + Unsized(42usize.into(), Some(100usize.into())),
      Unsized(52usize.into(), Some(110usize.into()))
    );

    // Unsized + ...
    assert_eq!(
      Unsized(10usize.into(), None) + Unknown,
      Unknown
    );
    assert_eq!(// (10..) + 42 = (52..)
      Unsized(10usize.into(), None) + Sized(42usize.into()),
      Unsized(52usize.into(), None)
    );
    assert_eq!(// (10..) + (42..) = (52..)
      Unsized(10usize.into(), None) + Unsized(42usize.into(), None),
      Unsized(52usize.into(), None)
    );
    assert_eq!(// (10..) + (42..=100) = (52..)
      Unsized(10usize.into(), None) + Unsized(42usize.into(), Some(100usize.into())),
      Unsized(52usize.into(), None)
    );

    // Unsized + ...
    assert_eq!(
      Unsized(10usize.into(), Some(50usize.into())) + Unknown,
      Unknown
    );
    assert_eq!(// (10..=50) + 42 = (52..=92)
      Unsized(10usize.into(), Some(50usize.into())) + Sized(42usize.into()),
      Unsized(52usize.into(), Some(92usize.into()))
    );
    assert_eq!(// (10..=50) + (42..) = (52..)
      Unsized(10usize.into(), Some(50usize.into())) + Unsized(42usize.into(), None),
      Unsized(52usize.into(), None)
    );
    assert_eq!(// (10..=50) + (42..=100) = (52..=150)
      Unsized(10usize.into(), Some(50usize.into())) + Unsized(42usize.into(), Some(100usize.into())),
      Unsized(52usize.into(), Some(150usize.into()))
    );
  }

  #[test]
  fn or() {
    // Unknown .or ...
    assert_eq!(
      SizeOf::or(
        Unknown,
        Unknown
      ),
      Unknown
    );
    assert_eq!(
      SizeOf::or(
        Unknown,
        Sized(42usize.into())
      ),
      Unknown
    );
    assert_eq!(
      SizeOf::or(
        Unknown,
        Unsized(42usize.into(), None)
      ),
      Unknown
    );
    assert_eq!(
      SizeOf::or(
        Unknown,
        Unsized(42usize.into(), Some(100usize.into()))
      ),
      Unknown
    );

    //-------------------------------------------------------------------------
    // Sized .or ...
    assert_eq!(
      SizeOf::or(
        Sized(10usize.into()),
        Unknown
      ),
      Unknown
    );
    assert_eq!(// 10 .or 42 = 10..=42
      SizeOf::or(
        Sized(10usize.into()),
        Sized(42usize.into())
      ),
      Unsized(10usize.into(), Some(42usize.into()))
    );
    assert_eq!(// 42 .or 10 = 10..=42
      SizeOf::or(
        Sized(42usize.into()),
        Sized(10usize.into())
      ),
      Unsized(10usize.into(), Some(42usize.into()))
    );

    assert_eq!(// 10 .or (42..) = (10..)
      SizeOf::or(
        Sized(10usize.into()),
        Unsized(42usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// 42 .or (10..) = (10..)
      SizeOf::or(
        Sized(42usize.into()),
        Unsized(10usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );

    assert_eq!(// 10 .or (42..=50) = (10..=50)
      SizeOf::or(
        Sized(10usize.into()),
        Unsized(42usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );
    assert_eq!(// 42 .or (10..=50) = (10..=50)
      SizeOf::or(
        Sized(42usize.into()),
        Unsized(10usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );
    assert_eq!(// 50 .or (10..=42) = (10..=50)
      SizeOf::or(
        Sized(50usize.into()),
        Unsized(10usize.into(), Some(42usize.into()))
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );

    //-------------------------------------------------------------------------
    // Unsized .or ...
    assert_eq!(
      SizeOf::or(
        Unsized(10usize.into(), None),
        Unknown
      ),
      Unknown
    );

    assert_eq!(// (10..) .or 42 = (10..)
      SizeOf::or(
        Unsized(10usize.into(), None),
        Sized(42usize.into())
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (42..) .or 10 = (10..)
      SizeOf::or(
        Unsized(42usize.into(), None),
        Sized(10usize.into())
      ),
      Unsized(10usize.into(), None)
    );

    assert_eq!(// (10..) .or (42..) = (10..)
      SizeOf::or(
        Unsized(10usize.into(), None),
        Unsized(42usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (42..) .or (10..) = (10..)
      SizeOf::or(
        Unsized(42usize.into(), None),
        Unsized(10usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );

    assert_eq!(// (10..) .or (42..=50) = (10..)
      SizeOf::or(
        Unsized(10usize.into(), None),
        Unsized(42usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (42..) .or (10..=50) = (10..)
      SizeOf::or(
        Unsized(42usize.into(), None),
        Unsized(10usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (50..) .or (10..=42) = (10..)
      SizeOf::or(
        Unsized(50usize.into(), None),
        Unsized(10usize.into(), Some(42usize.into()))
      ),
      Unsized(10usize.into(), None)
    );

    //-------------------------------------------------------------------------
    // Unsized .or ...
    assert_eq!(
      SizeOf::or(
        Unsized(10usize.into(), Some(50usize.into())),
        Unknown
      ),
      Unknown
    );

    assert_eq!(// (42..=50) .or 10 = (10..=50)
      SizeOf::or(
        Unsized(42usize.into(), Some(50usize.into())),
        Sized(10usize.into())
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );
    assert_eq!(// (10..=50) .or 42 = (10..=50)
      SizeOf::or(
        Unsized(10usize.into(), Some(50usize.into())),
        Sized(42usize.into())
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );
    assert_eq!(// (10..=42) .or 50 = (10..=50)
      SizeOf::or(
        Unsized(10usize.into(), Some(42usize.into())),
        Sized(50usize.into())
      ),
      Unsized(10usize.into(), Some(50usize.into()))
    );

    assert_eq!(// (42..=50) .or (10..) = (10..)
      SizeOf::or(
        Unsized(42usize.into(), Some(50usize.into())),
        Unsized(10usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (10..=50) .or (42..) = (10..)
      SizeOf::or(
        Unsized(10usize.into(), Some(50usize.into())),
        Unsized(42usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );
    assert_eq!(// (10..=42) .or (50..) = (10..)
      SizeOf::or(
        Unsized(10usize.into(), Some(42usize.into())),
        Unsized(50usize.into(), None)
      ),
      Unsized(10usize.into(), None)
    );

    // [    ]
    //         (    )
    // [            ]
    assert_eq!(// (10..=42) .or (50..=100) = (10..=100)
      SizeOf::or(
        Unsized(10usize.into(), Some(42usize.into())),
        Unsized(50usize.into(), Some(100usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
    // [       ]
    //      (       )
    // [            ]
    assert_eq!(// (10..=50) .or (42..=100) = (10..=100)
      SizeOf::or(
        Unsized(10usize.into(), Some(50usize.into())),
        Unsized(42usize.into(), Some(100usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
    // [            ]
    //      (  )
    // [            ]
    assert_eq!(// (10..=100) .or (42..=50) = (10..=100)
      SizeOf::or(
        Unsized(10usize.into(), Some(100usize.into())),
        Unsized(42usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
    //      [  ]
    // (            )
    // [            ]
    assert_eq!(// (42..=50) .or (10..=100) = (10..=100)
      SizeOf::or(
        Unsized(42usize.into(), Some(50usize.into())),
        Unsized(10usize.into(), Some(100usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
    //      [       ]
    // (       )
    // [            ]
    assert_eq!(// (42..=100) .or (10..=50) = (10..=100)
      SizeOf::or(
        Unsized(42usize.into(), Some(100usize.into())),
        Unsized(10usize.into(), Some(50usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
    //         [    ]
    // (    )
    // [            ]
    assert_eq!(// (50..=100) .or (10..=42) = (10..=100)
      SizeOf::or(
        Unsized(50usize.into(), Some(100usize.into())),
        Unsized(10usize.into(), Some(42usize.into()))
      ),
      Unsized(10usize.into(), Some(100usize.into()))
    );
  }

  /// Tests calculation of size of the built-in types
  #[test]
  fn builtin() {
    macro_rules! check_size {
      ($variant:ident == $size:literal) => {
        let type_ref = TypeRef::Enum { base: Enumerable::$variant(BE), enum_: None };
        assert_eq!(type_ref.sizeof(), Sized($size.into()));

        let type_ref = TypeRef::Enum { base: Enumerable::$variant(LE), enum_: None };
        assert_eq!(type_ref.sizeof(), Sized($size.into()));
      };
    }

    let type_ref = TypeRef::Enum { base: Enumerable::U8, enum_: None };
    assert_eq!(type_ref.sizeof(), Sized(1usize.into()));

    let type_ref = TypeRef::Enum { base: Enumerable::I8, enum_: None };
    assert_eq!(type_ref.sizeof(), Sized(1usize.into()));

    check_size!(U16 == 2usize);
    check_size!(I16 == 2usize);

    check_size!(U32 == 4usize);
    check_size!(I32 == 4usize);

    check_size!(U64 == 8usize);
    check_size!(I64 == 8usize);

    //---------------------------------------------------------------------------------------------

    let type_ref = TypeRef::F32(BE);
    assert_eq!(type_ref.sizeof(), Sized(4usize.into()));

    let type_ref = TypeRef::F32(LE);
    assert_eq!(type_ref.sizeof(), Sized(4usize.into()));

    let type_ref = TypeRef::F64(BE);
    assert_eq!(type_ref.sizeof(), Sized(8usize.into()));

    let type_ref = TypeRef::F64(LE);
    assert_eq!(type_ref.sizeof(), Sized(8usize.into()));

    //---------------------------------------------------------------------------------------------

    let type_ref = TypeRef::Bytes;
    assert_eq!(type_ref.sizeof(), Unsized(0usize.into(), None));

    let type_ref = TypeRef::String("UTF-8".into());
    assert_eq!(type_ref.sizeof(), Unsized(0usize.into(), None));

    let type_ref = TypeRef::Fixed(b"12345".to_vec());
    assert_eq!(type_ref.sizeof(), Sized(5usize.into()));
  }

  mod chunk {
    // Colorful diffs in assertions - resolve ambiguous
    use pretty_assertions::assert_eq;
    use super::*;

    macro_rules! limited_check_size {
      ($fn:ident, $variant:ident == $size:expr) => {
        assert_eq!(
          chunk_size(TypeRef::Enum { base: Enumerable::$variant(BE), enum_: None }),
          Sized($size.into()),
        );
        assert_eq!(
          chunk_size(TypeRef::Enum { base: Enumerable::$variant(LE), enum_: None }),
          Sized($size.into()),
        );
      };
    }
    macro_rules! limited {
      ($fn:ident, $count:expr) => {
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::U8, enum_: None }),
          Sized($count.into()),
        );
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::I8, enum_: None }),
          Sized($count.into()),
        );

        limited_check_size!($fn, U16 == $count * 2);
        limited_check_size!($fn, I16 == $count * 2);

        limited_check_size!($fn, U32 == $count * 4);
        limited_check_size!($fn, I32 == $count * 4);

        limited_check_size!($fn, U64 == $count * 8);
        limited_check_size!($fn, I64 == $count * 8);

        //---------------------------------------------------------------------------------------------

        assert_eq!($fn(TypeRef::F32(BE)), Sized(($count * 4).into()));
        assert_eq!($fn(TypeRef::F32(LE)), Sized(($count * 4).into()));

        assert_eq!($fn(TypeRef::F64(BE)), Sized(($count * 8).into()));
        assert_eq!($fn(TypeRef::F64(LE)), Sized(($count * 8).into()));

        //---------------------------------------------------------------------------------------------

        assert_eq!($fn(TypeRef::Fixed(b"12345".to_vec())), Sized(($count * 5).into()));
      };
    }

    macro_rules! unlimited_check_size {
      ($fn:ident, $variant:ident == $size:literal) => {
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::$variant(BE), enum_: None }),
          Unsized($size.into(), None),
        );
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::$variant(LE), enum_: None }),
          Unsized($size.into(), None),
        );
      };
    }
    macro_rules! unlimited {
      ($fn:ident) => {
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::U8, enum_: None }),
          Unsized(1usize.into(), None),
        );
        assert_eq!(
          $fn(TypeRef::Enum { base: Enumerable::I8, enum_: None }),
          Unsized(1usize.into(), None),
        );

        unlimited_check_size!($fn, U16 == 2usize);
        unlimited_check_size!($fn, I16 == 2usize);

        unlimited_check_size!($fn, U32 == 4usize);
        unlimited_check_size!($fn, I32 == 4usize);

        unlimited_check_size!($fn, U64 == 8usize);
        unlimited_check_size!($fn, I64 == 8usize);

        //---------------------------------------------------------------------------------------------

        assert_eq!($fn(TypeRef::F32(BE)), Unsized(4usize.into(), None));
        assert_eq!($fn(TypeRef::F32(LE)), Unsized(4usize.into(), None));

        assert_eq!($fn(TypeRef::F64(BE)), Unsized(8usize.into(), None));
        assert_eq!($fn(TypeRef::F64(LE)), Unsized(8usize.into(), None));

        //---------------------------------------------------------------------------------------------

        assert_eq!($fn(TypeRef::Bytes),                    Unsized(0usize.into(), None));
        assert_eq!($fn(TypeRef::String("UTF-8".into())),   Unsized(0usize.into(), None));
        assert_eq!($fn(TypeRef::Fixed(b"12345".to_vec())), Unsized(5usize.into(), None));
      };
    }

    /// Natural-sized chunks should return `sizeof` of their type.
    ///
    /// Corresponds to:
    /// ```yaml
    /// type: ...
    /// ```
    #[test]
    fn natural() {
      fn chunk_size(type_ref: TypeRef) -> SizeOf {
        let chunk = Chunk {
          type_ref,
          size: Size::Natural,
        };
        chunk.sizeof()
      }

      limited!(chunk_size, 1usize);
      assert_eq!(chunk_size(TypeRef::Bytes),                  Unsized(0usize.into(), None));
      assert_eq!(chunk_size(TypeRef::String("UTF-8".into())), Unsized(0usize.into(), None));
    }

    /// All chunks that extends to the end-of-stream have unlimited size, but at least
    /// the size of the type because otherwise parsing will fail
    ///
    /// Corresponds to:
    /// ```yaml
    /// size-eos: true
    /// ```
    #[test]
    fn eos() {
      fn chunk_size(type_ref: TypeRef) -> SizeOf {
        let chunk = Chunk {
          type_ref,
          size: Size::Eos(None),
        };
        chunk.sizeof()
      }

      unlimited!(chunk_size);
    }

    /// Corresponds to:
    /// ```yaml
    /// size-eos: true
    /// terminator: 0
    /// ```
    #[test]
    fn eos_until() {
      fn chunk_size(type_ref: TypeRef) -> SizeOf {
        let chunk = Chunk {
          type_ref,
          size: Size::Eos(Some(0x00.into())),
        };
        chunk.sizeof()
      }

      unlimited!(chunk_size);
    }

    /// Corresponds to:
    /// ```yaml
    /// terminator: 0
    /// ```
    #[test]
    fn until() {
      fn chunk_size(type_ref: TypeRef) -> SizeOf {
        let chunk = Chunk {
          type_ref,
          size: Size::Until(0x00.into()),
        };
        chunk.sizeof()
      }

      unlimited!(chunk_size);
    }

    /// Exact-sized chunks occupies that amount of space that defined in their `size`,
    /// no matter how much underlying type is occupy
    mod exact {
      // Colorful diffs in assertions - resolve ambiguous
      use pretty_assertions::assert_eq;
      use super::*;


      macro_rules! constant {
        ($fn:ident, $count:expr) => {
          assert_eq!(
            $fn(TypeRef::Enum { base: Enumerable::U8, enum_: None }),
            Sized($count.into()),
          );
          assert_eq!(
            $fn(TypeRef::Enum { base: Enumerable::I8, enum_: None }),
            Sized($count.into()),
          );

          limited_check_size!($fn, U16 == $count);
          limited_check_size!($fn, I16 == $count);

          limited_check_size!($fn, U32 == $count);
          limited_check_size!($fn, I32 == $count);

          limited_check_size!($fn, U64 == $count);
          limited_check_size!($fn, I64 == $count);

          //---------------------------------------------------------------------------------------------

          assert_eq!($fn(TypeRef::F32(BE)), Sized($count.into()));
          assert_eq!($fn(TypeRef::F32(LE)), Sized($count.into()));

          assert_eq!($fn(TypeRef::F64(BE)), Sized($count.into()));
          assert_eq!($fn(TypeRef::F64(LE)), Sized($count.into()));

          //---------------------------------------------------------------------------------------------

          assert_eq!($fn(TypeRef::Bytes),                    Sized($count.into()));
          assert_eq!($fn(TypeRef::String("UTF-8".into())),   Sized($count.into()));
          assert_eq!($fn(TypeRef::Fixed(b"12345".to_vec())), Sized($count.into()));
        };
      }

      /// Corresponds to:
      /// ```yaml
      /// size: constant
      /// ```
      #[test]
      fn constant() {
        const COUNT: usize = 42;

        fn chunk_size(type_ref: TypeRef) -> SizeOf {
          let chunk = Chunk {
            type_ref,
            size: Size::Exact {
              count: Count(COUNT.into()),
              until: None,
            },
          };
          chunk.sizeof()
        }

        constant!(chunk_size, COUNT);
      }

      /// Corresponds to:
      /// ```yaml
      /// size: constant
      /// terminal: 0
      /// ```
      #[test]
      fn constant_until() {
        const COUNT: usize = 42;

        fn chunk_size(type_ref: TypeRef) -> SizeOf {
          let chunk = Chunk {
            type_ref,
            size: Size::Exact {
              count: Count(COUNT.into()),
              until: Some(0x00.into()),
            },
          };
          chunk.sizeof()
        }

        constant!(chunk_size, COUNT);
      }

      /// Corresponds to:
      /// ```yaml
      /// size: expression
      /// ```
      #[test]
      fn expression() {
        fn chunk_size(type_ref: TypeRef) -> SizeOf {
          let chunk = Chunk {
            type_ref,
            size: Size::Exact {
              count: Count(OwningNode::Attr(FieldName::valid("x"))),
              until: None,
            },
          };
          chunk.sizeof()
        }

        unlimited!(chunk_size);
      }

      /// Corresponds to:
      /// ```yaml
      /// size: expression
      /// terminator: 0
      /// ```
      #[test]
      fn expression_until() {
        fn chunk_size(type_ref: TypeRef) -> SizeOf {
          let chunk = Chunk {
            type_ref,
            size: Size::Exact {
              count: Count(OwningNode::Attr(FieldName::valid("x"))),
              until: Some(0x00.into()),
            },
          };
          chunk.sizeof()
        }

        unlimited!(chunk_size);
      }
    }
  }
}
