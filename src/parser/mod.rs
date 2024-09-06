//! Contains structures, that reflects physical KSY file structure.
//!
//! Main goal of this structs -- make base checks. For actual dealing
//! with KSY file use types from [`model`] module.
//!
//! [`model`]: crate::model

// Colorful diffs in assertions
#[cfg(test)]
use pretty_assertions::assert_eq;

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use serde_yml::{Number, Value};

pub use doc::{Doc, DocRef, XRef, XRefs};
pub use names::{Name, ProcessAlgo, UserName};
pub use import::Import;
pub use r#enum::{Enum, EnumRef, EnumValue, EnumVariant};
pub use utils::{Expression, OneOrMany, Scalar, Variant};

mod doc;
mod r#enum;
pub mod expressions;
mod import;
mod names;
mod utils;

/// Variants of endianness of integer attribute types
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum ByteOrder {
  /// Little-Endian
  Le,
  /// Big-Endian
  Be,
}

/// Variants of bit order of bit-sized integers
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum BitOrder {
  /// Little-Endian
  Le,
  /// Big-Endian
  Be,
}

/// Set of possible validation rules supported by Kaitai Struct
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum ValidationRules {
  /// Shorthand syntax for [`ValidationRules::Checks::eq`].
  Eq(Scalar),
  /// List of possible checks. Only `min` and `max` checks can be used together
  /// in a valid KSY file, but that is enforced on model level. Parser model allows
  /// any combinations.
  #[serde(rename_all = "kebab-case")]
  Checks {
    /// Parsed value should be equal to the specified expression.
    ///
    /// Available special context variables: none
    eq: Option<Scalar>,

    /// Parsed value should be `>=` than the specified expression.
    /// This restriction can be combined with `max`.
    ///
    /// Available special context variables: none
    min: Option<Expression<Number>>,
    /// Parsed value should be `<=` than the specified expression.
    /// This restriction can be combined with `min`.
    ///
    /// Available special context variables: none
    max: Option<Expression<Number>>,

    /// Specified expression should evaluate to `true` for valid parsed value and
    /// to `false` for invalid.
    ///
    /// Available special context variables:
    ///
    /// |Variable|Meaning
    /// |--------|------------
    /// |[`_`]   |Parsed value
    ///
    /// [`_`]: crate::parser::expressions::SpecialName::Value
    expr: Option<Expression<bool>>,

    /// Parsed value should be equal to the any of specified expressions.
    /// Each check is the same as for [`eq`][`ValidationRules::Checks::eq`].
    any_of: Option<Vec<Scalar>>,

    /// Parsed value should represent a known element of a specified enumeration.
    in_enum: Option<EnumRef>,
  },
}

/// Represent one element of array content for [`contents`] key.
///
/// [`contents`]: Attribute::contents
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum StringOrByte {
  /// Data for `contents` key, expressed as string in UTF-8 encoding.
  String(String),//TODO: allow `encoding` key and interpret all strings in that encoding
  /// One byte of data for `contents` key.
  Byte(u8),
}
impl StringOrByte {
  /// Fills specified vector with bytes from current object
  fn into_bytes(self, buffer: &mut Vec<u8>) {
    match self {
      StringOrByte::String(s) => buffer.extend(s.into_bytes()),
      StringOrByte::Byte(b)   => buffer.push(b),
    }
  }
}

/// Represents fixed byte content
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Contents {//TODO: Заменить на OneOrMany<StringOrByte>
  /// Byte content as single UTF-8 encoded string
  Str(String),
  /// Byte content as array of individual bytes and UTF-8 encoded strings
  Vec(Vec<StringOrByte>),
}
impl From<Contents> for Vec<u8> {
  fn from(contents: Contents) -> Self {
    match contents {
      Contents::Str(s) => s.into(),
      Contents::Vec(v) => {
        let mut buf = Vec::new();
        for e in v {
          e.into_bytes(&mut buf);
        }
        buf
      }
    }
  }
}
/// List of all built-in types
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Builtin {
  /// 1-byte unsigned integer.
  u1,

  /// 2-byte unsigned integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  u2,
  /// 2-byte unsigned integer with big-endian byte order.
  ///
  /// ```text
  /// 0x0102 = [0x01, 0x02]
  /// ```
  u2be,
  /// 2-byte unsigned integer with little-endian byte order.
  ///
  /// ```text
  /// 0x0102 = [0x02, 0x01]
  /// ```
  u2le,

  /// 4-byte unsigned integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  u4,
  /// 4-byte unsigned integer with big-endian byte order.
  ///
  /// ```text
  /// 0x01020304 = [0x01, 0x02, 0x03, 0x04]
  /// ```
  u4be,
  /// 4-byte unsigned integer with little-endian byte order.
  ///
  /// ```text
  /// 0x01020304 = [0x04, 0x03, 0x02, 0x01]
  /// ```
  u4le,

  /// 8-byte unsigned integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  u8,
  /// 8-byte unsigned integer with big-endian byte order.
  ///
  /// ```text
  /// 0x0102030405060708 = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
  /// ```
  u8be,
  /// 8-byte unsigned integer with little-endian byte order.
  ///
  /// ```text
  /// 0x0102030405060708 = [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
  /// ```
  u8le,

  /// 1-byte signed integer.
  s1,

  /// 2-byte signed integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  s2,
  /// 2-byte signed integer with big-endian byte order.
  s2be,
  /// 2-byte signed integer with little-endian byte order.
  s2le,

  /// 4-byte signed integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  s4,
  /// 4-byte signed integer with big-endian byte order.
  s4be,
  /// 4-byte signed integer with little-endian byte order.
  s4le,

  /// 8-byte signed integer with [default endian](Defaults::endian).
  /// Can be used, only if `endian` is specified in one of surrounding types.
  s8,
  /// 8-byte signed integer with big-endian byte order.
  s8be,
  /// 8-byte signed integer with little-endian byte order.
  s8le,

  /// 4-byte floating point format that follows [IEEE 754] standard with [default endian].
  /// Can be used, only if `endian` is specified in one of surrounding types.
  /// Such type usually named `float` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  /// [default endian]: Defaults::endian
  f4,
  /// 4-byte floating point format that follows [IEEE 754] standard with big-endian byte order.
  /// Such type usually named `float` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  f4be,
  /// 4-byte floating point format that follows [IEEE 754] standard with little-endian byte order.
  /// Such type usually named `float` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  f4le,

  /// 8-byte floating point format that follows [IEEE 754] standard with [default endian].
  /// Can be used, only if `endian` is specified in one of surrounding types.
  /// Such type usually named `double` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  /// [default endian]: Defaults::endian
  f8,
  /// 8-byte floating point format that follows [IEEE 754] standard with big-endian byte order.
  /// Such type usually named `double` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  f8be,
  /// 8-byte floating point format that follows [IEEE 754] standard with little-endian byte order.
  /// Such type usually named `double` in programming languages.
  ///
  /// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
  f8le,

  /// String with length of [`size`] in [`encoding`].
  ///
  /// [`size`]: Attribute::size
  /// [`encoding`]: Attribute::encoding
  str,
  /// String with length of [`size`] in [`encoding`] terminated by `\0` symbol
  /// (aka C-string).
  ///
  /// [`size`]: Attribute::size
  /// [`encoding`]: Attribute::encoding
  strz,
}
/// Reference to type definition
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum TypeRef {
  /// Reference to built-in type
  Builtin(Builtin),
  /// Reference to user-defined type. If path contains only one element, then
  /// type definition is searched in this level and above, otherwise in this
  /// level and below.
  ///
  /// Pattern: `^([a-z][a-z0-9_]*::)*[a-z][a-z0-9_]*(\(.+\))?$`
  User(String),
}
/// Definition of attribute type.
pub type Type = Variant<TypeRef>;

/// Attribute repetition variants
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum Repeat {
  /// Repeat until the end of the current stream.
  Eos,
  /// Repeat as many times as specified in `repeat-expr`.
  Expr,
  /// Repeat until the expression in `repeat-until` becomes **`true`**.
  Until,
}

/// Expression used to represent repetition count.
///
/// Although repetition count never can be negative, we use a signed value here
/// in order to be able to parse negative literals and produce a better error on
/// the later stages of compilation
pub type Count = Expression<i64>;

/// Expression used to represent instance position
pub type Position = Expression<u64>;

/// Expression, that used in boolean contexts
pub type Condition = Expression<bool>;

/// Version of the Kaitai Struct Compiler (KSC).
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Version {
  /// Version, represented as number, for example `1.0`.
  Number(Number),
  /// Version, represented as string, for example `1.0-alpha`.
  String(String),
}

/// Default values for attributes and user-defined keys for types.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct Defaults {
  /// Sets a default string encoding for fields of the type.
  ///
  /// Contains a user-defined encoding scheme, for example `ASCII`, `UTF-8`, `UTF-16LE`,
  /// `UTF-16BE`, `UTF-32LE`, `UTF-32BE` or a Name from the [IANA character sets registry][iana].
  ///
  /// If set, `str` and `strz` data types will have their encoding by default set to this value.
  ///
  /// [iana]: https://www.iana.org/assignments/character-sets/character-sets.xhtml
  #[serde(skip_serializing_if = "Option::is_none")]
  pub encoding: Option<String>,// TODO: encoding-rs encodings
  /// Default endianness for all numeric fields in the type.
  ///
  /// If set, primitive data types like `u4` would be treated as aliases to `u4le` / `u4be`
  /// (depending on the setting); if not set, attempt to use abbreviated types like `u4`
  /// (i.e. without full endianness qualifier) will yield compile-time error.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub endian: Option<Variant<ByteOrder>>,
  /// Default bit endianness for all bitwise fields in the type.
  ///
  /// If set, primitive bitwise types (`bX`) would be treated as aliases to `bXle` / `bXbe`
  /// (depending on the setting); if not set, the default big-endian will be used.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub bit_endian: Option<BitOrder>,

  /// Additional arbitrary values.
  #[serde(flatten)]
  pub other: IndexMap<UserName, Value>,
}

/// Meta-information relevant the user-defined type or KSY file in whole.
/// It also can be used to assign some defaults and provide some configuration
/// options for compiler.
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct MetaSpec {//TODO: json: разделить информацию в схеме
  /// Default values for all attributes in this file.
  #[serde(flatten)]
  pub defaults: Defaults,
  /// Identifier for a primary structure described in top-level map.
  ///
  /// It would be converted to suit general formatting rules of a language
  /// and used as the name of class.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub id: Option<Name>,
  /// Free-form text string that is a longer title of this `.ksy` file.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub title: Option<String>,
  /// Free-form text string that describes applications that's associated with
  /// this particular format.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub application: Option<OneOrMany<String>>,
  /// Roughly identify which files can be parsed with this format by filename extension.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub file_extension: Option<OneOrMany<String>>,
  /// Список ссылок на нормативные документы, описывающие формат
  #[serde(skip_serializing_if = "Option::is_none")]
  pub xref: Option<XRefs>,
  /// A string which matches one of the identifiers within the [SPDX license list][licenses].
  ///
  /// [licenses]: https://spdx.org/licenses/
  #[serde(skip_serializing_if = "Option::is_none")]
  pub license: Option<String>,//TODO: Add SPDX validation

  /// List of relative or absolute paths to another `.ksy` files to import
  /// (**without** the `.ksy` extension).
  ///
  /// The top-level type of the imported file will be accessible in the current spec under
  /// the name specified in the top-level `/meta/id` of the imported file.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub imports: Option<Vec<Import>>,

  /// A string which contains a minimum version of Kaitai Struct Compiler (KSC) required
  /// to interpret this `.ksy` file. Prevents this `.ksy` file from being read by older
  /// versions of KSC which may not understand newer syntax of this `.ksy` file.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub ks_version: Option<Version>,
  /// Advise the Kaitai Struct Compiler (KSC) to use debug mode.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub ks_debug: Option<bool>,
  /// Advise the Kaitai Struct Compiler (KSC) to ignore missing types in the `.ksy` file,
  /// and assume that these types are already provided externally by the environment the
  /// classes are generated for.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub ks_opaque_types: Option<bool>,//TODO: Удалить. Нужно всегда явно импортировать нужные типы
}

/// Attribute specification describes how to read and write one particular attribute —
/// typically, a single number, a string, array of bytes, etc. Attribute can also be
/// a complex structure, specified with a [User-defined type spec][type]. Each attribute
/// is typically compiled into equivalent reading / writing instruction(s) in target language.
///
/// Every attribute MUST BE a map that maps certain keys to values. Some of these keys
/// are common to every possible attribute spec, some are only valid for certain types.
///
/// # Examples:
///
/// ```yaml
/// id: coord_x
/// type: f8
/// doc: X coordinate of a node.
/// ```
/// ```yaml
/// id: body_len_64
/// type: u8
/// if: body_len_32 == 0
/// doc: |
///   Additional value that designates length of the body as 64-bit
///   integer. To save space in common cases where 32-bit store is enough,
///   present only if `body_len_32` is set to 0.
/// ```
/// ```yaml
/// id: body
/// type: encoded_body
/// size: (body_len_32 == 0) ? body_len_64 : body_len_32
/// process: zlib
/// ```
///
/// [type]: TypeSpec
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct Attribute {
  /// Contains a string used to identify one attribute among others.
  ///
  /// If not specified, then that attribute will not be accessible,
  /// unless debug mode is enabled. In that case attribute give a some unspecified
  /// unique (in that type) name.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub id: Option<Name>,

  /// Documentation for an attribute.
  #[serde(flatten)]
  pub doc: Doc,

  /// Specify fixed contents that the parser should encounter at this point.
  /// If the content of the stream doesn't match the given bytes, an error is
  /// thrown and it's meaningless to continue parsing
  #[serde(skip_serializing_if = "Option::is_none")]
  pub contents: Option<Contents>,

  /// Defines data type for an attribute.
  ///
  /// The type can also be user-defined in the [`types`] key.
  ///
  /// One can reference a nested user-defined type by specifying a relative
  /// [path] to it from the current type, with a double colon as a path delimiter
  /// (e.g. `foo::bar::my_type`).
  ///
  /// # Type resolution
  ///
  /// If type is used to reference a [User-defined type spec][type], then the
  /// following algorithm it used to find which type is referred to, given the name:
  ///
  /// 1. It tries to find a given type by name in current type's [`types`] — declaration
  ///    of subtypes map.
  /// 2. If that fails, it checks if current type actually has that name and if it does,
  ///    uses current type recursively. Both type names given using a key in [`types`] —
  ///    declaration of subtypes and type name of top-level type given with [`meta/id`] work.
  ///
  /// If that fails too, it goes one level up in the hierarchy of nested types and
  /// tries to resolve it there.
  ///
  /// This mechanism is similar to the type name resolution algorithm that is used by C++,
  /// Java, Ruby, etc, and allows one to effectively use types as namespaces for subtypes,
  /// i.e. for example, this is legal:
  ///
  /// ```yaml
  /// meta
  ///   id: top_level
  /// seq:
  ///   - id: foo
  ///     type: header
  ///     # resolves to /top_level/header ──┐
  ///   - id: bar     #                     │
  ///     type: body1 #                     │
  ///   - id: baz     #                     │
  ///     type: body2 #                     │
  /// types:          #                     │
  ///   header: # ... <─────────────────────┘ <─┐
  ///   body1:             #                    │
  ///     seq:             #                    │
  ///       - id: foo      #                    │
  ///         type: header #                    │
  ///         # resolves to /top_level/header ──┘
  ///   body2:
  ///     seq:
  ///       - id: foo
  ///         type: header
  ///         # resolves to /top_level/second_level/header ──┐
  ///     types: #                                           │
  ///       header: # ... <──────────────────────────────────┘
  /// ```
  ///
  /// [`types`]: TypeSpec::types
  /// [path]: Type::User
  /// [type]: TypeSpec
  /// [`meta/id`]: MetaSpec::id
  #[serde(rename = "type")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub type_: Option<Type>,

  /// Designates repeated attribute in a structure.
  ///
  /// Attribute would be read as array / list / sequence, executing parsing
  /// code multiple times.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub repeat: Option<Repeat>,//TODO: сделать необязательным (https://github.com/kaitai-io/kaitai_struct/issues/776)
  /// Specify number of repetitions for repeated attribute.
  ///
  /// If that key is specified, `repeat` key must be `Some(Repeat::Expr)` or `None`.
  ///
  /// Only this one or `repeat_until` key must be specified at same time.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub repeat_expr: Option<Count>,
  /// Specifies a condition to be checked **after** each parsed item, repeating
  /// while the expression is `false`.
  ///
  /// One can use `_` in the expression, which is a special **local** variable
  /// that references the last read element.
  ///
  /// If that key is specified, `repeat` key must be `Some(Repeat::Expr)` or `None`.
  ///
  /// Only this one or `repeat_expr` key must be specified at same time.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub repeat_until: Option<Condition>,

  /// Marks the attribute as optional (attribute is parsed only if the condition specified
  /// evaluates to `true`).
  #[serde(rename = "if")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub condition: Option<Condition>,

  /// The number of bytes to read, before `type` would be parsed.
  /// If `type` isn't defined, just byte array of specified size will be returned.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub size: Option<Count>,
  /// If `true`, reads all the bytes till the end of the stream.
  ///
  /// Default is `false`.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub size_eos: Option<bool>,

  /// Processes the byte buffer before access.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub process: Option<ProcessAlgo>,
  /// Name of existing enum field data type becomes given enum.
  #[serde(rename = "enum")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub enum_: Option<EnumRef>,

  /// Encoding, used for that attribute, if it has `str` or `strz` type.
  ///
  /// If not specified, default encoding from [`meta/encoding`] is applied.
  ///
  /// See more info at [`meta/encoding`] key description.
  ///
  /// [`meta/encoding`]: Defaults::encoding
  #[serde(skip_serializing_if = "Option::is_none")]
  pub encoding: Option<String>,
  /// Specify a byte which is the string or byte array padded with after the end up to the total size.
  ///
  /// Can be used only with `size` or `size-eos: true` (when the size is fixed).
  ///
  /// When `terminator`:
  /// - isn't specified, then the `pad-right` controls where the string ends (basically acts like a terminator)
  /// - is specified, padding comes after the terminator, not before. The value is terminated immediately after
  ///   the terminator occurs, so the `pad-right` has no effect on parsing and is only relevant for serialization
  #[serde(skip_serializing_if = "Option::is_none")]
  pub pad_right: Option<u8>,// TODO: add default to meta.pad_right

  /// String or byte array reading will stop when it encounters this byte
  ///
  /// Cannot be used with `type: strz` (which already implies `terminator: 0` -- null-terminated string)
  #[serde(skip_serializing_if = "Option::is_none")]
  pub terminator: Option<u8>,// TODO: add default to meta.terminator
  /// Specify if terminator byte should be "consumed" when reading
  ///
  /// If `true`: the stream pointer will point to the byte after the terminator byte
  /// If `false`: the stream pointer will point to the terminator byte itself
  ///
  /// Default is `true`
  #[serde(skip_serializing_if = "Option::is_none")]
  pub consume: Option<bool>,// TODO: add default to meta.consume
  /// Specifies if terminator byte should be considered part of the string read and thus be appended to it
  ///
  /// Default is `false`
  #[serde(skip_serializing_if = "Option::is_none")]
  pub include: Option<bool>,// TODO: add default to meta.include
  /// Allows the compiler to ignore the lack of a terminator if `eos-error` is disabled,
  /// string reading will stop at either:
  ///
  ///   1. terminator being encountered
  ///   2. end of stream is reached
  ///
  /// Default is `true`.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub eos_error: Option<bool>,// TODO: add default to meta.eos_error

  /// Expression that enforces parent type that will be accessible via [`_parent`]
  /// contextual variable in the expressions within fields of this type.
  ///
  /// [`_parent`]: crate::parser::expressions::SpecialName::Parent
  #[serde(skip_serializing_if = "Option::is_none")]
  pub parent: Option<Expression<bool>>,

  /// Rules for validation of parsed values. For attributes with repetitions
  /// validation performed for each element of a collection.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub valid: Option<ValidationRules>,

  /// Additional arbitrary values.
  #[serde(flatten)]
  pub other: IndexMap<UserName, Value>,
}

/// [`Attribute`] specialization for use in [`instances`].
///
/// [`instances`]: TypeSpec::instances
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct Instance {
  /// Instructions for parsing data.
  #[serde(flatten)]
  pub attr: Attribute,

  /// Specifies position at which the value should be parsed.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub pos: Option<Position>,
  /// Specifies an IO stream from which a value should be parsed.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub io: Option<String>,
  /// Overrides any reading & parsing. Instead, just calculates function specified in value
  /// and returns the result as this instance. Has many purposes
  #[serde(skip_serializing_if = "Option::is_none")]
  pub value: Option<Scalar>,
}

/// Definition of a single type parameter under [`params`] key.
///
/// [`params`]: TypeSpec::params
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct Param {
  /// Unique name of this parameter by which it can be referenced in expressions.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub id: Option<Name>,//TODO: why parameter id is optional? Parameters without name is useless
  /// Specifies "pure" type of the parameter, without any serialization details
  /// (like endianness, sizes, encodings).
  ///
  /// | Value                  | Description
  /// |------------------------|------------
  /// | `u1`, `u2`, `u4`, `u8` | unsigned integer
  /// | `s1`, `s2`, `s4`, `s8` | signed integer
  /// | `bX`                   | bit-sized integer (if `X` != 1)
  /// | `f4`, `f8`             | floating point number
  /// | `type` key missing<br>or `bytes` | byte array
  /// | `str`                  | string
  /// | `bool` (or `b1`)       | boolean
  /// | `struct`               | arbitrary KaitaiStruct-compatible user type
  /// | `io`                   | KaitaiStream-compatible IO stream
  /// | `any`                  | allow any type (if target language supports that)
  /// | other identifier       | user-defined type, without parameters<br>a nested type can be referenced with double colon (e.g. `type: 'foo::bar'`)
  ///
  /// One can specify arrays by appending `[]` after the type identifier
  /// (e.g. `type: u2[]`, `type: 'foo::bar[]'`, `type: struct[]` etc.)
  #[serde(rename = "type")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub type_: Option<String>,

  /// Documentation for parameter.
  #[serde(flatten)]
  pub doc: Doc,

  /// Path to an enum type (defined in the `enums` map), which will become
  /// the type of the parameter.
  ///
  /// Only integer-based enums are supported, so `type` must be an integer type
  /// (`type: uX`, `type: sX` or `type: bX`) for this property to work.
  ///
  /// You can use `enum` with `type: b1` as well: `b1` means a 1-bit **integer** (0 or 1)
  /// when used with `enum` (**not** a boolean).
  ///
  /// One can reference an enum type of a subtype by specifying a relative path
  /// to it from the current type, with a double colon as a path delimiter
  /// (e.g. `foo::bar::my_enum`)
  #[serde(rename = "enum")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub enum_: Option<EnumRef>,

  /// Additional arbitrary values.
  #[serde(flatten)]
  pub other: IndexMap<UserName, Value>,
}

/// User-defined type specification is an essential component of KSY specification.
/// It declares a single user-defined type, which may include:
/// - `meta` — meta-information
/// - `doc` — docstrings
/// - `seq` — sequence of attributes
/// - `instances` — calculated values
/// - `enums` — declaration of named constants
/// - `types` — declaration of subtypes
/// - `params` — declaration of parameters that can affect number and composition
///   of fields
///
/// # Note
/// User-defined type spec is recursive and can include other user-defined type specs
/// inside `types` element.
///
/// Any `.ksy` file is a single user-defined type (exactly the same as any nested subtypes),
/// with two minor differences:
/// - top-level type spec MUST include `meta/id` key that is used to give a name for
///   top-level type,
/// - all nested types MUST NOT have that key (as they already have a certain ID from
///   the map key name provided in types — declaration of subtypes)
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct TypeSpec {
  /// Defaults for attributes' parameters
  #[serde(rename = "meta")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub default: Option<Defaults>,
  /// Documentation for type.
  #[serde(flatten)]
  pub doc: Doc,

  /// List of type parameters, that can be used, for example, in field existence checks.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub params: Option<Vec<Param>>,
  /// List of enumeration types, defined inside this type. Each enumeration has its
  /// own unique name inside this type (however, that name must not be the same as
  /// names in `types` and `instances` keys of this type).
  #[serde(skip_serializing_if = "Option::is_none")]
  pub enums: Option<IndexMap<Name, Enum>>,
  /// List of used-defined types, defined inside this type. Each type has its
  /// own unique name inside this type (however, that name must not be the same as
  /// names in `enums` and `instances` keys of this type).
  #[serde(skip_serializing_if = "Option::is_none")]
  pub types: Option<IndexMap<Name, TypeSpec>>,

  /// The list of fields that this type consists of. The fields in the data stream
  /// are in the same order as they are declared here.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub seq: Option<Vec<Attribute>>,
  /// List of dynamic and calculated fields of this type. The position of these fields
  /// is not fixed in the type, and they may not even be physically represented in the
  /// data stream at all.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub instances: Option<IndexMap<Name, Instance>>,

  /// Expression that used to represent type as a string (typically by calling the
  /// `toString()` / `inspect` / `__repr__` / similar method or property).
  ///
  /// Usually used for debugging purposes / internal dumping mechanism.
  #[serde(skip_serializing_if = "Option::is_none")]
  pub to_string: Option<Expression<String>>,

  /// Additional arbitrary values.
  #[serde(flatten)]
  pub other: IndexMap<UserName, Value>,
}

/// Type representing the entire file
#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub struct Ksy {
  /// Meta-information about this file
  pub meta: MetaSpec,
  /// Root type in the file
  #[serde(flatten)]
  pub root: TypeSpec,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[test]
fn version() {
  let number: MetaSpec = serde_yml::from_str("
    ks-version: 1.0
  ").unwrap();
  assert_eq!(number, MetaSpec {
    ks_version: Some(Version::Number(1.0.into())),
    ..Default::default()
  });

  let string: MetaSpec = serde_yml::from_str("
    ks-version: 1.0-alpha
  ").unwrap();
  assert_eq!(string, MetaSpec {
    ks_version: Some(Version::String("1.0-alpha".into())),
    ..Default::default()
  });
}

#[test]
fn string_or_byte() {
  let string: StringOrByte = serde_yml::from_str("'one'").unwrap();
  assert_eq!(string, StringOrByte::String("one".to_owned()));

  let number: StringOrByte = serde_yml::from_str("2").unwrap();
  assert_eq!(number, StringOrByte::Byte(2));

  let string_array: Vec<StringOrByte> = serde_yml::from_str("[one, 'two']").unwrap();
  assert_eq!(string_array, vec![
    StringOrByte::String("one".to_owned()),
    StringOrByte::String("two".to_owned()),
  ]);

  let number_array: Vec<StringOrByte> = serde_yml::from_str("[0x1, 2]").unwrap();
  assert_eq!(number_array, vec![
    StringOrByte::Byte(1),
    StringOrByte::Byte(2),
  ]);
  let mixed_array: Vec<StringOrByte> = serde_yml::from_str("[one, 2]").unwrap();
  assert_eq!(mixed_array, vec![
    StringOrByte::String("one".to_owned()),
    StringOrByte::Byte(2),
  ]);
}

#[test]
fn contents() {
  let string: Contents = serde_yml::from_str("one").unwrap();
  assert_eq!(string, Contents::Str("one".to_owned()));

  let array: Contents = serde_yml::from_str("[0x1, 'two', 3]").unwrap();
  assert_eq!(array, Contents::Vec(vec![
    StringOrByte::Byte(1),
    StringOrByte::String("two".to_owned()),
    StringOrByte::Byte(3),
  ]));

  let string: Attribute = serde_yml::from_str("
    contents: one
  ").unwrap();
  assert_eq!(string, Attribute {
    contents: Some(Contents::Str("one".to_owned())),
    ..Default::default()
  });

  let array: Attribute = serde_yml::from_str("
    contents: [0x1, 'two', 3]
  ").unwrap();
  assert_eq!(array, Attribute {
    contents: Some(Contents::Vec(vec![
      StringOrByte::Byte(1),
      StringOrByte::String("two".to_owned()),
      StringOrByte::Byte(3),
    ])),
    ..Default::default()
  });
}

#[test]
fn type_() {
  use std::iter::FromIterator;

  let type_: Type = serde_yml::from_str("str").unwrap();
  assert_eq!(type_, Type::Fixed(TypeRef::Builtin(Builtin::str)));

  let type_: Type = serde_yml::from_str("custom").unwrap();
  assert_eq!(type_, Type::Fixed(TypeRef::User("custom".to_owned())));

  let type_: Type = serde_yml::from_str("
    switch-on: id
    cases:
      '1': one
      '2': two
  ").unwrap();
  assert_eq!(type_, Type::Choice {
    switch_on: Scalar::String("id".to_owned()),
    cases: IndexMap::from_iter(vec![
      (Scalar::String("1".to_owned()), TypeRef::User("one".to_owned())),
      (Scalar::String("2".to_owned()), TypeRef::User("two".to_owned())),
    ]),
  });
}

#[cfg(test)]
mod repeat {
  use super::*;
  use pretty_assertions::assert_eq;

  #[test]
  fn eos() {
    let repeat: Attribute = serde_yml::from_str("
      repeat: eos
    ").unwrap();
    assert_eq!(repeat, Attribute {
      repeat: Some(Repeat::Eos),
      repeat_expr: None,
      repeat_until: None,
      ..Default::default()
    });
  }
  #[test]
  fn expr() {
    let repeat: Attribute = serde_yml::from_str("
      repeat: expr
      repeat-expr: 1 + 1
    ").unwrap();
    assert_eq!(repeat, Attribute {
      repeat: Some(Repeat::Expr),
      repeat_expr: Some(Count::Expr("1 + 1".to_owned())),
      ..Default::default()
    });

    let repeat: Attribute = serde_yml::from_str("
      repeat-expr: 42
    ").unwrap();
    assert_eq!(repeat, Attribute {
      repeat: None,
      repeat_expr: Some(Count::Value(42)),
      repeat_until: None,
      ..Default::default()
    });
  }
  #[test]
  fn until() {
    let repeat: Attribute = serde_yml::from_str("
      repeat: until
      repeat-until: 1 + 1
    ").unwrap();
    assert_eq!(repeat, Attribute {
      repeat: Some(Repeat::Until),
      repeat_expr: None,
      repeat_until: Some(Condition::Expr("1 + 1".to_owned())),
      ..Default::default()
    });

    let repeat: Attribute = serde_yml::from_str("
      repeat-until: false
    ").unwrap();
    assert_eq!(repeat, Attribute {
      repeat: None,
      repeat_expr: None,
      repeat_until: Some(Condition::Value(false)),
      ..Default::default()
    });
  }
}

#[cfg(test)]
mod parent {
  use super::*;
  use pretty_assertions::assert_eq;

  #[test]
  fn none() {
    let attr: Attribute = serde_yml::from_str("
      parent: false
    ").unwrap();
    assert_eq!(attr, Attribute {
      parent: Some(Expression::Value(false)),
      ..Default::default()
    });
  }

  #[test]
  fn some() {
    let attr: Attribute = serde_yml::from_str("
      parent: _parent._parent
    ").unwrap();
    assert_eq!(attr, Attribute {
      parent: Some(Expression::Expr("_parent._parent".into())),
      ..Default::default()
    });
  }
}

#[cfg(test)]
mod valid {
  use super::*;
  use pretty_assertions::assert_eq;

  #[test]
  fn shorthand_eq() {
    let rules: ValidationRules = serde_yml::from_str("true").unwrap();
    assert_eq!(rules, ValidationRules::Eq(Scalar::Bool(true)));

    let rules: ValidationRules = serde_yml::from_str("false").unwrap();
    assert_eq!(rules, ValidationRules::Eq(Scalar::Bool(false)));

    let rules: ValidationRules = serde_yml::from_str("10").unwrap();
    assert_eq!(rules, ValidationRules::Eq(Scalar::Number(10.into())));

    let rules: ValidationRules = serde_yml::from_str("'10'").unwrap();
    assert_eq!(rules, ValidationRules::Eq(Scalar::String("10".into())));
  }

  #[test]
  fn empty() {
    let rules: ValidationRules = serde_yml::from_str("{}").unwrap();
    assert_eq!(rules, ValidationRules::Checks {
      eq: None,
      min: None,
      max: None,
      expr: None,
      any_of: None,
      in_enum: None,
    });
  }

  #[test]
  fn checks() {
    let rules: ValidationRules = serde_yml::from_str("
      eq: 10
      min: 10
      max: 10
      expr: _
      any-of: [1, 2]
      in-enum: path::to::enum
    ").unwrap();
    assert_eq!(rules, ValidationRules::Checks {
      eq: Some(Scalar::Number(10.into())),
      min: Some(Expression::Value(10.into())),
      max: Some(Expression::Value(10.into())),
      expr: Some(Expression::Expr("_".into())),
      any_of: Some(vec![
        Scalar::Number(1.into()),
        Scalar::Number(2.into()),
      ]),
      in_enum: Some(EnumRef("path::to::enum".into())),
    });
  }

  #[test]
  fn min_max_arrays() {
    let rules: ValidationRules = serde_yml::from_str("
      min: '[1, 2]'
      max: '[3, 4]'
    ").unwrap();
    assert_eq!(rules, ValidationRules::Checks {
      eq: None,
      min: Some(Expression::Expr("[1, 2]".into())),
      max: Some(Expression::Expr("[3, 4]".into())),
      expr: None,
      any_of: None,
      in_enum: None,
    });
  }

  #[test]
  fn min_max_strings() {
    let rules: ValidationRules = serde_yml::from_str(r#"
      min: '"ab"'
      max: '"ac"'
    "#).unwrap();
    assert_eq!(rules, ValidationRules::Checks {
      eq: None,
      min: Some(Expression::Expr("\"ab\"".into())),
      max: Some(Expression::Expr("\"ac\"".into())),
      expr: None,
      any_of: None,
      in_enum: None,
    });
  }
}
