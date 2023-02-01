//! Contains expression contexts. Each context defines possible context
//! variables that can be used in the expression and what they mean.
//!
//! # Contexts
//! An each expression property in the Kaitai Struct forming their own context
//! where only a subset а possible variables are available. All contexts have
//! an access to that list of variables:
//!
//! Variable |Type            |Description
//! ---------|----------------|-----------
//! `_root`  |_KaitaiStruct_  |The reference to the root type in the file
//! `_parent`|_KaitaiStruct_  |The reference to the _parent_ type of a type with a property that uses this variable
//! `_sizeof`|Unsigned integer|The size in bytes of a type with a property that uses this variable
//! `_io`    |_KaitaiStream_  |The stream was that used to read a type with a property that uses this variable
//!
//! Additionally, the following variables are available if attribute is repeated
//! (defined with the `repeat-expr`, `repeat-until`, or `repeat: eos` key):
//!
//! Variable |Type            |Description
//! ---------|----------------|-----------
//! `_`      |_Attribute type_|The last parsed element. This variable is unavailable in the `cases.<case>` contexts because of special meaning
//! `_buf`   |`u1[]`          |The raw byte buffer of a last parsed element
//! `_index` |Unsigned integer|The index of an element being parsed (counted from 0)
//!
//! The other variables are available depending on the property:
//!
//! - `[type.]meta.endian.switch-on`
//! - `[type.]meta.endian.cases.<case>`
//! - `<type>.to-string`
//! - `<type>.seq[i].if`
//! - `<type>.seq[i].process`
//! - `<type>.seq[i].repeat-expr`
//! - `<type>.seq[i].repeat-until`
//! - `<type>.seq[i].size`
//! - `<type>.seq[i].type`
//! - `<type>.seq[i].type.switch-on`
//! - `<type>.seq[i].type.cases.<case>`
//! - `<type>.seq[i].valid`
//! - `instances.<instance>.io`
//! - `instances.<instance>.pos`
//! - `instances.<instance>.value`
//! - `instances.<instance>.if`
//! - `instances.<instance>.process`
//! - `instances.<instance>.repeat-expr`
//! - `instances.<instance>.repeat-until`
//! - `instances.<instance>.size`
//! - `instances.<instance>.type`
//! - `instances.<instance>.type.switch-on`
//! - `instances.<instance>.type.cases.<case>`
//! - `instances.<instance>.valid`


use crate::error::ModelError;
use crate::model::expressions::OwningNode;
use crate::parser::expressions::SpecialName;

macro_rules! context {
  (
    $(#[$meta:meta])*
    $var:ident, $expr:ident : $ty:ty = $ctx:literal => ($(
      $(#[$doc:meta])*
      $key:ident => $value:ident,
    )*)
  ) => {
    $(#[$meta])*
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum $var {
      /// `_io`: stream associated with this object of user-defined type.
      Stream,
      /// `_root`: top-level user-defined structure in the current file.
      Root,
      /// `_parent`: structure that produced this particular instance of the
      /// user-defined type.
      Parent,
      /// `_sizeof`: used as an attribute of the struct to get a compile-time size
      /// of the structure:
      ///
      /// ```yaml
      /// seq:
      /// - id: file_hdr
      ///   type: file_header
      /// - id: dib_info
      ///   size: file_hdr.ofs_bitmap - file_hdr._sizeof
      /// ```
      SizeOf,
      $(
        $(#[$doc])*
        $value
      ),*
    }

    impl TryFrom<SpecialName> for $var {
      type Error = ModelError;

      #[inline]
      fn try_from(name: SpecialName) -> Result<Self, Self::Error> {
        match name {
          SpecialName::Stream => Ok(Self::Stream),
          SpecialName::Root   => Ok(Self::Root),
          SpecialName::Parent => Ok(Self::Parent),
          SpecialName::SizeOf => Ok(Self::SizeOf),//TODO: проверить на рекурсивность определения
          $(
            SpecialName::$key => Ok(Self::$value),
          )*

          _ => Err(ModelError::Validation(format!(
            "special variable `{}` is unaccessible in the `{}` context",
            name, $ctx
          ).into())),
        }
      }
    }

    $(#[$meta])*
    pub struct $expr(OwningNode<$var>);
  };
}

context!(
  /// Variables available in expressions used at the type level:
  /// - `[<type>.]meta.endian.switch-on`
  /// - `[<type>.]to-string`
  TypeVar: () = "to-string" => ()
);

context!(
  /// Variables available in expressions used at the attribute level outside the cycle for repeated attributes:
  /// - `<type>.seq[i].if`
  /// - `<type>.seq[i].process`
  /// - `<type>.seq[i].valid`
  AttributeVar: () = "" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index    => Index,
    /// `_`: Last parsed element in an element
    Value    => Last,
    /// `_buf`: Unparsed content of current iteration as an array
    RawValue => LastBuffer,
  )
);

context!(
  /// Variables available in expressions used at the attribute level inside the cycle for repeated attributes:
  /// - `<type>.seq[i].repeat-expr`
  /// - `<type>.seq[i].repeat-until`
  /// - `<type>.seq[i].size`
  /// - `<type>.seq[i].type`
  /// - `<type>.seq[i].type.switch-on`
  /// - `<type>.seq[i].type.cases.<case>`
  RepeatedVar: () = "" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index    => Index,
    /// `_`: Last parsed element in an element
    Value    => Last,
    /// `_buf`: Unparsed content of current iteration as an array
    RawValue => LastBuffer,
  )
);

context!(
  /// Context variables that available in the
  /// - `[<type>.]meta.endian.cases.<case>`
  /// - `<type>.seq[i].type.cases.<case>`
  CaseVar: () = "cases.<case>" => (
    /// `_`: Default label that will be used if all more specific cases does not match
    Value => Default,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `[<type>.]meta.endian.switch-on`
  EndianSwitchOnVar, ByteOrderSwitchOnExpr: () = "endian.switch-on" => ()
);

context!(
  /// Context variables that available in the
  /// - `[<type>.]meta.endian.cases.<case>`
  EndianCasesVar, ByteOrderCasesExpr: () = "endian.cases.<case>" => (
    /// `_`: Default label that will be used if all more specific cases does not match
    Value => Default,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].if`
  /// - `instances.<instance>.if`
  IfVar, IfExpr: bool = "if" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].process`
  /// - `instances.<instance>.process`
  ProcessVar, ProcessExpr: () = "process" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,
  )
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].repeat-expr`
  /// - `instances.<instance>.repeat-expr`
  RepeatCountVar, RepeatCountExpr: usize = "repeat-expr" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].repeat-until`
  /// - `instances.<instance>.repeat-until`
  RepeatUntilVar, RepeatUntilExpr: bool = "repeat-until" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index    => Index,
    /// `_`: Last parsed element in field
    Value    => Last,
    /// `_buf`: Unparsed content of current iteration as an array
    RawValue => LastUnparsed,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].size`
  /// - `instances.<instance>.size`
  SizeVar, SizeExpr: usize = "size" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index, //TODO: only if `repeat` key is defined
  )
);

context!(
  /// Context variables that available in the
  /// - `<type>.to-string`
  ToStringVar: String = "to-string" => ()
);
/*
context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].type`
  /// - `instances.<instance>.type`
  TypeVar, TypeExpr: TypeRef = "type" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index, //TODO: only if `repeat` key is defined
    /// `_`: Last parsed element in field. Undefined on the first iteration
    Value => Last,  //TODO: only if `repeat` key is defined
  )
);*/

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].type.switch-on`
  /// - `instances.<instance>.type.switch-on`
  TypeSwitchOnVar, TypeSwitchOnExpr: () = "type.switch-on" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,    //TODO: only if `repeat` key is defined
  )
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].type.cases.<case>`
  /// - `instances.<instance>.type.cases.<case>`
  TypeCasesVar, TypeCasesExpr: () = "type.cases.<case>" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,    //TODO: only if `repeat` key is defined
    /// `_`: Default label that will be used if all more specific cases does not match
    Value => Default,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `instances.<instance>.io`
  IoVar, IoExpr: () = "io" => ()
);

context!(
  /// Context variables that available in the
  /// - `instances.<instance>.pos`
  PosVar, PosExpr: () = "pos" => ()
);

context!(
  /// Context variables that available in the
  /// - `instances.<instance>.value`
  ValueVar, ValueExpr: () = "value" => ()
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].valid`
  /// - `instances.<instance>.valid`
  ValidVar, ValidExpr: bool = "valid" => ()
);
