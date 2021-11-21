//! Contains expression contexts. Each context defines possible context
//! variables that can be used in the expression and what they mean.
//!
//! # Contexts
//! An each expression property in the Kaitai Struct forming their own context
//! where only a subset of possible variables are available. All contexts have
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
//! `_buf`   |`[u8]`          |The raw byte buffer of a last parsed element
//! `_index` |Unsigned integer|The index of an element being parsed (counted from 0)
//!
//! The other variables are available depending on the property:
//!
//! - `[<type>.]meta.endian.switch-on`
//! - `[<type>.]meta.endian.cases.<case>`
//! - `<type>.to-string`
//! - `<type>.seq[i].if`
//! - `<type>.seq[i].parent`
//! - `<type>.seq[i].process`
//! - `<type>.seq[i].repeat-expr`
//! - `<type>.seq[i].repeat-until`
//! - `<type>.seq[i].size`
//! - `<type>.seq[i].type`
//! - `<type>.seq[i].type.switch-on`
//! - `<type>.seq[i].type.cases.<case>`
//! - `<type>.seq[i].valid`
//! - `<type>.seq[i].valid.eq`
//! - `<type>.seq[i].valid.min`
//! - `<type>.seq[i].valid.max`
//! - `<type>.seq[i].valid.expr`
//! - `<type>.seq[i].valid.any-of[i]`
//! - `<type>.instances.<instance>.io`
//! - `<type>.instances.<instance>.pos`
//! - `<type>.instances.<instance>.value`
//! - `<type>.instances.<instance>.if`
//! - `<type>.instances.<instance>.parent`
//! - `<type>.instances.<instance>.process`
//! - `<type>.instances.<instance>.repeat-expr`
//! - `<type>.instances.<instance>.repeat-until`
//! - `<type>.instances.<instance>.size`
//! - `<type>.instances.<instance>.type`
//! - `<type>.instances.<instance>.type.switch-on`
//! - `<type>.instances.<instance>.type.cases.<case>`
//! - `<type>.instances.<instance>.valid`
//! - `<type>.instances.<instance>.valid.eq`
//! - `<type>.instances.<instance>.valid.min`
//! - `<type>.instances.<instance>.valid.max`
//! - `<type>.instances.<instance>.valid.expr`
//! - `<type>.instances.<instance>.valid.any-of[i]`


use crate::error::ModelError;
use crate::parser::expressions::ContextVar;

/// Defines enumeration with the context variables, available is some property.
macro_rules! context {
  (
    $(#[$meta:meta])*
    $var:ident : $ty:ty = $ctx:literal => ($(
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

    impl TryFrom<ContextVar> for $var {
      type Error = ModelError;

      #[inline]
      fn try_from(name: ContextVar) -> Result<Self, Self::Error> {
        match name {
          $(
            ContextVar::$key => Ok(Self::$value),
          )*

          _ => Err(ModelError::Validation(format!(
            "special variable `{}` is unaccessible in the `{}` context",
            name, $ctx
          ).into())),
        }
      }
    }
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
  /// - `<type>.seq[i].valid.eq`
  /// - `<type>.seq[i].valid.min`
  /// - `<type>.seq[i].valid.max`
  /// - `<type>.seq[i].valid.expr`
  /// - `<type>.seq[i].valid.any-of[j]`
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
  EndianSwitchOnVar: () = "endian.switch-on" => ()
);

context!(
  /// Context variables that available in the
  /// - `[<type>.]meta.endian.cases.<case>`
  EndianCasesVar: () = "endian.cases.<case>" => (
    /// `_`: Default label that will be used if all more specific cases does not match
    Value => Default,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].if`
  /// - `<type>.instances.<instance>.if`
  IfVar: bool = "if" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].process`
  /// - `<type>.instances.<instance>.process`
  ProcessVar: () = "process" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,
  )
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].repeat-expr`
  /// - `<type>.instances.<instance>.repeat-expr`
  RepeatCountVar: usize = "repeat-expr" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].repeat-until`
  /// - `<type>.instances.<instance>.repeat-until`
  RepeatUntilVar: bool = "repeat-until" => (
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
  /// - `<type>.instances.<instance>.size`
  SizeVar: usize = "size" => (
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
  /// - `<type>.instances.<instance>.type`
  TypeVar: TypeRef = "type" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index, //TODO: only if `repeat` key is defined
    /// `_`: Last parsed element in field. Undefined on the first iteration
    Value => Last,  //TODO: only if `repeat` key is defined
  )
);*/

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].type.switch-on`
  /// - `<type>.instances.<instance>.type.switch-on`
  TypeSwitchOnVar: () = "type.switch-on" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,    //TODO: only if `repeat` key is defined
  )
);

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].type.cases.<case>`
  /// - `<type>.instances.<instance>.type.cases.<case>`
  TypeCasesVar: () = "type.cases.<case>" => (
    /// `_index`: Current iteration (counting from zero) if one of `repeat` keys is defined for a type
    Index => Index,    //TODO: only if `repeat` key is defined
    /// `_`: Default label that will be used if all more specific cases does not match
    Value => Default,
  )
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.instances.<instance>.io`
  IoVar: () = "io" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.instances.<instance>.pos`
  PosVar: () = "pos" => ()
);

context!(
  /// Context variables that available in the
  /// - `<type>.instances.<instance>.value`
  ValueVar: () = "value" => ()
);

//-------------------------------------------------------------------------------------------------

context!(
  /// Context variables that available in the
  /// - `<type>.seq[i].valid`
  /// - `<type>.instances.<instance>.valid`
  ValidVar: bool = "valid" => ()
);
