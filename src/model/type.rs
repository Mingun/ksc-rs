use std::fmt::Display;
use std::hash::Hash;

use indexmap::map::Entry;
use indexmap::IndexMap;

use crate::error::ModelError;
use crate::model::expressions::OwningNode;
use crate::model::{
  Attribute, Enum, EnumName, FileContext, PackageContext, SeqName, TypeContext, TypeName,
};
use crate::parser as p;
use crate::parser::expressions::{Node, TypeName as TName};

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
  pub(crate) fn validate(name: TName, args: Vec<Node>, ctx: &TypeContext) -> Result<Self, ModelError> {
    Ok(Self {
      //TODO: resolve relative types
      path: name.scope.path.into_iter().map(TypeName::valid).collect(),
      name: TypeName::valid(name.name),
      args: OwningNode::validate_all(args, ctx)?,
    })
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines a user-defined type
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UserType {
  /// The list of fields that this type consists of. The fields in the data stream
  /// are in the same order as they are declared here.
  pub fields: IndexMap<SeqName, Attribute>,
  // pub getters: IndexMap<InstanceName, Instance>, //TODO: instances
  /// List of used-defined types, defined inside this type.
  pub types: IndexMap<TypeName, UserType>,
  /// List of enumerations defined inside this type.
  pub enums: IndexMap<EnumName, Enum>,
  // pub params: IndexMap<ParamName, Param>, //TODO: Parameters
}
impl UserType {
  /// Performs validation of lists for duplicated entries
  ///
  /// # Parameters
  /// - `seq`: sequence of elements from a `parser` module
  /// - `check`: validation function that converts type from a `parser` module into
  ///   type from a `model` module
  fn check_duplicates<I, K, V, F>(
    seq: Option<I>,
    mut check: F,
  ) -> Result<IndexMap<K, V>, ModelError>
  where
    I: IntoIterator,
    K: Eq + Hash + Display,
    F: FnMut(I::Item) -> Result<(K, V), ModelError>,
  {
    use ModelError::*;

    Ok(match seq {
      None => IndexMap::new(),
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

  fn validate(spec: &p::TypeSpec, mut defaults: p::Defaults, ctx: &FileContext) -> Result<Self, ModelError> {
    // Merge type defaults with inherited defaults
    if let Some(def) = spec.default.clone() {
      defaults.endian     = def.endian.or(defaults.endian);
      defaults.bit_endian = def.bit_endian.or(defaults.bit_endian);
      defaults.encoding   = def.encoding.or(defaults.encoding);
    }

    let type_ctx = ctx.for_type(spec);

    let fields = Self::check_duplicates(spec.seq.as_ref().map(|s| s.into_iter().enumerate()), |(i, spec)| {
      Ok((
        SeqName::validate(i, spec.id.clone())?,
        Attribute::validate(spec, &defaults, &type_ctx)?,
      ))
    })?;
    let types = Self::check_duplicates(spec.types.as_ref(), |(name, spec)| {
      Ok((
        TypeName::validate(name)?,
        UserType::validate(spec, defaults.clone(), ctx)?,
      ))
    })?;
    let enums = Self::check_duplicates(spec.enums.as_ref(), |(name, spec)| {
      Ok((
        EnumName::validate(name)?,
        Enum::validate(spec)?,
      ))
    })?;

    Ok(Self {
      fields,
      types,
      enums,
    })
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines top-level user-defined type
#[derive(Clone, Debug, PartialEq)]
pub struct Root {
  /// Name of top-level type
  pub name: TypeName,
  /// Definition of type
  pub type_: UserType,
}
impl Root {
  pub(crate) fn validate(data: &p::Ksy, ctx: &PackageContext) -> Result<Self, ModelError> {
    let name = match &data.meta.id {
      Some(name) => TypeName::validate(name)?,
      None => return Err(ModelError::Validation("`meta/id` is not defined".into())),
    };
    let type_ = UserType::validate(
      &data.root,
      data.meta.defaults.clone().into(),
      &ctx.for_file(&data),
    )?;

    Ok(Self { name, type_ })
  }
}
