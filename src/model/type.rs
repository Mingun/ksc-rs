use std::fmt::Display;
use std::hash::Hash;

use indexmap::map::Entry;
use indexmap::IndexMap;

use crate::error::ModelError;
use crate::model::expressions::OwningNode;
use crate::model::{
  Attribute, Enum, EnumName, FieldName, FileContext, Instance, PackageContext, SeqName, SizeOf,
  TypeContext, TypeName,
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
    if let Err(_) = ctx.resolve_type(&name) {
      if !ctx.allow_opaque_types() {
        return Err(ModelError::Validation(format!("unknown type `{name}`").into()));
      }
    }
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
  /// List of dynamic and calculated fields of this type. The position of these fields
  /// is not fixed in the type, and they may not even be physically represented in the
  /// data stream at all.
  pub instances: IndexMap<FieldName, Instance>,
  /// List of used-defined types, defined inside this type.
  pub types: IndexMap<TypeName, UserType>,
  /// List of enumerations defined inside this type.
  pub enums: IndexMap<EnumName, Enum>,
  // pub params: IndexMap<ParamName, Param>, //TODO: Parameters
}
impl UserType {
  /// Calculates size that instances of that type occupied in the stream.
  ///
  /// The expression's language operator `sizeof<T>` and a special property [`_sizeof`] returns
  /// result of this method.
  ///
  /// The size is calculated as sum of sizes of all [`fields`].
  ///
  /// [`_sizeof`]: crate::model::expressions::OwningAttr::SizeOf
  /// [`fields`]: UserType::fields
  pub fn sizeof(&self) -> SizeOf {
    self.fields.iter().fold(SizeOf::Sized(0usize.into()), |acc, (_, a)| acc + a.sizeof())
  }

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
    let instances = Self::check_duplicates(spec.instances.as_ref(), |(name, spec)| {
      use ModelError::*;

      let name = FieldName::validate(name)?;

      if fields.contains_key(&name) {
        return Err(Validation(format!("a sequenced attribute and an instance cannot have the same name `{}`", name).into()));
      }

      Ok((name, Instance::validate(spec, &defaults, &type_ctx)?))
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
      instances,
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

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod sizeof {
  use super::*;
  use crate::model::Package;
  use pretty_assertions::assert_eq;

  macro_rules! type_check {
    ($fn:ident($type_:literal) == $size:expr) => {
      #[test]
      fn $fn() {
        let ty: p::TypeSpec = serde_yml::from_str(&format!(r#"
          seq:
          - id: f0
            type: u2
          - id: f1
            type: {}
        "#, $type_)).unwrap();
        let pkg = Package::test(p::Ksy::default());
        let ctx = PackageContext::new(&pkg);
        let ksy = pkg.files.values().next().unwrap();
        let ctx = ctx.for_file(ksy);

        let ty = UserType::validate(&ty, p::Defaults {
          encoding: Some("utf-8".into()),
          endian: Some(p::Variant::Fixed(p::ByteOrder::Be)),
          ..Default::default()
        }, &ctx).unwrap();
        assert_eq!(ty.sizeof(), $size);
      }
    };
  }
  macro_rules! type_check_if {
    ($fn:ident($type_:literal) == $size:expr) => {
      #[test]
      fn $fn() {
        let ty: p::TypeSpec = serde_yml::from_str(&format!(r#"
          seq:
          - id: f0
            type: u2
          - id: f1
            type: {}
            if: f0 != 0
        "#, $type_)).unwrap();
        let pkg = Package::test(p::Ksy::default());
        let ctx = PackageContext::new(&pkg);
        let ksy = pkg.files.values().next().unwrap();
        let ctx = ctx.for_file(ksy);

        let ty = UserType::validate(&ty, p::Defaults {
          encoding: Some("utf-8".into()),
          endian: Some(p::Variant::Fixed(p::ByteOrder::Be)),
          ..Default::default()
        }, &ctx).unwrap();
        assert_eq!(ty.sizeof(), $size);
      }
    };
  }

  type_check!(fixed_fixed("u4") == SizeOf::Sized(6usize.into()));
  type_check!(fixed_dynamic1("strz") == SizeOf::Unsized(2usize.into(), None));
  type_check!(fixed_dynamic2(
    "{ switch-on: 1, cases: { 1: u1, 2: u4 } }")
    ==
    SizeOf::Unsized(3usize.into(), Some(6usize.into()))
  );

  type_check_if!(fixed_fixed_if("u4") == SizeOf::Unsized(2usize.into(), Some(6usize.into())));
  type_check_if!(fixed_dynamic_if1("strz") == SizeOf::Unsized(2usize.into(), None));
  type_check_if!(fixed_dynamic_if2(
    "{ switch-on: 1, cases: { 1: u1, 2: u4 } }")
    ==
    SizeOf::Unsized(2usize.into(), Some(6usize.into()))
  );
}
