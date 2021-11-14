use std::fmt::Display;
use std::hash::Hash;
use std::ops::Deref;

use indexmap::map::Entry;
use indexmap::IndexMap;

use crate::error::ModelError;
use crate::model::expressions::OwningNode;
use crate::model::{
  Attribute, AttributeName, Enum, EnumName, FieldName, FileContext, Instance, OptionalName,
  PackageContext, SeqName, SizeOf, TypeContext, TypeName,
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
  /// Returns a map with field names that is valid according to the target
  /// language rules. Generation and validity checks are performed by the
  /// `generator` function that receives 2 parameters:
  /// - a field name for which name is generated
  /// - a generation attempt. Attempts are started from zero and increasing
  ///   over the time. The generator MUST return different name on each attempt
  ///   otherwise the algorithm will run in infinity cycle.
  ///
  /// # Parameters
  /// - `generator`: a name generator function. This function should return
  ///   `Some(name)` if generated name in this attempt is valid and `None` if not.
  ///
  /// # Example
  ///
  /// ```
  /// # use ksc::model::UserType;
  /// use ksc::model::AttributeName::*;
  /// use heck::ToLowerCamelCase;
  ///
  /// # let ty: UserType = UserType::default();/*
  /// let ty: UserType = ...;
  /// # */
  ///
  /// // List of reserved words
  /// const KEYWORDS: [&'static str; 1] = [
  ///   "enum",
  /// ];
  ///
  /// let names = ty.attribute_names(|name, attempt| {
  ///   // Generate a name converted by converting KSY field name
  ///   // to mixedCase (Java field style names) on first attempt
  ///   // and adding a numerical suffix on other attempts
  ///   let generated = match (attempt, name) {
  ///     // it is better to generate non-intersecting names for
  ///     // unnamed fields, for example, in this case, starting
  ///     // with an underscore (because such names are not possible
  ///     // for named fields after to mixedCase conversion), but
  ///     // that is not strictly necessary
  ///     (0, Unnamed(i)) => format!("unnamed{}", i),
  ///     (a, Unnamed(i)) => format!("unnamed{}{}", i, a),
  ///
  ///     (0, Seq(n)) => n.to_lower_camel_case(),
  ///     (a, Seq(n)) => format!("{}{}", n.to_lower_camel_case(), a),
  ///
  ///     (0, NonSeq(n)) => n.to_lower_camel_case(),
  ///     (a, NonSeq(n)) => format!("{}{}", n.to_lower_camel_case(), a),
  ///   };
  ///
  ///   // Check if a generated name conflicts with a keyword and
  ///   // return `None` if that is true
  ///   match KEYWORDS.binary_search(&generated.as_ref()) {
  ///     Ok(_) => None,
  ///     Err(_) => Some(generated),
  ///   }
  /// });
  /// ```
  pub fn attribute_names<G, R>(
    &self,
    generator: G,
  ) -> IndexMap<AttributeName, R>
    where G: Fn(AttributeName, usize) -> Option<R>,
          R: Clone + Eq + Hash + AsRef<str>,
  {
    let mut mapping = IndexMap::new();
    let mut used_names = IndexMap::new();
    let mut unprocessed_named = Vec::new();
    let mut unprocessed_unnamed = Vec::new();

    enum State<'a> {
      /// Mapping was added
      Inserted,
      /// Old mapping was replaced by new one, the old mapped value returned
      Replaced(AttributeName<'a>),
      /// Mapping was not done because there is a invalid name or unnamed field
      Postponed,
    }

    let mut generate = |attempt, name, original| {
      if let Some(generated) = generator(name, attempt) {
        match used_names.entry(generated.clone()) {
          // If name not used yet, register mapping
          Entry::Vacant(e) => {
            mapping.insert(name, generated);
            e.insert(name);
            State::Inserted
          },
          // If mapping already used, but generated name does not match
          // original one, and new candidate has the same name as generated one,
          // replace mapping
          Entry::Occupied(mut e) => {
            if original == generated.as_ref() && mapping.get(&name) != Some(&generated) {
              mapping.insert(name, generated);
              let old = e.insert(name);
              mapping.swap_remove(&old);
              State::Replaced(old)
            } else {
              State::Postponed
            }
          },
        }
      } else {
        State::Postponed
      }
    };

    // First, use all names that does not violates rules. Unnamed fields does
    // not violate rules, but their generated names could conflict with the
    // explicitly defined ones, so we postpone their name generation
    for (name, _) in &self.fields {
      match name {
        OptionalName::Unnamed(i) => unprocessed_unnamed.push(*i),
        OptionalName::Named(n) => {
          match generate(0, AttributeName::Seq(n), n.deref()) {
            State::Inserted => {},
            State::Replaced(old) => unprocessed_named.push(old),
            State::Postponed => unprocessed_named.push(AttributeName::Seq(n)),
          }
        }
      }
    }

    for (name, _) in &self.instances {
      match generate(0, AttributeName::NonSeq(name), name.deref()) {
        State::Inserted => {},
        State::Replaced(old) => unprocessed_named.push(old),
        State::Postponed => unprocessed_named.push(AttributeName::NonSeq(name)),
      }
    }

    for name in unprocessed_named {
      match name {
        AttributeName::Seq(n) | AttributeName::NonSeq(n) => {
          for attempt in 1.. {
            if let State::Inserted = generate(attempt, name, n.deref()) {
              break;
            }
          }
        },
        _ => unreachable!(),
      }
    }

    // Generate names for unnamed fields in the last stage
    for i in unprocessed_unnamed {
      for attempt in 0.. {
        if let State::Inserted = generate(attempt, AttributeName::Unnamed(i), "") {
          break;
        }
      }
    }

    mapping
  }

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

#[test]
fn type_names() {
  use pretty_assertions::assert_eq;
  use std::collections::BTreeMap;
  use heck::ToLowerCamelCase;
  use AttributeName::*;
  use crate::model::{Name, Package};

  macro_rules! p {
    (@ $key:literal => $value:literal) => {
      (Unnamed($key), $value.to_string())
    };
    ($key:literal => $value:literal) => {
      (Seq(&Name::valid($key)), $value.to_string())
    };
  }

  let ty: p::TypeSpec = serde_yml::from_str(r#"
  seq:
  - size: 1
  - size: 1
  - size: 1

  - id: unnamed0
    size: 1
  - id: unnamed01
    size: 1
  - id: unnamed0_1
    size: 1

  - id: unnamed1
    size: 1
  - id: unnamed1_1
    size: 1
  - id: unnamed11
    size: 1

  - id: enum
    size: 1
  - id: enum1
    size: 1
  - id: enum1_1
    size: 1
  "#).unwrap();

  let pkg = Package::test(p::Ksy::default());
  let ksy = pkg.files.values().next().unwrap();
  let ctx = PackageContext::new(&pkg);
  let ctx = ctx.for_file(&ksy);
  let ty = UserType::validate(&ty, p::Defaults::default(), &ctx).unwrap();
  const KEYWORDS: [&'static str; 1] = [
    "enum",
  ];

  let names = ty.attribute_names(|name, attempt| {
    let generated = match (attempt, name) {
      (0, Unnamed(i)) => format!("unnamed{}", i),
      (a, Unnamed(i)) => format!("unnamed{}{}", i, a),
      (0, Seq(n)) => n.to_lower_camel_case(),
      (a, Seq(n)) => format!("{}{}", n.to_lower_camel_case(), a),
      (0, NonSeq(n)) => n.to_lower_camel_case(),
      (a, NonSeq(n)) => format!("{}{}", n.to_lower_camel_case(), a),
    };

    match KEYWORDS.binary_search(&generated.as_ref()) {
      Ok(_) => None,
      Err(_) => Some(generated),
    }
  });

  let names: BTreeMap<_, _> = names.into_iter().collect();

  assert_eq!(names, BTreeMap::from([
    p!(@ 0          => "unnamed02"),  // Because "unnamed0" and "unnamed01" already exist
    p!(@ 1          => "unnamed12"),  // Because "unnamed1" already exist
    p!(@ 2          => "unnamed2"),

    p!("unnamed0"   => "unnamed0"),
    p!("unnamed01"  => "unnamed01"),
    p!("unnamed0_1" => "unnamed011"), // Because "unnamed01" already exist

    p!("unnamed1"   => "unnamed1"),
    p!("unnamed1_1" => "unnamed111"),
    p!("unnamed11"  => "unnamed11"),  // Because "unnamed01" already exist

    p!("enum"       => "enum2"),      // Because "enum1" already exist
    p!("enum1"      => "enum1"),
    p!("enum1_1"    => "enum11"),
  ]));
}
