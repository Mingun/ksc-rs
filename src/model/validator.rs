use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};

use bigdecimal::num_bigint::BigInt;
use bigdecimal::BigDecimal;

use crate::model::Package;
use crate::parser::expressions::{Attr, EnumRef, Node, Scope, TypeName, UnaryOp};
use crate::parser::{Attribute, Enum, Ksy, Name, TypeSpec};

/// `TypeId` uses equivalence of pointers to compare equivalent types
#[derive(Debug)]
struct TypeId<'t>(&'t TypeSpec);
impl<'t> PartialEq for TypeId<'t> {
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    self.0 as *const TypeSpec == other.0 as *const TypeSpec
  }
}
impl<'t> Eq for TypeId<'t> {}
impl<'t> Hash for TypeId<'t> {
  #[inline]
  fn hash<H: Hasher>(&self, state: &mut H) {
    let ptr = self.0 as *const TypeSpec;
    ptr.hash(state);
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Possible errors returned when try to resolve names of various things.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveError<'n> {
  /// Specified type cannot be resolved
  UnknownType(&'n str),
  /// Specified enum cannot be resolved
  UnknownEnum(&'n str),
  /// Specified field cannot be resolved
  UnknownField,
  /// Specified enumeration variant cannot be resolved
  UnknownEnumVariant,
  /// Parent for a type cannot be determined
  UnknownParent,
  /// Expression should have boolean type in this context
  NotBool,
  /// Two expressions should have compatible types, but they don't
  MismatchedTypes,
}

impl<'n> fmt::Display for ResolveError<'n> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::UnknownType(n) => write!(f, "unknown type `{n}`"),
      Self::UnknownEnum(n) => write!(f, "unknown enum `{n}`"),
      Self::UnknownField => f.write_str("unknown field"),
      Self::UnknownEnumVariant => f.write_str("unknown enum variant"),
      Self::UnknownParent => f.write_str("unknown parent"),
      Self::NotBool => f.write_str("expected boolean expression"),
      Self::MismatchedTypes => f.write_str("mismatched types"),
    }
  }
}

impl<'n> Error for ResolveError<'n> {}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Debug, PartialEq)]
pub enum AttrType<'t> {
  Str,
  /// Type of indexes and sizeof operation
  Usize,
  Int,
  /// Each integer constant gives its own type
  IntConstant(BigInt),
  Float,
  /// Each floating-point constant gives its own type
  FloatConstant(BigDecimal),
  Bool,
  Bytes,

  /// Generic `KaitaiStruct` type, base for all user types
  Struct,
  /// Concrete instance of `KaitaiStruct`
  UserType(&'t TypeSpec),

  /// Type is a stream used to reading
  Stream,

  /// Type is a sequence of another type
  Seq(Box<AttrType<'t>>),
  /// Type is optional
  Option(Box<AttrType<'t>>),

  Enum(&'t Enum),
  Switch(Vec<AttrType<'t>>),
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Fills mapping from all child types to `ty` and recursively apply that to all child types.
/// The resulting map can be used to query in which type the specific type was defined.
fn fill_parents<'t>(parents: &mut HashMap<TypeId<'t>, &'t TypeSpec>, ty: &'t TypeSpec) {
  if let Some(types) = &ty.types {
    for (_, child) in types {
      parents.insert(TypeId(child), ty);
      fill_parents(parents, child);
    }
  }
}

/// Returns `true` if given id is equal to the given string
fn id_matches(id: &Option<Name>, name: &str) -> bool {
  id.as_ref().map(|n| n.0.as_str()) == Some(name)
}

fn merge_types<'t, 'n>(left: AttrType<'t>, right: AttrType<'t>) -> Result<AttrType<'t>, ResolveError<'n>> {
  todo!("l={:?}\nr={:?}", left, right)
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Context contains information about the whole model that used for cross-checking links in the model.
///
/// Goals of the context:
/// - provide a way to resolve types and enums by their names
/// - collect errors found during validation
#[derive(Debug)]
pub struct PackageContext<'p> {
  /// Contains the all files that was directly and indirectly imported
  package: &'p Package,
  /// Mapping from types to their enclosing types in KSY (which is called "parent" in Kaitai)
  parents: HashMap<TypeId<'p>, &'p TypeSpec>,
}
impl<'p> PackageContext<'p> {
  /// Creates a new context for checking specified package. You usually does not need
  /// to use this function, except in tests.
  pub fn new(package: &'p Package) -> Self {
    let mut parents = HashMap::new();
    for (_, file) in &package.files {
      fill_parents(&mut parents, &file.root);
    }

    Self { package, parents }
  }

  /// Returns the validation context for the specified file.
  ///
  /// # Parameters
  /// - `ksy`: the type which root type will be used to resolve absolute paths
  pub fn for_file<'a>(&'a self, ksy: &'a Ksy) -> FileContext<'a> {
    let mut imports = HashMap::new();
    if let Some(file_imports) = &ksy.meta.imports {
      for import in file_imports {
        if let Some(imported) = self.package.files.get(&import.name) {
          imports.insert(import.name.clone(), &imported.root);
        }
        // TODO: emit error about unknown import
      }
    }
    FileContext {
      ctx: self,
      ksy: &ksy,
      imports,
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Context of one file contains information about all types in the package and
/// information about root type of the concrete KS file.
///
/// Goals of the context:
/// - provide a way to resolve types and enums by their names
/// - collect errors found during validation
#[derive(Debug)]
pub struct FileContext<'p> {
  /// Contains the all files that was directly and indirectly imported
  ctx: &'p PackageContext<'p>,
  /// Root type in the file
  ksy: &'p Ksy,
  /// List of imported types under corresponding names
  imports: HashMap<Name, &'p TypeSpec>,
}
impl<'p> FileContext<'p> {
  /// Returns instance of object which can answer to the question
  /// "to what enum/type the specified name refers?".
  ///
  /// # Parameters
  /// - `context`: the type relative to which all relative paths will be resolved
  pub fn for_type<'a>(&'a self, context: &'a TypeSpec) -> TypeContext<'a> {
    TypeContext {
      file: self,
      context,
    }
  }

  /// Helper method, returns type context for the top-level type in a file.
  /// Useful when need to deal with absolute paths.
  pub fn for_root<'a>(&'a self) -> TypeContext<'a> {
    self.for_type(&self.ksy.root)
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Converted of type names to the instances of Rust types describing Kaitai user-defined types.
pub struct TypeContext<'t> {
  file: &'t FileContext<'t>,
  /// Type of the attribute, relative to which all names will be resolved
  context: &'t TypeSpec,
}

impl<'t> TypeContext<'t> {
  /// Returns whether types not defined in current file is allowed or not
  pub fn allow_opaque_types(&self) -> bool {
    self.file.ksy.meta.ks_opaque_types.unwrap_or_default()
  }

  /// Returns the surrounding type of the specified type or `None` if type is
  /// - a root type
  /// - an imported type
  /// - an unknown type
  fn parent(&self, type_id: &TypeId<'t>) -> Option<&'t TypeSpec> {
    Some(*self.file.ctx.parents.get(type_id)?)
  }

  /// Resolves type by its reference relatively to the contextual type.
  ///
  /// If type with `ref_.name` is defined inside `self.context`, then reference to it
  /// is returned. Otherwise go to the parent type and repeat search in it.
  ///
  /// # Parameters
  /// - `ref_`: the reference to the user-defined Kaitai type
  ///
  /// Returns `None` if type cannot be resolved.
  pub fn resolve_type<'n>(&self, ref_: &'n TypeName) -> Result<&'t TypeSpec, ResolveError<'n>> {
    if ref_.scope.absolute {
      self.file.for_root().resolve_scoped_type(&ref_.scope, ref_.name)
    } else {
      self.resolve_scoped_type(&ref_.scope, ref_.name)
    }
  }

  fn resolve_scoped_type<'n>(
    &self,
    scope: &'n Scope,
    name: &'n str,
  ) -> Result<&'t TypeSpec, ResolveError<'n>> {
    if scope.path.is_empty() {
      // just one name
      self.resolve_type_name(name)
    } else {
      // name with path or one name under root
      let ty = self.resolve_type_path(&scope.path)?;
      if let Some(types) = &ty.types {
        if let Some(ty) = types.get(name) {
          return Ok(ty);
        }
      }
      Err(ResolveError::UnknownType(name))
    }
  }

  /// Resolves type by its path relatively to the contextual type.
  ///
  /// If type with `name` is defined inside `self.context`, then reference to it
  /// is returned. Otherwise go to the parent type and repeat search in it.
  ///
  /// # Parameters
  /// - `path`: the list of type names to look for the type. The last name is the
  ///   name of type in question
  ///
  /// Returns `None` if type cannot be resolved.
  fn resolve_type_path<'n>(&self, path: &'n [&str]) -> Result<&'t TypeSpec, ResolveError<'n>> {
    let mut context = self.context;
    // Resolve types of each elements of a path
    if let [first, rest @ ..] = path {
      context = self.resolve_type_name(first)?;
      for name in rest {
        context = match &context.types {
          Some(types) => match types.get(*name) {
            Some(t) => t,
            None => return Err(ResolveError::UnknownType(*name)),
          },
          None => return Err(ResolveError::UnknownType(*name)),
        };
      }
    }
    Ok(context)
  }

  /// Resolves type by name relatively to the contextual type.
  ///
  /// If type with `name` is defined inside `self.context`, then reference to it
  /// is returned. Otherwise go to the parent type and repeat search in it.
  ///
  /// # Parameters
  /// - `name`: the name of the type to resolve
  ///
  /// Returns `None` if type cannot be resolved.
  fn resolve_type_name<'n>(&self, name: &'n str) -> Result<&'t TypeSpec, ResolveError<'n>> {
    let mut context = self.context;
    loop {
      let ctx = TypeId(context);
      // Root type does not have entry in self.parents, so handle it separately
      // TODO: Maybe create a fictive root type with real root and all imported types?
      let parent = if ctx == TypeId(&self.file.ksy.root) {
        if id_matches(&self.file.ksy.meta.id, name) {
          return Ok(context);
        }
        None
      } else {
        // Because `context` is not root (checked above) missing parent means unknown type
        let parent = match self.parent(&ctx) {
          Some(p) => p,
          None => return Err(ResolveError::UnknownType(name)),
        };

        // Unqualified name firstly tried to resolve to the same type in which context
        // type resolution is performed, so we need to check our name first, but because
        // types does not store their name, we ask a parent about it.
        if let Some(types) = &parent.types {
          match types.get(name) {
            // If we found `context` under requested name in parent, return it
            Some(me) if ctx == TypeId(me) => return Ok(context),
            _ => {},
          }
        }
        Some(parent)
      };

      // If current type have nested types, try to find in it
      if let Some(types) = &context.types {
        if let Some(t) = types.get(name) {
          return Ok(t);
        }
      }

      // Otherwise try in parent (surrounding) type or in imported types if we under root already
      context = match parent {
        Some(parent) => parent,
        None => {
          return match self.file.imports.get(name) {
            Some(t) => Ok(*t),
            None => Err(ResolveError::UnknownType(name)),
          };
        },
      };
    }
  }

  /// Resolves enum by its reference relatively to the contextual type.
  ///
  /// If enum with `ref_.name` is defined inside `self.context`, then reference to it
  /// is returned. Otherwise go to the parent type and repeat search in it.
  ///
  /// # Parameters
  /// - `scope`: the type from which enum should be taken
  /// - `name`: the name of an enum to get
  ///
  /// Returns `None` if enum cannot be resolved.
  fn resolve_enum<'n>(&self, ref_: &'n EnumRef) -> Result<&'t Enum, ResolveError<'n>> {
    if ref_.scope.absolute {
      self.file.for_root().resolve_scoped_enum(&ref_.scope, ref_.name)
    } else {
      self.resolve_scoped_enum(&ref_.scope, ref_.name)
    }
  }

  fn resolve_scoped_enum<'n>(
    &self,
    scope: &'n Scope,
    name: &'n str,
  ) -> Result<&'t Enum, ResolveError<'n>> {
    if scope.path.is_empty() {
      // just one name
      self.resolve_enum_name(name)
    } else {
      // name with path or one name under root
      let ty = self.resolve_type_path(&scope.path)?;
      if let Some(enums) = &ty.enums {
        if let Some(e) = enums.get(name) {
          return Ok(e);
        }
      }
      Err(ResolveError::UnknownEnum(name))
    }
  }

  /// Resolves enum by name relatively to the contextual type.
  ///
  /// If enum with `name` is defined inside `self.context`, then reference to it
  /// is returned. Otherwise go to the parent type and repeat search in it.
  ///
  /// # Parameters
  /// - `name`: the name of the enum to resolve
  ///
  /// Returns `None` if enum cannot be resolved.
  fn resolve_enum_name<'n>(&self, name: &'n str) -> Result<&'t Enum, ResolveError<'n>> {
    let mut context = self.context;
    loop {
      if let Some(enums) = &context.enums {
        if let Some(e) = enums.get(name) {
          return Ok(e);
        }
      }

      // Not found in current type, try in parent
      let ctx = TypeId(context);

      // If current type is root type and we still not found an enum, it is unknown
      if ctx == TypeId(&self.file.ksy.root) {
        return Err(ResolveError::UnknownEnum(name));
      }

      // Because `context` is not root (checked above) missing parent means unknown enum
      // Do not look up into imports, because enums cannot be directly imported.
      // Only types can be imported
      context = match self.parent(&ctx) {
        Some(parent) => parent,
        None => return Err(ResolveError::UnknownEnum(name)),
      };
    }
  }

  /// Calculates type of expression in current context
  fn calc_type(&self, expression: &'t Node) -> Result<AttrType<'t>, ResolveError<'t>> {
    use crate::parser::expressions::ContextVar as CtxVar;
    use Node::*;

    match expression {
      Str(_) => Ok(AttrType::Str),
      Int(i) => Ok(AttrType::IntConstant(i.clone())),
      Float(f) => Ok(AttrType::FloatConstant(f.clone())),
      Bool(_) => Ok(AttrType::Bool),
      InterpolatedStr(_) => Ok(AttrType::Str),
      ContextVar(CtxVar::Index) => Ok(AttrType::Usize),
      ContextVar(CtxVar::Value) => todo!("{:?}", expression),
      ContextVar(CtxVar::IsLe) => Ok(AttrType::Bool),
      ContextVar(CtxVar::RawValue) => Ok(AttrType::Bytes),
      ContextVar(CtxVar::SwitchOn) => todo!("{:?}", expression),
      Attr(attr) => self.calc_field(attr),
      EnumVariant { enum_, variant } => {
        let e = self.resolve_enum(enum_)?;
        // TODO: check presence of enum variant
        Ok(AttrType::Enum(e))
      }
      List(vec) => todo!("{:?}", expression),
      SizeOf { .. } => Ok(AttrType::Usize),
      Call { callee, method, args } => {
        let callee = self.calc_type(callee)?;
        let args: Result<Vec<_>, ResolveError> = args.iter().map(|a| self.calc_type(a)).collect();

        todo!("{:?}", expression)
      },
      Cast { expr, to_type } => {
        let expr_type = self.calc_type(expr)?;
        // TODO: check compatibility of types
        todo!("{:?} -> {:?}", expr_type, to_type)
      },
      Index { expr, index } => {
        // Expression should be indexable
        let elem = match self.calc_type(expr)? {
          AttrType::Seq(elem) => elem,
          _ => return Err(ResolveError::MismatchedTypes),
        };
        // Check that index has an integral type
        match self.calc_type(index)? {
          AttrType::Int | AttrType::IntConstant(_) => {},
          _ => return Err(ResolveError::MismatchedTypes),
        }
        Ok(*elem)
      },
      Access { expr, attr } => {
        match self.calc_type(expr)? {
          AttrType::UserType(context) => self.file.for_type(context).calc_field(attr),
          _ => Err(ResolveError::MismatchedTypes),
        }
      },
      Unary { op, expr } => {
        let expr = self.calc_type(expr)?;
        match (op, &expr) {
          (UnaryOp::Inv, AttrType::Int) |
          (UnaryOp::Inv, AttrType::IntConstant(_)) => Ok(expr),
          (UnaryOp::Inv, _) => Err(ResolveError::MismatchedTypes),

          (UnaryOp::Neg, AttrType::Int) |
          (UnaryOp::Neg, AttrType::IntConstant(_)) => Ok(expr),
          (UnaryOp::Neg, _) => Err(ResolveError::MismatchedTypes),

          (UnaryOp::Not, AttrType::Bool) => Ok(expr),
          (UnaryOp::Not, _) => Err(ResolveError::MismatchedTypes),
        }
      },
      Binary { op, left, right } => {
        let l = self.calc_type(left)?;
        let r = self.calc_type(right)?;

        todo!("{:?}", (op, l, r))
      },
      Branch { condition, if_true, if_false } => {
        match self.calc_type(condition)? {
          AttrType::Bool => {
            let l = self.calc_type(if_true)?;
            let r = self.calc_type(if_false)?;
            merge_types(l, r)
          },
          _ => Err(ResolveError::NotBool),
        }
      },
    }
  }

  fn calc_field(&self, attr: &Attr) -> Result<AttrType<'t>, ResolveError<'t>> {
    match attr {
      Attr::Stream => Ok(AttrType::Stream),
      Attr::Root => Ok(AttrType::UserType(&self.file.ksy.root)),
      Attr::Parent => match self.parent(&TypeId(self.context)) {
        Some(parent) => Ok(AttrType::UserType(parent)),
        None => Err(ResolveError::UnknownParent),
      },
      Attr::SizeOf => Ok(AttrType::Usize),
      Attr::User(field) => {
        if let Some(seq) = &self.context.seq {
          match seq.iter().find(|a| id_matches(&a.id, *field)) {
            Some(a) => return self.calc_attr(a),
            None => {},
          }
        }
        if let Some(instances) = &self.context.instances {
          match instances.get(*field) {
            Some(i) => return self.calc_attr(&i.attr),
            None => {},
          }
        }
        if let Some(params) = &self.context.params {
          match params.iter().find(|p| id_matches(&p.id, *field)) {
            Some(p) => todo!("param({}) -> {:?}", field, p),
            None => {},
          }
        }
        Err(ResolveError::UnknownField)
      },
    }
  }

  fn calc_attr(&self, attr: &Attribute) -> Result<AttrType<'t>, ResolveError<'t>> {
    todo!("{:?}", attr)
    /*let ty = match &attr.chunk {
      Variant::Fixed(chunk) => self.calc_chunk(chunk)?,
      Variant::Choice { .. } => todo!("{:?}", attr.chunk),
    };

    // TODO: probably just two flags, because arbitrary nesting is not required
    let ty = match attr.repeat {
      Repeat::None => AttrType::Seq(Box::new(ty)),
      _ => ty,
    };
    let ty = match attr.condition {
      Some(_) => AttrType::Option(Box::new(ty)),
      None => ty,
    };
    Ok(ty)*/
  }

  /*fn calc_chunk<'n>(&self, chunk: &'n Chunk) -> Result<AttrType<'t>, ResolveError<'n>> {
    match &chunk.type_ref {
      TypeRef::Enum { base, enum_ } => match enum_ {
        Some(path) => match self.resolve_enum_ref(path) {
          Some(e) => Ok(AttrType::Enum(e)),
          None => Err(ResolveError::UnknownEnum),
        },
        None => Ok(AttrType::Int),
      },
      TypeRef::F32(_) => Ok(AttrType::Float),
      TypeRef::F64(_) => Ok(AttrType::Float),
      TypeRef::Bytes => Ok(AttrType::Bytes),
      TypeRef::String(_) => Ok(AttrType::Str),
      TypeRef::User(u) => {
        let ty = match self.resolve_type_ref(u) {
          Some(ty) => ty,
          None => return Err(ResolveError::UnknownType),
        };
        // Check correctness of types of the arguments
        for arg in &u.args {
          self.calc_type(arg)?;
        }
        Ok(AttrType::UserType(ty))
      },
      TypeRef::Fixed(_) => Ok(AttrType::Bytes),
    }
  }*/
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
  use super::*;
  use ResolveError::*;
  use pretty_assertions::assert_eq;

  fn setup() -> Ksy {
    serde_yml::from_str("
    meta:
      id: root
    enums:
      e: {} # e_root
    types:
      child_1:
        types:
          one: # child_11
            enums:
              e: {} # e_11
          two: # child_12
            enums:
              e: {} # e_12
            types:
              one: {} # child_121
              two: {} # child_122
      child_2:
        enums:
          e: {} # e_2
        types:
          one: {} # child_21
          two: {} # child_22
    ").unwrap()
  }

  #[test]
  fn fill_parents() {
    let ksy = setup();

    let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
    let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

    let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
    let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

    let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
    let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

    let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
    let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

    let mut parents = HashMap::new();
    super::fill_parents(&mut parents, &ksy.root);
    dbg!(&parents);

    assert_eq!(parents.len(), 8, "number of types"); // all child_*
    assert_eq!(parents.get(&TypeId(&ksy.root)), None);

    assert_eq!(parents.get(&TypeId(child_1)), Some(&&ksy.root));
    assert_eq!(parents.get(&TypeId(child_2)), Some(&&ksy.root));

    assert_eq!(parents.get(&TypeId(child_11)), Some(&child_1));
    assert_eq!(parents.get(&TypeId(child_12)), Some(&child_1));

    assert_eq!(parents.get(&TypeId(child_21)), Some(&child_2));
    assert_eq!(parents.get(&TypeId(child_22)), Some(&child_2));

    assert_eq!(parents.get(&TypeId(child_121)), Some(&child_12));
    assert_eq!(parents.get(&TypeId(child_122)), Some(&child_12));
  }

  /// Checks that the type specified by a name can be correctly found in a complex hierarchy of types
  #[test]
  fn resolve_type_name() {
    let pkg = Package::test(setup());
    let ctx = PackageContext::new(&pkg);
    let ksy = pkg.files.values().next().unwrap();
    let context = ctx.for_file(ksy);

    let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
    let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

    let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
    let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

    let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
    let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

    let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
    let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

    let root_ptr = &ksy.root as *const TypeSpec;
    let child_1_ptr = child_1 as *const TypeSpec;
    let child_2_ptr = child_2 as *const TypeSpec;

    let child_11_ptr = child_11 as *const TypeSpec;
    let child_12_ptr = child_12 as *const TypeSpec;

    let child_21_ptr = child_21 as *const TypeSpec;
    let child_22_ptr = child_22 as *const TypeSpec;

    let child_121_ptr = child_121 as *const TypeSpec;
    let child_122_ptr = child_122 as *const TypeSpec;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve<'n>(resolver: &TypeContext, name: &'n str) -> Result<*const TypeSpec, ResolveError<'n>> {
      resolver.resolve_type_name(name).map(|t| t as *const TypeSpec)
    }

    let resolver = context.for_type(&ksy.root);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, "two"), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_1);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_11_ptr));
    assert_eq!(resolve(&resolver, "two"), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_2);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "one"), Ok(child_21_ptr));
    assert_eq!(resolve(&resolver, "two"), Ok(child_22_ptr));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_11);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_12);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, "two"), Ok(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_21);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Ok(child_22_ptr));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_22);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_21_ptr));
    assert_eq!(resolve(&resolver, "two"), Ok(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_121);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));

    let resolver = context.for_type(child_122);
    assert_eq!(resolve(&resolver, "root"), Ok(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Ok(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Ok(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, "two"), Ok(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), Err(UnknownType("unk")));
  }

  /// Checks that the type specified by a path can be correctly found in a complex hierarchy of types
  #[test]
  fn resolve_type_path() {
    let pkg = Package::test(setup());
    let ctx = PackageContext::new(&pkg);
    let ksy = pkg.files.values().next().unwrap();
    let context = ctx.for_file(ksy);

    let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
    let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

    let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
    let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

    let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
    let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

    let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
    let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

    let root_ptr = &ksy.root as *const TypeSpec;
    let child_1_ptr = child_1 as *const TypeSpec;
    let child_2_ptr = child_2 as *const TypeSpec;

    let child_11_ptr = child_11 as *const TypeSpec;
    let child_12_ptr = child_12 as *const TypeSpec;

    let child_21_ptr = child_21 as *const TypeSpec;
    let child_22_ptr = child_22 as *const TypeSpec;

    let child_121_ptr = child_121 as *const TypeSpec;
    let child_122_ptr = child_122 as *const TypeSpec;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve<'n>(resolver: &TypeContext, path: &'n [&str]) -> Result<*const TypeSpec, ResolveError<'n>> {
      resolver.resolve_type_path(path).map(|t| t as *const TypeSpec)
    }

    let resolver = context.for_type(&ksy.root);
    assert_eq!(resolve(&resolver, &[]), Ok(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["two", "one"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("two")));

    let resolver = context.for_type(child_1);
    assert_eq!(resolve(&resolver, &[]), Ok(child_1_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_11_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_2);
    assert_eq!(resolve(&resolver, &[]), Ok(child_2_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_21_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_22_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_11);
    assert_eq!(resolve(&resolver, &[]), Ok(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_12);
    assert_eq!(resolve(&resolver, &[]), Ok(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_21);
    assert_eq!(resolve(&resolver, &[]), Ok(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_22_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_22);
    assert_eq!(resolve(&resolver, &[]), Ok(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_21_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_121);
    assert_eq!(resolve(&resolver, &[]), Ok(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Ok(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));

    let resolver = context.for_type(child_122);
    assert_eq!(resolve(&resolver, &[]), Ok(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Ok(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Ok(child_121_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), Err(UnknownType("two")));
    assert_eq!(resolve(&resolver, &["one", "unk"]), Err(UnknownType("unk")));
    assert_eq!(resolve(&resolver, &["two"]), Ok(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), Err(UnknownType("one")));
    assert_eq!(resolve(&resolver, &["two", "unk"]), Err(UnknownType("unk")));
  }

  /// Checks that the type specified by a reference can be correctly found in a complex hierarchy of types
  mod resolve_type {
    use super::*;
    use pretty_assertions::assert_eq;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve<'n>(resolver: &TypeContext, ref_: &'n TypeName) -> Result<*const TypeSpec, ResolveError<'n>> {
      resolver.resolve_type(ref_).map(|t| t as *const TypeSpec)
    }

    #[test]
    fn relative() {
      let pkg = Package::test(setup());
      let ctx = PackageContext::new(&pkg);
      let ksy = pkg.files.values().next().unwrap();
      let context = ctx.for_file(ksy);

      let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
      let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

      let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
      let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

      let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
      let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

      let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
      let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

      let root_ptr = &ksy.root as *const TypeSpec;
      let child_11_ptr = child_11 as *const TypeSpec;
      let child_21_ptr = child_21 as *const TypeSpec;
      let child_121_ptr = child_121 as *const TypeSpec;

      // Kaitai path: root
      let rty_ref = TypeName {
        scope: Scope {
          absolute: false,
          path: Vec::new(),
        },
        name: "root",
      };
      // Kaitai path: unknown
      let unknown = TypeName {
        scope: Scope {
          absolute: false,
          path: Vec::new(),
        },
        name: "unknown",
      };

      // Kaitai path: one
      let one_ref = TypeName {
        scope: Scope {
          absolute: false,
          path: Vec::new(),
        },
        name: "one",
      };
      // Kaitai path: one::two
      let one_two = TypeName {
        scope: Scope {
          absolute: false,
          path: vec!["one"],
        },
        name: "two",
      };
      // Kaitai path: one::unknown
      let one_unk = TypeName {
        scope: Scope {
          absolute: false,
          path: vec!["one"],
        },
        name: "unknown",
      };

      // Kaitai path: two::one
      let two_one = TypeName {
        scope: Scope {
          absolute: false,
          path: vec!["two"],
        },
        name: "one",
      };

      let resolver = context.for_type(&ksy.root);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &two_one), Err(UnknownType("two")));

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Ok(child_121_ptr));

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_21_ptr));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Err(UnknownType("one")));

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_11_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Ok(child_121_ptr));

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_121_ptr));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Ok(child_121_ptr));

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_21_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Err(UnknownType("one")));

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_21_ptr));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Err(UnknownType("one")));

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_121_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Ok(child_121_ptr));

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &one_ref), Ok(child_121_ptr));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &two_one), Err(UnknownType("one")));
    }

    #[test]
    fn absolute() {
      let pkg = Package::test(setup());
      let ctx = PackageContext::new(&pkg);
      let ksy = pkg.files.values().next().unwrap();
      let context = ctx.for_file(ksy);

      let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
      let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

      let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
      let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

      let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
      let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

      let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
      let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

      let root_ptr = &ksy.root as *const TypeSpec;
      let child_1_ptr = child_1 as *const TypeSpec;
      let child_11_ptr = child_11 as *const TypeSpec;

      // Kaitai path: ::root
      let rty_ref = TypeName {
        scope: Scope {
          absolute: true,
          path: Vec::new(),
        },
        name: "root",
      };
      // Kaitai path: ::unknown
      let unknown = TypeName {
        scope: Scope {
          absolute: true,
          path: Vec::new(),
        },
        name: "unknown",
      };

      // Kaitai path: ::child_1
      let ch1_ref = TypeName {
        scope: Scope {
          absolute: true,
          path: Vec::new(),
        },
        name: "child_1",
      };
      // Kaitai path: ::child_1::one
      let ch1_one = TypeName {
        scope: Scope {
          absolute: true,
          path: vec!["child_1"],
        },
        name: "one",
      };
      // Kaitai path: ::child_1::unknown
      let ch1_unk = TypeName {
        scope: Scope {
          absolute: true,
          path: vec!["child_1"],
        },
        name: "unknown",
      };

      let resolver = context.for_type(&ksy.root);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &rty_ref), Ok(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
      assert_eq!(resolve(&resolver, &ch1_ref), Ok(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownType("unknown")));
    }
  }

  /// Checks that the enum specified by a name can be correctly found in a complex hierarchy of types
  #[test]
  fn resolve_enum_name() {
    let pkg = Package::test(setup());
    let ctx = PackageContext::new(&pkg);
    let ksy = pkg.files.values().next().unwrap();
    let context = ctx.for_file(ksy);

    let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
    let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

    let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
    let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

    let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
    let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

    let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
    let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

    let e_root = ksy.root.enums.as_ref().unwrap().get("e").expect("`e_root` not found") as *const Enum;
    let e_11 = child_11.enums.as_ref().unwrap().get("e").expect("`e_11` not found") as *const Enum;
    let e_12 = child_12.enums.as_ref().unwrap().get("e").expect("`e_12` not found") as *const Enum;
    let e_2 = child_2.enums.as_ref().unwrap().get("e").expect("`e_2` not found") as *const Enum;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve<'n>(
      resolver: &TypeContext,
      name: &'n str,
    ) -> Result<*const Enum, ResolveError<'n>> {
      resolver.resolve_enum_name(name).map(|e| e as *const Enum)
    }

    let resolver = context.for_type(&ksy.root);
    assert_eq!(resolve(&resolver, "e"), Ok(e_root));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_1);
    assert_eq!(resolve(&resolver, "e"), Ok(e_root));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_2);
    assert_eq!(resolve(&resolver, "e"), Ok(e_2));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_11);
    assert_eq!(resolve(&resolver, "e"), Ok(e_11));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_12);
    assert_eq!(resolve(&resolver, "e"), Ok(e_12));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_21);
    assert_eq!(resolve(&resolver, "e"), Ok(e_2));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_22);
    assert_eq!(resolve(&resolver, "e"), Ok(e_2));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_121);
    assert_eq!(resolve(&resolver, "e"), Ok(e_12));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));

    let resolver = context.for_type(child_122);
    assert_eq!(resolve(&resolver, "e"), Ok(e_12));
    assert_eq!(resolve(&resolver, "unknown"), Err(UnknownEnum("unknown")));
  }

  /// Checks that the enum specified by a reference can be correctly found in a complex hierarchy of types
  mod resolve_enum {
    use super::*;
    use pretty_assertions::assert_eq;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve<'n>(
      resolver: &TypeContext,
      ref_: &'n EnumRef,
    ) -> Result<*const Enum, ResolveError<'n>> {
      resolver.resolve_enum(ref_).map(|e| e as *const Enum)
    }

    #[test]
    fn relative() {
      let pkg = Package::test(setup());
      let ctx = PackageContext::new(&pkg);
      let ksy = pkg.files.values().next().unwrap();
      let context = ctx.for_file(ksy);

      let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
      let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

      let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
      let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

      let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
      let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

      let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
      let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

      let e_root = ksy.root.enums.as_ref().unwrap().get("e").expect("`e_root` not found") as *const Enum;
      let e_11 = child_11.enums.as_ref().unwrap().get("e").expect("`e_11` not found") as *const Enum;
      let e_12 = child_12.enums.as_ref().unwrap().get("e").expect("`e_12` not found") as *const Enum;
      let e_2 = child_2.enums.as_ref().unwrap().get("e").expect("`e_2` not found") as *const Enum;

      // Kaitai path: e
      let none = EnumRef {
        scope: Scope {
          absolute: false,
          path: Vec::new(),
        },
        name: "e",
      };
      // Kaitai path: one::e
      let one_e = EnumRef {
        scope: Scope {
          absolute: false,
          path: vec!["one"],
        },
        name: "e",
      };
      // Kaitai path: one::unknown
      let one_unk = EnumRef {
        scope: Scope {
          absolute: false,
          path: vec!["one"],
        },
        name: "unknown",
      };
      // Kaitai path: one::two::e
      let one_two = EnumRef {
        scope: Scope {
          absolute: false,
          path: vec!["one", "two"],
        },
        name: "e",
      };
      // Kaitai path: unknown::e
      let unknown = EnumRef {
        scope: Scope {
          absolute: false,
          path: vec!["unknown"],
        },
        name: "e",
      };

      let resolver = context.for_type(&ksy.root);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownType("one")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &one_e), Ok(e_11));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &none), Ok(e_2));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &none), Ok(e_11));
      assert_eq!(resolve(&resolver, &one_e), Ok(e_11));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &none), Ok(e_12));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &none), Ok(e_2));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &none), Ok(e_2));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &none), Ok(e_12));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &none), Ok(e_12));
      assert_eq!(resolve(&resolver, &one_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &one_two), Err(UnknownType("two")));
      assert_eq!(resolve(&resolver, &one_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
    }

    #[test]
    fn absolute() {
      let pkg = Package::test(setup());
      let ctx = PackageContext::new(&pkg);
      let ksy = pkg.files.values().next().unwrap();
      let context = ctx.for_file(ksy);

      let child_1 = ksy.root.types.as_ref().unwrap().get("child_1").expect("`child_1` not found");
      let child_2 = ksy.root.types.as_ref().unwrap().get("child_2").expect("`child_2` not found");

      let child_11 = child_1.types.as_ref().unwrap().get("one").expect("`child_11` not found");
      let child_12 = child_1.types.as_ref().unwrap().get("two").expect("`child_12` not found");

      let child_21 = child_2.types.as_ref().unwrap().get("one").expect("`child_21` not found");
      let child_22 = child_2.types.as_ref().unwrap().get("two").expect("`child_22` not found");

      let child_121 = child_12.types.as_ref().unwrap().get("one").expect("`child_121` not found");
      let child_122 = child_12.types.as_ref().unwrap().get("two").expect("`child_122` not found");

      let e_root = ksy.root.enums.as_ref().unwrap().get("e").expect("`e_root` not found") as *const Enum;
      let e_11 = child_11.enums.as_ref().unwrap().get("e").expect("`e_11` not found") as *const Enum;

      // Kaitai path: ::e
      let none = EnumRef {
        scope: Scope {
          absolute: true,
          path: Vec::new(),
        },
        name: "e",
      };
      // Kaitai path: ::child_1::e
      let ch1_e = EnumRef {
        scope: Scope {
          absolute: true,
          path: vec!["child_1"],
        },
        name: "e",
      };
      // Kaitai path: ::child_1::unknown
      let ch1_unk = EnumRef {
        scope: Scope {
          absolute: true,
          path: vec!["child_1"],
        },
        name: "unknown",
      };
      // Kaitai path: ::child_1::one::e
      let ch1_one = EnumRef {
        scope: Scope {
          absolute: true,
          path: vec!["child_1", "one"],
        },
        name: "e",
      };
      // Kaitai path: ::unknown::e
      let unknown = EnumRef {
        scope: Scope {
          absolute: true,
          path: vec!["unknown"],
        },
        name: "e",
      };

      let resolver = context.for_type(&ksy.root);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &none), Ok(e_root));
      assert_eq!(resolve(&resolver, &ch1_e), Err(UnknownEnum("e")));
      assert_eq!(resolve(&resolver, &ch1_one), Ok(e_11));
      assert_eq!(resolve(&resolver, &ch1_unk), Err(UnknownEnum("unknown")));
      assert_eq!(resolve(&resolver, &unknown), Err(UnknownType("unknown")));
    }
  }
}
