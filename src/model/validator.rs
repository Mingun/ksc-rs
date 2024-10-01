use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::model::Package;
use crate::parser::expressions::{Scope, TypeName};
use crate::parser::{Ksy, Name, TypeSpec};

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
  fn resolve_type(&self, ref_: &TypeName) -> Option<&'t TypeSpec> {
    if ref_.scope.absolute {
      self.file.for_root().resolve_scoped_type(&ref_.scope, ref_.name)
    } else {
      self.resolve_scoped_type(&ref_.scope, ref_.name)
    }
  }

  fn resolve_scoped_type(&self, scope: &Scope, name: &str) -> Option<&'t TypeSpec> {
    if scope.path.is_empty() {
      // just one name
      self.resolve_type_name(name)
    } else {
      // name with path or one name under root
      let ty = self.resolve_type_path(&scope.path)?;
      ty.types.as_ref()?.get(name)
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
  fn resolve_type_path(&self, path: &[&str]) -> Option<&'t TypeSpec> {
    let mut context = self.context;
    // Resolve types of each elements of a path
    if let [first, rest @ ..] = path {
      context = self.resolve_type_name(first)?;
      for name in rest {
        context = context.types.as_ref()?.get(*name)?;
      }
    }
    Some(context)
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
  fn resolve_type_name(&self, name: &str) -> Option<&'t TypeSpec> {
    let mut context = self.context;
    loop {
      let ctx = TypeId(context);
      // Root type does not have entry in self.parents, so handle it separately
      // TODO: Maybe create a fictive root type with real root and all imported types?
      let parent = if ctx == TypeId(&self.file.ksy.root) {
        if id_matches(&self.file.ksy.meta.id, name) {
          return Some(context);
        }
        None
      } else {
        // Because `context` is not root (checked above) missing parent means unknown type
        let parent = self.parent(&ctx)?;

        // Unqualified name firstly tried to resolve to the same type in which context
        // type resolution is performed, so we need to check our name first, but because
        // types does not store their name, we ask a parent about it.
        if let Some(types) = &parent.types {
          match types.get(name) {
            // If we found `context` under requested name in parent, return it
            Some(me) if ctx == TypeId(me) => return Some(context),
            _ => {},
          }
        }
        Some(parent)
      };

      // If current type have nested types, try to find in it
      if let Some(types) = &context.types {
        if let Some(t) = types.get(name) {
          return Some(t);
        }
      }

      // Otherwise try in parent (surrounding) type or in imported types if we under root already
      context = match parent {
        Some(parent) => parent,
        None => return Some(*self.file.imports.get(name)?),
      };
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
  use super::*;
  use pretty_assertions::assert_eq;

  fn setup() -> Ksy {
    serde_yml::from_str("
    meta:
      id: root
    types:
      child_1:
        types:
          one: {} # child_11
          two:    # child_12
            types:
              one: {} # child_121
              two: {} # child_122
      child_2:
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
    fn resolve(resolver: &TypeContext, name: &str) -> Option<*const TypeSpec> {
      resolver.resolve_type_name(name).map(|t| t as *const TypeSpec)
    }

    let resolver = context.for_type(&ksy.root);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), None);
    assert_eq!(resolve(&resolver, "two"), None);
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_1);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_11_ptr));
    assert_eq!(resolve(&resolver, "two"), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_2);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "one"), Some(child_21_ptr));
    assert_eq!(resolve(&resolver, "two"), Some(child_22_ptr));
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_11);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_12);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, "two"), Some(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_21);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Some(child_22_ptr));
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_22);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_21_ptr));
    assert_eq!(resolve(&resolver, "two"), Some(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_121);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "two"), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, "unk"), None);

    let resolver = context.for_type(child_122);
    assert_eq!(resolve(&resolver, "root"), Some(root_ptr));
    assert_eq!(resolve(&resolver, "child_1"), Some(child_1_ptr));
    assert_eq!(resolve(&resolver, "child_2"), Some(child_2_ptr));
    assert_eq!(resolve(&resolver, "one"), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, "two"), Some(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, "unk"), None);
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
    fn resolve(resolver: &TypeContext, path: &[&str]) -> Option<*const TypeSpec> {
      resolver.resolve_type_path(path).map(|t| t as *const TypeSpec)
    }

    let resolver = context.for_type(&ksy.root);
    assert_eq!(resolve(&resolver, &[]), Some(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one"]), None);
    assert_eq!(resolve(&resolver, &["one", "two"]), None); // 'one' not exist
    assert_eq!(resolve(&resolver, &["one", "unk"]), None); // 'one' not exist
    assert_eq!(resolve(&resolver, &["two"]), None);
    assert_eq!(resolve(&resolver, &["two", "one"]), None); // 'two' not exist
    assert_eq!(resolve(&resolver, &["two", "unk"]), None); // 'two' not exist

    let resolver = context.for_type(child_1);
    assert_eq!(resolve(&resolver, &[]), Some(child_1_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_11_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_2);
    assert_eq!(resolve(&resolver, &[]), Some(child_2_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_21_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_22_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), None);
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_11);
    assert_eq!(resolve(&resolver, &[]), Some(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_11_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_12);
    assert_eq!(resolve(&resolver, &[]), Some(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_12_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_21);
    assert_eq!(resolve(&resolver, &[]), Some(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_21_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_22_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), None);
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_22);
    assert_eq!(resolve(&resolver, &[]), Some(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_21_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_22_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), None);
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_121);
    assert_eq!(resolve(&resolver, &[]), Some(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_12_ptr));
    assert_eq!(resolve(&resolver, &["two", "one"]), Some(child_121_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);

    let resolver = context.for_type(child_122);
    assert_eq!(resolve(&resolver, &[]), Some(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["root"]), Some(root_ptr));
    assert_eq!(resolve(&resolver, &["one"]), Some(child_121_ptr));
    assert_eq!(resolve(&resolver, &["one", "two"]), None);
    assert_eq!(resolve(&resolver, &["one", "unk"]), None);
    assert_eq!(resolve(&resolver, &["two"]), Some(child_122_ptr)); // self-reference
    assert_eq!(resolve(&resolver, &["two", "one"]), None);
    assert_eq!(resolve(&resolver, &["two", "unk"]), None);
  }

  /// Checks that the type specified by a reference can be correctly found in a complex hierarchy of types
  mod resolve_type {
    use super::*;
    use pretty_assertions::assert_eq;

    /// We want to check that concrete objects is returned instead of checking that
    /// the object with the same structure is returned
    fn resolve(resolver: &TypeContext, ref_: &TypeName) -> Option<*const TypeSpec> {
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
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), None);
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), None);

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), Some(child_121_ptr));

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_21_ptr));
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), None);

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_11_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), Some(child_121_ptr));

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_121_ptr));
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), Some(child_121_ptr));

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_21_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), None);

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_21_ptr));
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), None);

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_121_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), Some(child_121_ptr));

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &one_ref), Some(child_121_ptr));
      assert_eq!(resolve(&resolver, &one_two), None);
      assert_eq!(resolve(&resolver, &one_unk), None);
      assert_eq!(resolve(&resolver, &two_one), None);
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
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_1);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr)); // self-reference
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_2);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_11);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_12);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_21);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_22);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_121);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);

      let resolver = context.for_type(child_122);
      assert_eq!(resolve(&resolver, &rty_ref), Some(root_ptr));
      assert_eq!(resolve(&resolver, &unknown), None);
      assert_eq!(resolve(&resolver, &ch1_ref), Some(child_1_ptr));
      assert_eq!(resolve(&resolver, &ch1_one), Some(child_11_ptr));
      assert_eq!(resolve(&resolver, &ch1_unk), None);
    }
  }
}
