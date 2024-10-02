//! Kaitai struct definition compiler for rust in pure rust.
#![deny(missing_docs)]

pub mod error;
pub mod identifiers;
pub mod model;
pub mod parser;

/// Expected, that https://github.com/kaitai-io/kaitai_struct_formats was checkout to
/// crate root directory, next to `src`.
/// Expected, that https://github.com/kaitai-io/kaitai_struct_tests was checkout to
/// the `test-data` in the crate root directory, next to `src`.
#[cfg(test)]
mod formats {
  use crate::model::{ImportLoader, Package};
  use crate::parser::{Import, Ksy};
  use std::fs::File;
  use std::io;
  use std::path::{Path, PathBuf};
  use test_generator::test_resources;

  #[derive(Debug)]
  // Values of enumeration is not used directly, but still valuable if test fail
  #[allow(dead_code)]
  enum LoaderError {
    Io(String, io::Error),
    Parse(serde_yml::Error),
  }

  fn to_path(mut base: PathBuf, import: &Import) -> PathBuf {
    for comp in &import.components {
      base.push(comp);
    }
    base.push(&import.name.0);
    base.set_extension("ksy");
    base
  }

  struct FileLoader {
    /// Bases for absolute imports
    abs_roots: Vec<PathBuf>,
  }
  impl ImportLoader for FileLoader {
    type Id = PathBuf;
    type Error = LoaderError;

    fn new_id(&mut self, mut base: Self::Id, import: &Import) -> Self::Id {
      if import.absolute {
        for base in self.abs_roots.iter().cloned() {
          let path = to_path(base, import);
          // Required for tests which expect that absolute import will look into several places
          // test-data/formats/imports_abs.ksy
          // test-data/formats/imports_abs_abs.ksy
          // test-data/formats/imports_abs_rel.ksy
          // test-data/formats/ks_path/for_abs_imports/imported_and_abs.ksy
          if path.exists() {
            return path;
          }
        }
        // In tests we should find file in one of the provided roots
        panic!("cannot find file for {import}");
      } else {
        // Remove name of the file from which we are imported
        base.pop();
        to_path(base, import)
      }
    }

    fn load(&mut self, id: Self::Id) -> Result<Ksy, Self::Error> {
      let display = id.display().to_string();
      let file = File::open(id).map_err(|e| LoaderError::Io(display, e))?;
      serde_yml::from_reader(file).map_err(LoaderError::Parse)
    }
  }

  #[test_resources("formats/**/*.ksy")]
  #[test_resources("test-data/formats/**/*.ksy")]
  fn parse(resource: &str) {
    let file = File::open(resource).expect(&format!("can't read file {}", resource));
    let ksy: Ksy = serde_yml::from_reader(file).expect(&format!("invalid file {}", resource));

    // Currently this file cannot be successfully parsed in non-compatible mode
    // Unfortunately, negative glob patterns are not allowed in test_resources,
    // as well as adding #[ignore], so we filter out test here
    // TODO: Fix file `type_ternary_2nd_falsy.ksy` in upstream and enable testing
    // it in non-compatible mode
    #[cfg(not(feature = "compatible"))]
    if resource.ends_with("type_ternary_2nd_falsy.ksy") {
      return;
    }
    // Contains underscores in numbers, which are threated as strings according to YAML 1.2 rules
    // which serde_yml applies, but original compiler apply YAML 1.1 rules.
    // See https://github.com/kaitai-io/kaitai_struct/issues/1132
    if resource.ends_with("renderware_binary_stream.ksy") {
      return;
    }
    // Invalid spec - defines some enum values as strings instead of numbers
    // TODO: remove when https://github.com/kaitai-io/kaitai_struct_formats/pull/701 merged
    if resource.ends_with("nt_mdt.ksy") {
      return;
    }

    let id = Path::new(resource).to_path_buf();
    // Directory with `ksc` crate
    let ksc_dir = Path::new(env!("CARGO_MANIFEST_DIR"));

    let name = ksy.meta.id.clone().expect("missing `meta/id`");
    let package = Package::new(id, name, ksy, FileLoader {
      abs_roots: vec![
        ksc_dir.join("formats"),
        ksc_dir.join("test-data").join("formats"),
        ksc_dir.join("test-data").join("formats").join("ks_path"),
      ],
    }).expect(&format!("invalid imports in {}", resource));

    package.validate().expect(&format!("incorrect KSY {}", resource));
  }

  #[test_resources("test-data/formats_err/**/*.ksy")]
  fn error(resource: &str) {
    let file = File::open(resource).expect(&format!("can't read file {}", resource));
    let _ksy: Result<Ksy, _> = serde_yml::from_reader(file);

    // Error formats not yet passed the validation tests because validation not
    // finished yet.
    // TODO: Enable testing `formats_err` when validation would be finished
    /*match ksy {
      Ok(ksy) => {
        let root: Result<Root, _> = ksy.try_into();
        root.expect_err(&format!("correct KSY {}", resource));
      },
      _ => (),
    }*/
  }
}
