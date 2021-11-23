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
  use crate::model::Root;
  use crate::parser::Ksy;
  use std::convert::TryInto;
  use std::fs::File;
  use test_generator::test_resources;

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

    let _: Root = ksy.try_into().expect(&format!("incorrect KSY {}", resource));
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
