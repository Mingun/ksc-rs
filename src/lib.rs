//! Kaitai struct definition compiler for rust in pure rust.
#![deny(missing_docs)]

pub mod error;
pub mod identifiers;
pub mod model;
pub mod parser;

/// Expected, that https://github.com/kaitai-io/kaitai_struct_formats was checkout to
/// crate root directory, next to `src`.
#[cfg(test)]
mod formats {
  use crate::model::Root;
  use crate::parser::Ksy;
  use std::convert::TryInto;
  use std::fs::File;
  use test_generator::test_resources;

  #[test_resources("formats/**/*.ksy")]
  fn parse(resource: &str) {
    let file = File::open(resource).expect(&format!("can't read file {}", resource));
    let ksy: Ksy = serde_yml::from_reader(file).expect(&format!("invalid file {}", resource));
    let _: Root = ksy.try_into().expect(&format!("incorrect KSY {}", resource));
  }
}
