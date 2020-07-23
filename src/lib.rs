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
    let _: Root = ksy.try_into().expect(&format!("incorrect KSY {}", resource));
  }
  /*TODO: включить ошибочные тесты, когда они прекратят падать (== будет сделан полный разбор)
  #[test_resources("test-data/formats_err/**/*.ksy")]
  fn error(resource: &str) {
    let file = File::open(resource).expect(&format!("can't read file {}", resource));
    let ksy: Result<Ksy, _> = serde_yaml::from_reader(file);
    match ksy {
      Ok(ksy) => {
        let root: Result<Root, _> = ksy.try_into();
        root.expect_err(&format!("correct KSY {}", resource));
      },
      _ => (),
    }
  }*/
}

#[test]
fn count() {
  use std::fs::File;
  use std::path::PathBuf;
  use parser::{Attribute, Ksy, TypeSpec};

  #[derive(Debug, Default, PartialEq)]
  #[allow(non_snake_case)]
  struct Counts {
    consume_true__include_true: usize,
    consume_true__include_false: usize,
    consume_false__include_true: usize,
    consume_false__include_false: usize,
  }
  impl Counts {
    fn inc_attr(&mut self, a: &Attribute) {
      match (a.consume, a.include) {
        ( true,  true) => self.consume_true__include_true +=1,
        ( true, false) => self.consume_true__include_false +=1,
        (false,  true) => self.consume_false__include_true +=1,
        (false, false) => self.consume_false__include_false +=1,
      }
    }
    fn inc_type(&mut self, t: &TypeSpec) {
      if let Some(seq) = &t.seq {
        for a in seq {
          self.inc_attr(&a);
        }
      }
      if let Some(seq) = &t.instances {
        for (_, i) in seq {
          self.inc_attr(&i.common);
        }
      }
    }
    fn inc(&mut self, t: &TypeSpec) {
      self.inc_type(&t);
      if let Some(types) = &t.types {
        for (_, t) in types {
          self.inc(&t);
        }
      }
    }
    fn count_file(&mut self, resource: PathBuf) {
      let file = File::open(resource).unwrap();
      let ksy: Ksy = serde_yaml::from_reader(file).unwrap();

      self.inc(&ksy.root);
    }
  }
  let mut counts = Counts::default();
  for file in glob::glob("formats/**/*.ksy").unwrap() {
    counts.count_file(file.unwrap());
  }
  assert_eq!(Counts::default(), counts);
}
