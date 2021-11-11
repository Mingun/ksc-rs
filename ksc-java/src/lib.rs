//! Compiler backend for generate a Java source code from the Kaitai Struct definition.

use proc_macro2::TokenStream;

/// Translates Kaitai Struct definition to a Java 8 source code
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct JavaGenerator;

/// Internal trait to facilitate translation of recursive structures
trait Translate {
  /// Translates self into a piece of Java code using settings in `gen`
  fn translate(&self, gen: &JavaGenerator) -> TokenStream;
}

/// Compile specified `source` as a java code and check that it has no errors.
/// The source should contain definition of the `KscJavaTest` class.
///
/// # Parameters
/// - `dir`: directory in which source file should be placed
/// - `source`: Java source code to compile
#[cfg(test)]
#[track_caller]
fn compile(dir: &std::path::Path, source: &str) {
  use std::fs::File;
  use std::io::Write;
  use std::process::Command;

  let path = std::env::temp_dir().join(dir);
  std::fs::create_dir_all(&path).expect("cannot create directory for test");

  let path = path.join("KscJavaTest.java");
  let mut java = File::create(&path).expect("cannot create temp file with java code");
  java.write_all(source.as_ref()).expect("cannot write Java source code to the file");

  let output = Command::new("javac")
    .arg(path.as_os_str())
    .output()
    .expect("failed to execute javac. Is JDK installed?");

  println!(r#"
status: {}
stdout(empty={}):
{}
stderr(empty={}):
{}
"#,
    output.status,
    output.stdout.is_empty(), String::from_utf8_lossy(&output.stdout),
    output.stderr.is_empty(), String::from_utf8_lossy(&output.stderr),
  );
  assert!(output.status.success());
}
