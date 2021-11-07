use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;
use std::str::FromStr;
use int_enum::IntEnum;
use structopt::StructOpt;

#[repr(u8)]
#[derive(Debug, Clone, Copy, IntEnum)]
enum CppStandard {
  Cpp98 = 98,
  Cpp11 = 11,
}
impl FromStr for CppStandard {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s.parse::<u8>() {
      Ok(98) => Ok(Self::Cpp98),
      Ok(11) => Ok(Self::Cpp11),
      _ => Err("only 98 and 11 are allowed"),
    }
  }
}
impl Default for CppStandard {
  fn default() -> Self { Self::Cpp98 }
}
impl Display for CppStandard {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", self.int_value())
  }
}

#[derive(Debug, StructOpt)]
#[structopt(name = "ksc")]
struct Cli {
  /// List of files to compile
  #[structopt(parse(from_os_str))]
  src_files: Vec<PathBuf>,

  /// Target languages
  #[structopt(short, long)]
  target: Vec<String>,

  /// Output directory (filenames will be auto-generated)
  #[structopt(short, long)]
  outdir: Option<PathBuf>,

  /// `.ksy` library search path(s) for imports
  #[structopt(short = "I", long = "import-path", env = "KSPATH")]
  imports: Vec<String>,

  /// C++ namespace (C++ only, default: none)
  #[structopt(long)]
  cpp_namespace: Option<String>,

  /// C++ standard to target (C++ only, supported: 98, 11)
  #[structopt(long, default_value)]
  cpp_standard: CppStandard,

  /// Go package (Go only, default: none)
  #[structopt(long)]
  go_package: Option<String>,

  /// Java package (Java only, default: root package)
  #[structopt(long)]
  java_package: Option<String>,

  /// Java class to be invoked in fromFile() helper (default: ${RuntimeConfig().java.fromFileClass})
  #[structopt(long)]
  java_from_file_class: Option<String>,

  /// .NET Namespace (.NET only, default: Kaitai)
  #[structopt(long)]
  dotnet_namespace: Option<String>,

  /// PHP Namespace (PHP only, default: root package)
  #[structopt(long)]
  php_namespace: Option<String>,

  /// Python package (Python only, default: root package)
  #[structopt(long)]
  python_package: Option<String>,

  /// Path of Nim runtime module (Nim only, default: kaitai_struct_nim_runtime)
  #[structopt(long)]
  nim_module: Option<String>,

  /// Directory of opaque Nim modules (Nim only, default: directory of generated module)
  #[structopt(long)]
  nim_opaque: Option<String>,

  /// Opaque types allowed, default: false
  #[structopt(long)]
  opaque_types: bool,

  /// `ksc` throws exceptions instead of human-readable error messages
  #[structopt(long)]
  ksc_exceptions: bool,

  /// Output compilation results as JSON to stdout
  #[structopt(long)]
  ksc_json_output: bool,

  /// Verbose output
  #[structopt(long)]
  verbose: Vec<String>,

  /// Disable auto-running `_read` in constructor
  #[structopt(long)]
  no_auto_read: bool,

  /// `_read` remembers attribute positions in stream
  #[structopt(long)]
  read_pos: bool,

  /// Same as `--no-auto-read --read-pos` (useful for visualization tools)
  #[structopt(long)]
  debug: bool,
}

fn main() {
  let opt = Cli::from_args();
  println!("{:#?}", opt);
}
