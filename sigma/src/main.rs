use clap::{Parser, ValueEnum};
use std::fmt;
use std::str::FromStr;

/// Sigma Virtual Machine.
#[derive(Parser, Debug)]
#[command(name = "sigma", version)]
struct CommandLineArgs {
  /// Path to the bytecode file.
  bytecode: String,

  /// Execution policy of the virtual machine.
  #[arg(value_enum, short, long, default_value_t = Policy::StrictAlign)]
  policy: Policy,

  /// Heap of the virtual machine.
  #[arg(value_enum, short = 'H', long, default_value_t = Heap::System)]
  heap: Heap,

  /// Garbage collector.
  #[arg(value_enum, short, long, default_value_t = GarbageCollector::MarkSweep)]
  gc: GarbageCollector,

  /// Garbage collector threshold.
  #[arg(short = 't', long, default_value_t = Size::Megabytes(256))]
  gc_threshold: Size,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
enum Policy {
  /// Checks type of values, division, and memory out of bounds.
  #[value(alias("s"))]
  Strict,
  /// Checks type of values, division, memory out of bounds and memory alignment.
  #[value(alias("sa"))]
  StrictAlign,
  /// Disable all checkings.
  #[value(alias("nc"))]
  NoCheck,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
enum Heap {
  /// Heap that uses system's allocator to allocate memory.
  #[value(alias("s"))]
  System,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
enum GarbageCollector {
  /// No garbage collector.
  #[value(alias("n"))]
  No,
  /// Mark-sweep garbage collector.
  #[value(alias("ms"))]
  MarkSweep,
}

/// Size in different units: B, KB, MB, GB.
#[derive(Clone, Copy, Debug)]
enum Size {
  Bytes(usize),
  Kilobytes(usize),
  Megabytes(usize),
  Gigabytes(usize),
}

impl From<Size> for usize {
  fn from(size: Size) -> Self {
    match size {
      Size::Bytes(b) => b,
      Size::Kilobytes(kb) => kb * 1024,
      Size::Megabytes(mb) => mb * 1024 * 1024,
      Size::Gigabytes(gb) => gb * 1024 * 1024 * 1024,
    }
  }
}

impl FromStr for Size {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let s = s.to_ascii_lowercase();
    let digits = match s.find(|c: char| !c.is_ascii_digit()) {
      Some(i) => &s.as_str()[..i],
      None => &s,
    };
    let size: usize = digits.parse().unwrap();
    if s.len() == digits.len() || s.ends_with("b") {
      Ok(Self::Bytes(size))
    } else if s.ends_with("k") || s.ends_with("kb") {
      Ok(Self::Kilobytes(size))
    } else if s.ends_with("m") || s.ends_with("mb") {
      Ok(Self::Megabytes(size))
    } else if s.ends_with("g") || s.ends_with("gb") {
      Ok(Self::Gigabytes(size))
    } else {
      Err("size can only end with B/KB/MB/GB")
    }
  }
}

impl fmt::Display for Size {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Bytes(b) => write!(f, "{b}B"),
      Self::Kilobytes(kb) => write!(f, "{kb}KB"),
      Self::Megabytes(mb) => write!(f, "{mb}MB"),
      Self::Gigabytes(gb) => write!(f, "{gb}GB"),
    }
  }
}

fn main() {
  let args = CommandLineArgs::parse();
  println!("{args:#?}");
}
