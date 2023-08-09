use clap::{Parser, ValueEnum};

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
  #[arg(short = 't', long, default_value_t = 1024 * 1024 * 1024)]
  gc_threshold: usize,
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

fn main() {
  let args = CommandLineArgs::parse();
  println!("{args:#?}");
}
