use clap::{Parser, ValueEnum};
use sigma_vm::bytecode::reader::Reader;
use sigma_vm::interpreter::gc::{GarbageCollector, MarkSweep, Nothing};
use sigma_vm::interpreter::heap::{Checked, Heap, System};
use sigma_vm::interpreter::policy::{NoCheck, Policy, Strict, StrictAlign};
use sigma_vm::interpreter::vm::VM;
use std::str::FromStr;
use std::{env, fmt, io, process};

/// Sigma Virtual Machine.
#[derive(Parser, Debug)]
#[command(name = "sigma", version)]
struct CommandLineArgs {
  /// Path to the bytecode file.
  bytecode: Option<String>,

  /// Execution policy of the virtual machine.
  #[arg(value_enum, short, long, default_value_t = PolicyArg::StrictAlign)]
  policy: PolicyArg,

  /// Heap of the virtual machine.
  #[arg(value_enum, short = 'H', long, default_value_t = HeapArg::System)]
  heap: HeapArg,

  /// Garbage collector.
  #[arg(value_enum, short, long, default_value_t = GarbageCollectorArg::MarkSweep)]
  gc: GarbageCollectorArg,

  /// Garbage collector threshold.
  #[arg(short = 't', long, default_value_t = Size::Megabytes(256))]
  gc_threshold: Size,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
enum PolicyArg {
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
enum HeapArg {
  /// Heap that uses system's allocator to allocate memory.
  #[value(alias("s"))]
  System,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
enum GarbageCollectorArg {
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
  select_heap(&args);
}

/// Selects heap from the command line arguments.
fn select_heap(args: &CommandLineArgs) {
  match args.heap {
    HeapArg::System => select_gc::<System>(args),
  }
}

/// Selects garbage collector from the command line arguments.
fn select_gc<H>(args: &CommandLineArgs)
where
  H: Heap,
{
  match args.gc {
    GarbageCollectorArg::No => select_policy::<H, Nothing>(args),
    GarbageCollectorArg::MarkSweep => select_policy::<H, MarkSweep>(args),
  }
}

/// Selects policy from the command line arguments.
fn select_policy<H, GC>(args: &CommandLineArgs)
where
  H: Heap,
  GC: GarbageCollector,
{
  let gc_threshold = args.gc_threshold.into();
  match args.policy {
    PolicyArg::Strict => select_reader(args, Strict::<Checked<H>, GC>::new(gc_threshold)),
    PolicyArg::StrictAlign => select_reader(args, StrictAlign::<Checked<H>, GC>::new(gc_threshold)),
    PolicyArg::NoCheck => select_reader(args, NoCheck::<H, GC>::new(gc_threshold)),
  }
}

/// Select bytecode reader from the command line arguments.
fn select_reader<P, V, E>(args: &CommandLineArgs, policy: P)
where
  P: Policy<Value = V, Error = E>,
  V: Clone,
  E: fmt::Debug + fmt::Display,
{
  match &args.bytecode {
    Some(path) => run_bytecode(policy, ok_or_exit(Reader::from_path(path), PROMPT_READER)),
    None => run_bytecode(policy, Reader::from_stdin()),
  }
}

/// Runs the bytecode from the given policy and reader.
fn run_bytecode<P, V, E, R>(policy: P, mut reader: Reader<R>)
where
  P: Policy<Value = V, Error = E>,
  V: Clone,
  E: fmt::Debug + fmt::Display,
  R: io::Read,
{
  // read bytecode file
  ok_or_exit(reader.read(), PROMPT_READER);
  // create VM instance
  let mut vm = VM::from_reader(policy, reader);
  // push arguments
  for arg in env::args() {
    vm.add_str(&arg);
  }
  // run VM
  ok_or_exit(vm.run(), PROMPT_VM);
  // return the top most integer value on the stack
  if let Some(v) = vm.value_stack().last() {
    if let Ok(v) = P::get_int_ptr(v) {
      process::exit(v as i32);
    }
  }
  // no value to return, just return zero
  process::exit(0);
}

/// Returns the result, or print error message and exit on error.
fn ok_or_exit<T, E>(result: Result<T, E>, prompt: &str) -> T
where
  E: fmt::Display,
{
  match result {
    Ok(v) => v,
    Err(e) => {
      eprintln!("{prompt}: {e}");
      process::exit(-1);
    }
  }
}

const PROMPT_READER: &'static str = "Error reading bytecode";
const PROMPT_VM: &'static str = "Sigma VM runtime error";
