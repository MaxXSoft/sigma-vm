use clap::{ArgAction, Parser, ValueEnum};
use sigma_vm::interpreter::gc::{GarbageCollector, MarkSweep, Nothing};
use sigma_vm::interpreter::heap::{Checked, Heap, System};
use sigma_vm::interpreter::policy::{NoCheck, Policy, Strict, StrictAlign};
use sigma_vm::interpreter::vm::VM;
use std::str::FromStr;
use std::{env, fmt, process};

/// Sigma Virtual Machine.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the bytecode file, default to standard input.
  bytecode: Option<String>,

  /// Add directory to search path of module loader.
  #[arg(short = 'L', id = "PATH", action = ArgAction::Append)]
  search_paths: Vec<String>,

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

  /// Arguments for the bytecode module.
  #[arg(last = true)]
  args: Vec<String>,
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
    let (digits, unit) = match s.find(|c: char| !c.is_ascii_digit()) {
      Some(i) => (&s.as_str()[..i], Some(&s.as_str()[i..])),
      None => (s.as_str(), None),
    };
    let size: usize = digits.parse().unwrap();
    match unit {
      None | Some("b") => Ok(Self::Bytes(size)),
      Some("k") | Some("kb") => Ok(Self::Kilobytes(size)),
      Some("m") | Some("mb") => Ok(Self::Megabytes(size)),
      Some("g") | Some("gb") => Ok(Self::Gigabytes(size)),
      _ => Err("size can only end with B/KB/MB/GB"),
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
    PolicyArg::Strict => run_bytecode(args, Strict::<Checked<H>, GC>::new(gc_threshold)),
    PolicyArg::StrictAlign => run_bytecode(args, StrictAlign::<Checked<H>, GC>::new(gc_threshold)),
    PolicyArg::NoCheck => run_bytecode(args, NoCheck::<H, GC>::new(gc_threshold)),
  }
}

/// Runs the bytecode from the given policy and reader.
fn run_bytecode<P, V, E>(args: &CommandLineArgs, policy: P)
where
  P: Policy<Value = V, Error = E>,
  V: Clone,
  E: fmt::Debug + fmt::Display,
{
  // create VM instance
  let mut vm = VM::new(policy);
  vm.loader_mut()
    .add_search_path(ok_or_exit(env::current_dir(), PROMPT_LOADER));
  for path in &args.search_paths {
    vm.loader_mut().add_search_path(path);
  }
  // load module
  let module = ok_or_exit(
    match &args.bytecode {
      Some(path) => vm.load_from_path(path),
      None => vm.load_from_stdin(),
    },
    PROMPT_LOADER,
  );
  // run VM
  let rets = ok_or_exit(vm.run_main(module, &args.args), PROMPT_VM);
  ok_or_exit(vm.terminate(), PROMPT_VM);
  // return the first integer value
  if let Some(v) = rets.first() {
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

// Prompts for printing error messages.
const PROMPT_LOADER: &str = "Error loading module";
const PROMPT_VM: &str = "Sigma VM runtime error";
