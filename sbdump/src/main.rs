mod dump;

use clap::Parser;
use sigma_vm::bytecode::reader::Reader;
use std::{fmt, fs, io, process};

/// Sigma VM bytecode dumper.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the bytecode module, default to standard input.
  bytecode: Option<String>,

  /// Path to the output of dumper, default to standard output.
  #[arg(short, long)]
  output: Option<String>,
}

fn main() {
  let args = CommandLineArgs::parse();
  // dump the input file
  match &args.bytecode {
    Some(path) => dump(&args, ok_or_exit(Reader::from_path(path), PROMPT_READER)),
    None => dump(&args, Reader::from_stdin()),
  }
}

/// Reads bytecode module from the given reader, and dumps to the output.
fn dump<R>(args: &CommandLineArgs, mut reader: Reader<R>)
where
  R: io::Read,
{
  // read the bytecode
  ok_or_exit(reader.read(), PROMPT_READER);
  // dump the bytecode
  let dumper = dump::BytecodeDumper::new(reader.into());
  let result = match &args.output {
    Some(path) => dumper.dump(&mut ok_or_exit(fs::File::create(path), PROMPT_DUMPER)),
    None => dumper.dump(&mut io::stdout()),
  };
  ok_or_exit(result, PROMPT_DUMPER);
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
const PROMPT_READER: &str = "Error reading bytecode module";
const PROMPT_DUMPER: &str = "Error dumping bytecode module";
