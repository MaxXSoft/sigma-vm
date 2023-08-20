mod anf;
mod back;
mod front;

use clap::{ArgAction, Parser};
use laps::reader::Reader;
use std::{fmt, io, process};

/// Lisp to Sigma VM bytecode compiler.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the Lisp source file, default to standard input.
  source: Option<String>,

  /// Add directory to search path for other Lisp modules.
  #[arg(short = 'I', id = "PATH", action = ArgAction::Append)]
  search_paths: Vec<String>,

  /// Path to the output bytecode file, default to standard output.
  #[arg(short, long)]
  output: Option<String>,
}

fn main() {
  let args = CommandLineArgs::parse();
  // compile the source file
  match &args.source {
    Some(path) => compile(&args, ok_or_exit(Reader::from_path(path))),
    None => compile(&args, Reader::from_stdin()),
  }
}

/// Compiles the source file.
fn compile<R>(args: &CommandLineArgs, reader: Reader<R>)
where
  R: io::Read,
{
  // run parser
  let mut parser = front::Parser::new(reader);
  let mut anf_gen = anf::Generator::new();
  loop {
    let elem = match parser.parse() {
      Ok(Some(elem)) => elem,
      Ok(None) => break,
      Err(_) => return,
    };
    // generate ANF
    let stmt = match anf_gen.generate(elem) {
      Ok(Some(stmt)) => stmt,
      Ok(None) => continue,
      Err(_) => return,
    };
    println!("{stmt:#?}");
  }
}

/// Returns the result, or print error message and exit on error.
fn ok_or_exit<T, E>(result: Result<T, E>) -> T
where
  E: fmt::Display,
{
  match result {
    Ok(v) => v,
    Err(e) => {
      eprintln!("{e}");
      process::exit(-1);
    }
  }
}
