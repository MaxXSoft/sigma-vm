mod anf;
mod back;
mod front;

use clap::Parser;
use laps::reader::Reader;
use sigma_vm::bytecode::writer::Writer;
use std::{fmt, io, process};

/// Lisp to Sigma VM bytecode compiler.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the Lisp source file, default to standard input.
  source: Option<String>,

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
  let mut parser = front::Parser::new(reader);
  let mut anf_gen = anf::Generator::new();
  let mut module_gen = back::Generator::new();
  // run parser
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
    // generate on the ANF
    module_gen.generate_on(stmt);
  }
  // check if there are undefined variables
  if anf_gen.check_undefined_vars() {
    return;
  }
  // generate module and write to the output
  let module = module_gen.generate();
  let writer = Writer::new(&module);
  ok_or_exit(match &args.output {
    Some(path) => writer.write_to_file(path),
    None => writer.write_to_stdout(),
  });
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
