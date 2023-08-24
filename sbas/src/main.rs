mod assembler;
mod front;

use clap::Parser;
use laps::input::InputStream;
use laps::reader::Reader;
use std::{fmt, fs, io, process};

/// Sigma VM bytecode assembler.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the bytecode assembly, default to standard input.
  assembly: Option<String>,

  /// Path to the output bytecode file, default to standard output.
  #[arg(short, long)]
  output: Option<String>,
}

fn main() {
  let args = CommandLineArgs::parse();
  // assemble the input file
  match &args.assembly {
    Some(path) => assemble(&args, ok_or_exit(Reader::from_path(path))),
    None => assemble(&args, Reader::from_stdin()),
  }
}

fn assemble<R>(args: &CommandLineArgs, reader: Reader<R>)
where
  R: io::Read,
{
  let span = reader.span().clone();
  let mut parser = front::Parser::new(reader);
  let mut assembler = assembler::Assembler::new();
  // run parser
  loop {
    let stmt = match parser.parse() {
      Ok(Some(stmt)) => stmt,
      Ok(None) => break,
      Err(_) => return,
    };
    // assemble
    if assembler.generate(stmt).is_err() {
      return;
    }
  }
  // write the output
  let _ = match &args.output {
    Some(path) => assembler.write(span, &mut ok_or_exit(fs::File::create(path))),
    None => assembler.write(span, &mut io::stdout()),
  };
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
