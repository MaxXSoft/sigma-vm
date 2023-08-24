mod assembler;
mod front;

use clap::Parser;
use laps::reader::Reader;
use std::{io, process};

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
    Some(path) => match Reader::from_path(path) {
      Ok(reader) => assemble(&args, reader),
      Err(e) => {
        eprintln!("{e}");
        process::exit(-1);
      }
    },
    None => assemble(&args, Reader::from_stdin()),
  }
}

fn assemble<R>(args: &CommandLineArgs, reader: Reader<R>)
where
  R: io::Read,
{
  // run parser
  let mut parser = front::Parser::new(reader);
  let mut assembler = assembler::Assembler::new();
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
  todo!()
}
