use laps::input::InputStream;
use laps::reader::Reader;
use std::{fmt, io, process};
use xeno::front::parser::{AnnotatedItemOrEof, Parser};

/// Xeno programming language compiler.
#[derive(clap::Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the Xeno source file, default to standard input.
  source: Option<String>,

  /// Path to the output file, default to standard output.
  #[arg(short, long)]
  output: Option<String>,
}

fn main() {
  use clap::Parser;
  let args = CommandLineArgs::parse();
  // compile the source file
  match &args.source {
    Some(path) => compile(&args, ok_or_exit(Reader::from_path(path))),
    None => compile(&args, Reader::from_stdin()),
  }
}

/// Compiles the source file.
fn compile<R>(_: &CommandLineArgs, reader: Reader<R>)
where
  R: io::Read,
{
  let span = reader.span().clone();
  // run parser
  let mut parser = Parser::new(reader);
  loop {
    match parser.parse() {
      Ok(AnnotatedItemOrEof::AnnotatedItem(a)) => println!("{a:?}"),
      Ok(AnnotatedItemOrEof::Eof(_)) => break,
      Err(_) => {
        span.log_summary();
        return;
      }
    }
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
