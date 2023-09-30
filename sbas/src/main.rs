mod assembler;
mod front;

use clap::Parser;
use laps::input::InputStream;
use laps::reader::Reader;
use std::io::{stdout, Read, Write};
use std::process::{exit, Command, Stdio};
use std::{env, fmt, fs};

/// Sigma VM bytecode assembler.
#[derive(Parser, Debug)]
#[command(version, about)]
struct CommandLineArgs {
  /// Path to the bytecode assembly, default to standard input.
  assembly: Option<String>,

  /// Path to the output bytecode file, default to standard output.
  #[arg(short, long)]
  output: Option<String>,

  /// Use C preprocessor to preprocess the input file.
  ///
  /// The C compiler will be detected automatically,
  /// current supports only GCC and Clang.
  #[arg(short, long, default_value_t = false)]
  preprocess: bool,
}

fn main() {
  let args = CommandLineArgs::parse();
  // preprocess the input file
  match &args.assembly {
    Some(path) => preprocess(&args, ok_or_exit(Reader::from_path(path))),
    None => preprocess(&args, Reader::from_stdin()),
  }
}

fn preprocess<R>(args: &CommandLineArgs, reader: Reader<R>)
where
  R: Read,
{
  if args.preprocess {
    // read from the reader
    let mut buf = Vec::new();
    ok_or_exit(reader.into_inner().read_to_end(&mut buf));
    // detect C compiler
    let cc = if let Some(cc) = env::var_os("CC") {
      cc
    } else {
      "cc".into()
    };
    // run preprocessor
    let mut child = ok_or_exit(
      Command::new(cc)
        .args(["-E", "-x", "assembler-with-cpp", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn(),
    );
    ok_or_exit(child.stdin.as_mut().unwrap().write_all(&buf));
    // read output from preprocessor
    let output = ok_or_exit(child.wait_with_output());
    if !output.status.success() {
      eprintln!("Failed to run preprocessor");
      exit(-1);
    }
    // assemble the input file
    assemble(args, Reader::from(output.stdout.as_slice()))
  } else {
    assemble(args, reader)
  }
}

fn assemble<R>(args: &CommandLineArgs, reader: Reader<R>)
where
  R: Read,
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
    None => assembler.write(span, &mut stdout()),
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
      exit(-1);
    }
  }
}
