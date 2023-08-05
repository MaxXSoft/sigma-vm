use crate::bytecode::consts::Const;
use crate::bytecode::insts::Inst;
use crate::bytecode::MAGIC;
use leb128::write::{signed, unsigned};
use std::fs::File;
use std::io::{stderr, stdout, Result, Stderr, Stdout, Write};
use std::path::Path;

/// Bytecode file writer.
pub struct Writer<'w, W> {
  writer: W,
  consts: &'w [Const],
  insts: &'w [Inst],
}

impl<'w, W> Writer<'w, W> {
  /// Creates a new writer.
  pub fn new(writer: W, consts: &'w [Const], insts: &'w [Inst]) -> Self {
    Self {
      writer,
      consts,
      insts,
    }
  }
}

impl<'w, W> Writer<'w, W>
where
  W: Write,
{
  /// Writes the bytecode to file.
  pub fn write(&mut self) -> Result<()> {
    self.write_magic()?;
    self.write_consts()?;
    self.write_insts()
  }

  /// Writes the magic number.
  fn write_magic(&mut self) -> Result<()> {
    self.writer.write_all(&MAGIC)
  }

  /// Writes constants.
  fn write_consts(&mut self) -> Result<()> {
    unsigned(&mut self.writer, self.consts.len() as u64)?;
    for c in self.consts {
      todo!()
    }
    Ok(())
  }

  /// Writes instructions.
  fn write_insts(&mut self) -> Result<()> {
    unsigned(&mut self.writer, self.insts.len() as u64)?;
    for inst in self.insts {
      todo!()
    }
    Ok(())
  }
}

impl<'w> Writer<'w, File> {
  /// Creates a new writer from the given path.
  ///
  /// The corresponding file will be overwritten.
  /// If the file does not exist, a new file will be created.
  pub fn from_path<P>(path: P, consts: &'w [Const], insts: &'w [Inst]) -> Result<Self>
  where
    P: AsRef<Path>,
  {
    File::create(path).map(|f| Self::new(f, consts, insts))
  }
}

impl<'w> Writer<'w, Stdout> {
  /// Creates a new writer from stdout.
  pub fn from_stdout(consts: &'w [Const], insts: &'w [Inst]) -> Self {
    Self::new(stdout(), consts, insts)
  }
}

impl<'w> Writer<'w, Stderr> {
  /// Creates a new writer from stderr.
  pub fn from_stderr(consts: &'w [Const], insts: &'w [Inst]) -> Self {
    Self::new(stderr(), consts, insts)
  }
}
