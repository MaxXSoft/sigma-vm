use crate::bytecode::consts::{Const, ConstKind, Object, Raw, Str};
use crate::bytecode::insts::{Inst, Operand};
use crate::bytecode::{MAGIC, VERSION};
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

  /// Converts the current writer into the inner writer.
  pub fn into_inner(self) -> W {
    self.writer
  }
}

impl<'w, W> Writer<'w, W>
where
  W: Write,
{
  /// Writes the bytecode to file.
  pub fn write(&mut self) -> Result<()> {
    self.write_magic()?;
    self.write_version()?;
    self.write_consts()?;
    self.write_insts()
  }

  /// Writes the magic number.
  fn write_magic(&mut self) -> Result<()> {
    self.writer.write_all(&MAGIC)
  }

  /// Writes the version.
  fn write_version(&mut self) -> Result<()> {
    for val in VERSION {
      unsigned(&mut self.writer, val)?;
    }
    Ok(())
  }

  /// Writes constants.
  fn write_consts(&mut self) -> Result<()> {
    unsigned(&mut self.writer, self.consts.len() as u64)?;
    for c in self.consts {
      c.write(&mut self.writer)?;
    }
    Ok(())
  }

  /// Writes instructions.
  fn write_insts(&mut self) -> Result<()> {
    unsigned(&mut self.writer, self.insts.len() as u64)?;
    for inst in self.insts {
      (inst.opcode() as u8).write(&mut self.writer)?;
      match inst.operand() {
        Some(Operand::Signed(opr)) => signed(&mut self.writer, opr)?,
        Some(Operand::Unsigned(opr)) => unsigned(&mut self.writer, opr)?,
        None => 0,
      };
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

/// Helper trait for writing data to the given writer.
trait WriteData {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write;
}

/// Implements [`WriteData`] for the given type for writing little endian data.
macro_rules! impl_write_le {
  ($ty:ty) => {
    impl WriteData for $ty {
      fn write<W>(&self, writer: &mut W) -> Result<()>
      where
        W: Write,
      {
        writer.write_all(&self.to_le_bytes())
      }
    }
  };
}

impl_write_le!(i8);
impl_write_le!(u8);
impl_write_le!(i16);
impl_write_le!(u16);
impl_write_le!(i32);
impl_write_le!(u32);
impl_write_le!(i64);
impl_write_le!(u64);
impl_write_le!(f32);
impl_write_le!(f64);

impl WriteData for Const {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    (self.kind() as u8).write(writer)?;
    match self.kind() {
      ConstKind::I8 => unsafe { self.value::<i8>() }.unwrap().write(writer),
      ConstKind::U8 => unsafe { self.value::<u8>() }.unwrap().write(writer),
      ConstKind::I16 => unsafe { self.value::<i16>() }.unwrap().write(writer),
      ConstKind::U16 => unsafe { self.value::<u16>() }.unwrap().write(writer),
      ConstKind::I32 => unsafe { self.value::<i32>() }.unwrap().write(writer),
      ConstKind::U32 => unsafe { self.value::<u32>() }.unwrap().write(writer),
      ConstKind::I64 => unsafe { self.value::<i64>() }.unwrap().write(writer),
      ConstKind::U64 => unsafe { self.value::<u64>() }.unwrap().write(writer),
      ConstKind::F32 => unsafe { self.value::<f32>() }.unwrap().write(writer),
      ConstKind::F64 => unsafe { self.value::<f64>() }.unwrap().write(writer),
      ConstKind::Str => unsafe { self.str() }.unwrap().write(writer),
      ConstKind::Object => unsafe { self.object() }.unwrap().write(writer),
      ConstKind::Raw => unsafe { self.raw() }.unwrap().write(writer),
    }
  }
}

impl WriteData for Str<[u8]> {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    unsigned(writer, self.len)?;
    writer.write_all(&self.bytes)
  }
}

impl WriteData for Object<[u64]> {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    unsigned(writer, self.size)?;
    unsigned(writer, self.align)?;
    unsigned(writer, self.managed_ptr.len)?;
    for offset in &self.managed_ptr.offsets {
      unsigned(writer, *offset)?;
    }
    Ok(())
  }
}

impl WriteData for Raw<[u8]> {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    unsigned(writer, self.len)?;
    writer.write_all(&self.bytes)
  }
}
