use crate::bytecode::consts::{Const, ConstKind, Object, Raw, Str};
use crate::bytecode::export::{CallSite, ExportInfo};
use crate::bytecode::insts::{Inst, Operand};
use crate::bytecode::module::StaticModule;
use crate::bytecode::{MAGIC, VERSION};
use leb128::write::{signed, unsigned};
use std::fs::File;
use std::io::{stderr, stdout, Result, Write};
use std::path::Path;

/// Bytecode file writer.
pub struct Writer<'w> {
  consts: &'w [Const],
  exports: &'w ExportInfo,
  insts: &'w [Inst],
}

impl<'w> Writer<'w> {
  /// Creates a new writer.
  pub fn new(module: &'w StaticModule) -> Self {
    Self {
      consts: &module.consts,
      exports: &module.exports,
      insts: &module.insts,
    }
  }

  /// Writes the bytecode to file by the given path.
  ///
  /// The corresponding file will be overwritten.
  /// If the file does not exist, a new file will be created.
  pub fn write_to_file<P>(&self, path: P) -> Result<()>
  where
    P: AsRef<Path>,
  {
    WriterImpl::new(&mut File::create(path)?, self).write()
  }

  /// Writes the bytecode to standard output.
  pub fn write_to_stdout(&self) -> Result<()> {
    WriterImpl::new(&mut stdout(), self).write()
  }

  /// Writes the bytecode to standard error.
  pub fn write_to_stderr(&self) -> Result<()> {
    WriterImpl::new(&mut stderr(), self).write()
  }

  /// Writes the bytecode to the given writer.
  pub fn write_to<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    WriterImpl::new(writer, self).write()
  }
}

impl<'w> From<&'w StaticModule> for Writer<'w> {
  fn from(module: &'w StaticModule) -> Self {
    Self::new(module)
  }
}

/// Implementation of writer.
struct WriterImpl<'w, W> {
  writer: &'w mut W,
  consts: &'w [Const],
  exports: &'w ExportInfo,
  insts: &'w [Inst],
}

impl<'w, W> WriterImpl<'w, W>
where
  W: Write,
{
  /// Create a new writer implementation from the given writer.
  fn new(writer: &'w mut W, w: &'w Writer<'w>) -> Self {
    Self {
      writer,
      consts: w.consts,
      exports: w.exports,
      insts: w.insts,
    }
  }

  /// Writes the bytecode.
  fn write(&mut self) -> Result<()> {
    self.write_magic()?;
    self.write_version()?;
    self.write_consts()?;
    self.write_exports()?;
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

  /// Writes exports.
  fn write_exports(&mut self) -> Result<()> {
    unsigned(&mut self.writer, self.exports.len() as u64)?;
    for (name, call_site) in self.exports {
      call_site.write(&mut self.writer)?;
      name.write(&mut self.writer)?;
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
    unsigned(writer, self.destructor)?;
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

impl WriteData for String {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    unsigned(writer, self.len() as u64)?;
    writer.write_all(self.as_bytes())?;
    Ok(())
  }
}

impl WriteData for CallSite {
  fn write<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    unsigned(writer, self.pc)?;
    unsigned(writer, self.num_args.into())?;
    unsigned(writer, self.num_rets)?;
    Ok(())
  }
}
