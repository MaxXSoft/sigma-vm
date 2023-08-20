use crate::bytecode::consts::{Const, ConstKind, Object, Raw, Str};
use crate::bytecode::export::{Export, ExportInfo};
use crate::bytecode::insts::{Inst, Opcode, Operand, OperandType};
use crate::bytecode::module::StaticModule;
use crate::bytecode::{Section, MAGIC, VERSION};
use crate::utils::{alloc_uninit, Unsized};
use leb128::read::{signed, unsigned, Error as LebError};
use std::alloc::LayoutError;
use std::fs::File;
use std::io::{stdin, Error as IoError, ErrorKind, Read, Result as IoResult, Stdin};
use std::path::Path;
use std::{fmt, mem};

/// Error that can occur when reading bytecode files.
#[derive(Debug)]
pub enum Error {
  /// I/O error.
  IO(IoError),
  /// Invalid magic number.
  InvalidMagic,
  /// Incompatible version.
  IncompatibleVersion,
  /// Unknown section.
  UnknownSection,
  /// Integer overflow.
  Overflow,
  /// Unknown constant kind.
  UnknownConstKind(u8),
  /// Layout error.
  Layout(LayoutError),
  /// Invalid export function name.
  InvalidName,
  /// Duplicate export.
  DuplicateExport,
  /// Unknown opcode.
  UnknownOpcode(u8),
}

impl From<LebError> for Error {
  fn from(e: LebError) -> Self {
    match e {
      LebError::IoError(e) => Self::IO(e),
      LebError::Overflow => Self::Overflow,
    }
  }
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::IO(io) => write!(f, "{io}"),
      Self::InvalidMagic => write!(f, "invalid magic number"),
      Self::IncompatibleVersion => write!(f, "incompatible version"),
      Self::UnknownSection => write!(f, "unknown section"),
      Self::Overflow => write!(f, "integer overflow when reading bytecode"),
      Self::UnknownConstKind(k) => write!(f, "unknown constant kind: {k}"),
      Self::Layout(l) => write!(f, "{l}"),
      Self::InvalidName => write!(f, "invalid export function name"),
      Self::DuplicateExport => write!(f, "duplicate export"),
      Self::UnknownOpcode(o) => write!(f, "unknown opcode: {o}"),
    }
  }
}

/// Result type for reading bytecode files.
pub type Result<T> = std::result::Result<T, Error>;

/// Bytecode file reader.
pub struct Reader<R> {
  reader: R,
  consts: Vec<Const>,
  exports: ExportInfo,
  insts: Vec<Inst>,
  custom: Vec<u8>,
}

impl<R> Reader<R> {
  /// Creates a new reader.
  pub fn new(reader: R) -> Self {
    Self {
      reader,
      consts: vec![],
      exports: ExportInfo::new(),
      insts: vec![],
      custom: vec![],
    }
  }

  /// Returns a reference to the constant pool.
  pub fn consts(&self) -> &[Const] {
    &self.consts
  }

  /// Returns a reference to the export information.
  pub fn exports(&self) -> &ExportInfo {
    &self.exports
  }

  /// Returns a reference to the instruction list.
  pub fn insts(&self) -> &[Inst] {
    &self.insts
  }

  /// Returns a reference to the custom metadata.
  pub fn custom(&self) -> &[u8] {
    &self.custom
  }
}

impl<R> Reader<R>
where
  R: Read,
{
  /// Reads the bytecode from file.
  pub fn read(&mut self) -> Result<()> {
    self.check_magic()?;
    self.check_version()?;
    self.read_sections()
  }

  /// Checks the magic number.
  fn check_magic(&mut self) -> Result<()> {
    let mut magic = [0; MAGIC.len()];
    self.reader.fill(&mut magic)?;
    if magic == MAGIC {
      Ok(())
    } else {
      Err(Error::InvalidMagic)
    }
  }

  /// Checks the version number.
  fn check_version(&mut self) -> Result<()> {
    let version: [u64; 3] = [
      self.reader.read_leb128()?,
      self.reader.read_leb128()?,
      self.reader.read_leb128()?,
    ];
    if version[0] != VERSION[0] || (version[0] == 0 && version[1..] != VERSION[1..]) {
      Err(Error::IncompatibleVersion)
    } else {
      Ok(())
    }
  }

  /// Reads sections.
  fn read_sections(&mut self) -> Result<()> {
    loop {
      // read section kind
      let mut buf = [0];
      match self.reader.read_exact(&mut buf) {
        Ok(_) => {}
        Err(e) if e.kind() == ErrorKind::UnexpectedEof => break Ok(()),
        Err(e) => return Err(Error::IO(e)),
      }
      // read by kind
      match Section::from_byte(buf[0]) {
        Some(Section::Consts) => self.read_consts()?,
        Some(Section::Exports) => self.read_exports()?,
        Some(Section::Insts) => self.read_insts()?,
        Some(Section::Custom) => self.read_custom()?,
        None => return Err(Error::UnknownSection),
      }
    }
  }

  /// Reads constants.
  fn read_consts(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    self.consts.reserve_exact(len as usize);
    for _ in 0..len {
      self.consts.push(self.reader.read_const()?);
    }
    Ok(())
  }

  /// Reads export information.
  fn read_exports(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    self.exports.reserve(len as usize);
    for _ in 0..len {
      let export = self.reader.read_export()?;
      let name = export.name.to_str().ok_or(Error::InvalidName)?;
      if self
        .exports
        .insert(name.into(), export.call_site.clone())
        .is_some()
      {
        return Err(Error::DuplicateExport);
      }
    }
    Ok(())
  }

  /// Reads instructions.
  fn read_insts(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    self.insts.reserve_exact(len as usize);
    for _ in 0..len {
      self.insts.push(self.reader.read_inst()?);
    }
    Ok(())
  }

  /// Reads custom metadata.
  fn read_custom(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    let prev_len = self.custom.len();
    self.custom.resize(prev_len + len as usize, 0);
    self.reader.fill(&mut self.custom[prev_len..])
  }
}

impl Reader<File> {
  /// Creates a new reader from the given path.
  pub fn from_path<P>(path: P) -> IoResult<Self>
  where
    P: AsRef<Path>,
  {
    File::open(path).map(Self::new)
  }
}

impl Reader<Stdin> {
  /// Creates a new reader from stdin.
  pub fn from_stdin() -> Self {
    Self::new(stdin())
  }
}

impl<'a> From<&'a [u8]> for Reader<&'a [u8]> {
  /// Creates a new reader from the given byte array.
  fn from(bytes: &'a [u8]) -> Self {
    Self::new(bytes)
  }
}

impl<R> From<Reader<R>> for StaticModule {
  fn from(reader: Reader<R>) -> Self {
    Self {
      consts: reader.consts.into_boxed_slice(),
      exports: reader.exports,
      insts: reader.insts.into_boxed_slice(),
    }
  }
}

/// Helper trait for reading data from reader.
trait ReadData {
  /// Reads bytes to fill the given buffer.
  fn fill(&mut self, buf: &mut [u8]) -> Result<()>;

  /// Reads an LEB128 integer.
  fn read_leb128<T>(&mut self) -> Result<T>
  where
    T: ReadLeb128;

  /// Reads a little endian integer.
  fn read_le<T>(&mut self) -> Result<T>
  where
    T: ReadLe;

  /// Reads a constant.
  fn read_const(&mut self) -> Result<Const>;

  /// Reads an export entry.
  fn read_export(&mut self) -> Result<Box<Export<[u8]>>>;

  /// Reads a instruction.
  fn read_inst(&mut self) -> Result<Inst>;
}

impl<R> ReadData for R
where
  R: Read,
{
  fn fill(&mut self, buf: &mut [u8]) -> Result<()> {
    self.read_exact(buf).map_err(Error::IO)
  }

  fn read_leb128<T>(&mut self) -> Result<T>
  where
    T: ReadLeb128,
  {
    T::read(self)
  }

  fn read_le<T>(&mut self) -> Result<T>
  where
    T: ReadLe,
  {
    T::read(self)
  }

  fn read_const(&mut self) -> Result<Const> {
    Const::read(self)
  }

  fn read_export(&mut self) -> Result<Box<Export<[u8]>>> {
    let pc = self.read_leb128()?;
    let num_args: u64 = self.read_leb128()?;
    let num_rets = self.read_leb128()?;
    let len = self.read_leb128()?;
    let size = Export::<[u8]>::size(len);
    let mut data: Box<Export<[u8]>> =
      unsafe { alloc_uninit(size, Export::<[u8]>::ALIGN, len as usize) }.map_err(Error::Layout)?;
    data.call_site.pc = pc;
    data.call_site.num_args = num_args.into();
    data.call_site.num_rets = num_rets;
    data.name.len = len;
    self.fill(&mut data.name.bytes)?;
    Ok(data)
  }

  fn read_inst(&mut self) -> Result<Inst> {
    let opc = self.read_le()?;
    let opcode = Opcode::try_from(opc).map_err(|_| Error::UnknownOpcode(opc))?;
    let opr = match opcode.operand_type() {
      Some(OperandType::Signed) => Some(Operand::Signed(self.read_leb128()?)),
      Some(OperandType::Unsigned) => Some(Operand::Unsigned(self.read_leb128()?)),
      None => None,
    };
    Ok(Inst::new(opcode, opr))
  }
}

/// Helper trait for reading LEB128 integer.
trait ReadLeb128: Sized {
  fn read<R>(reader: &mut R) -> Result<Self>
  where
    R: Read;
}

impl ReadLeb128 for i64 {
  fn read<R>(reader: &mut R) -> Result<Self>
  where
    R: Read,
  {
    signed(reader).map_err(Error::from)
  }
}

impl ReadLeb128 for u64 {
  fn read<R>(reader: &mut R) -> Result<Self>
  where
    R: Read,
  {
    unsigned(reader).map_err(Error::from)
  }
}

/// Helper trait for reading little endian data.
trait ReadLe: Sized {
  fn read<R>(reader: &mut R) -> Result<Self>
  where
    R: Read;
}

/// Helper macro for implementing [`ReadLe`] for the given type.
macro_rules! impl_read_le {
  ($ty:ty) => {
    impl ReadLe for $ty {
      fn read<R>(reader: &mut R) -> Result<Self>
      where
        R: Read,
      {
        let mut buf = [0; mem::size_of::<Self>()];
        reader.fill(&mut buf)?;
        Ok(Self::from_le_bytes(buf))
      }
    }
  };
}

impl_read_le!(i8);
impl_read_le!(u8);
impl_read_le!(i16);
impl_read_le!(u16);
impl_read_le!(i32);
impl_read_le!(u32);
impl_read_le!(i64);
impl_read_le!(u64);
impl_read_le!(f32);
impl_read_le!(f64);

/// Helper trait for reading constants.
trait ReadConst {
  type Const;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read;
}

impl ReadConst for Const {
  type Const = Self;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    match ConstKind::read(reader)? {
      ConstKind::I8 => <i8 as ReadConst>::read(reader),
      ConstKind::U8 => <u8 as ReadConst>::read(reader),
      ConstKind::I16 => <i16 as ReadConst>::read(reader),
      ConstKind::U16 => <u16 as ReadConst>::read(reader),
      ConstKind::I32 => <i32 as ReadConst>::read(reader),
      ConstKind::U32 => <u32 as ReadConst>::read(reader),
      ConstKind::I64 => <i64 as ReadConst>::read(reader),
      ConstKind::U64 => <u64 as ReadConst>::read(reader),
      ConstKind::F32 => <f32 as ReadConst>::read(reader),
      ConstKind::F64 => <f64 as ReadConst>::read(reader),
      ConstKind::Str => Str::<[u8]>::read(reader),
      ConstKind::Object => Object::<[u64]>::read(reader),
      ConstKind::Raw => Raw::<[u8]>::read(reader),
    }
  }
}

impl ReadConst for ConstKind {
  type Const = Self;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    let kind = reader.read_le()?;
    Self::try_from(kind).map_err(|_| Error::UnknownConstKind(kind))
  }
}

/// Helper macro for implementing [`ReadConst`] for the given type.
macro_rules! impl_read_const {
  ($ty:ty) => {
    impl ReadConst for $ty {
      type Const = Const;

      fn read<R>(reader: &mut R) -> Result<Self::Const>
      where
        R: Read,
      {
        reader.read_le::<Self>().map(From::from)
      }
    }
  };
}

impl_read_const!(i8);
impl_read_const!(u8);
impl_read_const!(i16);
impl_read_const!(u16);
impl_read_const!(i32);
impl_read_const!(u32);
impl_read_const!(i64);
impl_read_const!(u64);
impl_read_const!(f32);
impl_read_const!(f64);

impl ReadConst for Str<[u8]> {
  type Const = Const;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    let len = reader.read_leb128()?;
    let size = Self::size(len);
    let mut data: Box<Self> =
      unsafe { alloc_uninit(size, Self::ALIGN, len as usize) }.map_err(Error::Layout)?;
    data.len = len;
    reader.fill(&mut data.bytes)?;
    Ok(unsafe { Const::new(ConstKind::Str, data, size) })
  }
}

impl ReadConst for Object<[u64]> {
  type Const = Const;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    let size = reader.read_leb128()?;
    let align = reader.read_leb128()?;
    let destructor = reader.read_leb128()?;
    let len = reader.read_leb128()?;
    let total_size = Self::size(len);
    let mut data: Box<Self> =
      unsafe { alloc_uninit(total_size, Self::ALIGN, len as usize) }.map_err(Error::Layout)?;
    data.size = size;
    data.align = align;
    data.destructor = destructor;
    data.managed_ptr.len = len;
    for i in 0..len as usize {
      data.managed_ptr.offsets[i] = reader.read_leb128()?;
    }
    Ok(unsafe { Const::new(ConstKind::Object, data, total_size) })
  }
}

impl ReadConst for Raw<[u8]> {
  type Const = Const;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    let mut c = Str::<[u8]>::read(reader)?;
    // safety: layout of `Raw` and `Str` must be the same.
    unsafe { c.set_kind(ConstKind::Raw) };
    Ok(c)
  }
}
