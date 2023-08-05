use crate::bytecode::consts::{Const, ConstKind, Object, Raw, Str};
use crate::bytecode::insts::{Inst, Opcode, Operand, OperandType};
use crate::bytecode::MAGIC;
use leb128::read::{signed, unsigned, Error as LebError};
use std::alloc::{self, Layout, LayoutError};
use std::fs::File;
use std::io::{stdin, Error as IoError, Read, Result as IoResult, Stdin};
use std::mem;
use std::path::Path;
use std::ptr::{self, Pointee};

/// Error that can occur when reading bytecode files.
#[derive(Debug)]
pub enum Error {
  /// I/O error.
  IO(IoError),
  /// Invalid magic number.
  InvalidMagic,
  /// Integer overflow.
  Overflow,
  /// Unknown constant kind.
  UnknownConstKind,
  /// Layout error.
  Layout(LayoutError),
  /// Unknown opcode.
  UnknownOpcode,
}

impl From<LebError> for Error {
  fn from(e: LebError) -> Self {
    match e {
      LebError::IoError(e) => Self::IO(e),
      LebError::Overflow => Self::Overflow,
    }
  }
}

/// Result type for reading bytecode files.
pub type Result<T> = std::result::Result<T, Error>;

/// Bytecode file reader.
pub struct Reader<R> {
  reader: R,
  consts: Vec<Const>,
  insts: Vec<Inst>,
}

impl<R> Reader<R> {
  /// Creates a new reader.
  pub fn new(reader: R) -> Self {
    Self {
      reader,
      consts: vec![],
      insts: vec![],
    }
  }

  /// Returns a reference to the constant pool.
  pub fn consts(&self) -> &[Const] {
    &self.consts
  }

  /// Returns a reference to the instruction list.
  pub fn insts(&self) -> &[Inst] {
    &self.insts
  }

  /// Converts the reader into a constant pool and an instruction list.
  pub fn into_consts_insts(self) -> (Box<[Const]>, Box<[Inst]>) {
    (
      self.consts.into_boxed_slice(),
      self.insts.into_boxed_slice(),
    )
  }
}

impl<R> Reader<R>
where
  R: Read,
{
  /// Reads the bytecode from file.
  pub fn read(&mut self) -> Result<()> {
    self.check_magic()?;
    self.read_consts()?;
    self.read_insts()
  }

  /// Checks the magic number.
  fn check_magic(&mut self) -> Result<()> {
    let mut magic = [0; 4];
    self.reader.fill(&mut magic)?;
    if magic == MAGIC {
      Ok(())
    } else {
      Err(Error::InvalidMagic)
    }
  }

  /// Reads constants.
  fn read_consts(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    self.consts.clear();
    self.consts.reserve_exact(len as usize);
    for _ in 0..len {
      self.consts.push(self.reader.read_const()?);
    }
    Ok(())
  }

  /// Reads instructions.
  fn read_insts(&mut self) -> Result<()> {
    let len: u64 = self.reader.read_leb128()?;
    self.insts.clear();
    self.insts.reserve_exact(len as usize);
    for _ in 0..len {
      self.insts.push(self.reader.read_inst()?);
    }
    Ok(())
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

  fn read_inst(&mut self) -> Result<Inst> {
    let opcode = Opcode::from_byte(self.read_le()?).ok_or(Error::UnknownOpcode)?;
    let opr = match opcode.opr_type() {
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
    Self::from_byte(reader.read_le()?).ok_or(Error::UnknownConstKind)
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

/// Creates an uninitialized `T` on heap, applies the given metadata.
///
/// # Safety
///
/// The created data must be set a valid value first.
unsafe fn alloc_uninit<T>(
  size: usize,
  align: usize,
  metadata: <T as Pointee>::Metadata,
) -> Result<Box<T>>
where
  T: ?Sized,
{
  let layout = Layout::from_size_align(size, align).map_err(Error::Layout)?;
  let ptr = alloc::alloc(layout);
  if ptr.is_null() {
    alloc::handle_alloc_error(layout);
  }
  Ok(Box::from_raw(ptr::from_raw_parts_mut(
    ptr as *mut _,
    metadata,
  )))
}

impl ReadConst for Str<[u8]> {
  type Const = Const;

  fn read<R>(reader: &mut R) -> Result<Self::Const>
  where
    R: Read,
  {
    let len = reader.read_leb128()?;
    let len_size = mem::size_of_val(&len);
    let size = len_size + len as usize;
    let mut data: Box<Self> = unsafe { alloc_uninit(size, len_size, len as usize)? };
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
    let len = reader.read_leb128()?;
    let size_size = mem::size_of_val(&size);
    let total_size = size_size + mem::size_of_val(&len) + len as usize * mem::size_of::<u64>();
    let mut data: Box<Self> = unsafe { alloc_uninit(total_size, size_size, len as usize)? };
    data.size = size;
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
