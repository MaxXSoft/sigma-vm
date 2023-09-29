use sigma_vm::bytecode::consts::{Const, ConstKind, Object, Raw, Str};
use sigma_vm::bytecode::export::NumArgs;
use sigma_vm::bytecode::insts::{Inst, Opcode, Operand};
use sigma_vm::bytecode::module::StaticModule;
use std::collections::{HashMap, HashSet};
use std::io::{Result, Write};

/// Bytecode dumper.
pub struct BytecodeDumper {
  module: StaticModule,
}

impl BytecodeDumper {
  /// Creates a new bytecode dumper.
  pub fn new(module: StaticModule) -> Self {
    Self { module }
  }

  /// Dumps to the given writer.
  pub fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    DumperImpl {
      writer,
      module: &self.module,
      exported_pcs: HashMap::new(),
    }
    .dump()
  }
}

/// Constant label.
const CONST_LABEL: &str = "const";

/// Instruction label.
const INST_LABEL: &str = "inst";

/// Implementation of the bytecode dumper.
struct DumperImpl<'d, W> {
  writer: &'d mut W,
  module: &'d StaticModule,
  exported_pcs: HashMap<u64, Vec<String>>,
}

impl<'d, W> DumperImpl<'d, W>
where
  W: Write,
{
  /// Dumps to the given writer.
  fn dump(&mut self) -> Result<()> {
    self.dump_consts()?;
    if !self.module.consts.is_empty() && !self.module.exports.is_empty() {
      writeln!(self.writer)?;
    }
    self.dump_exports()?;
    if !self.module.exports.is_empty() && !self.module.insts.is_empty() {
      writeln!(self.writer)?;
    }
    self.dump_insts()?;
    if !self.module.insts.is_empty() && !self.module.custom.is_empty() {
      writeln!(self.writer)?;
    }
    self.dump_custom()
  }

  /// Dumps the constant pool.
  fn dump_consts(&mut self) -> Result<()> {
    if !self.module.consts.is_empty() {
      writeln!(self.writer, "Section `consts`:")?;
      for (i, c) in self.module.consts.iter().enumerate() {
        self.write_label(CONST_LABEL, i, self.module.consts.len())?;
        c.dump(self.writer)?;
      }
    }
    Ok(())
  }

  /// Dumps the export information.
  fn dump_exports(&mut self) -> Result<()> {
    if !self.module.exports.is_empty() {
      writeln!(self.writer, "Section `exports`:")?;
      for (name, cs) in &self.module.exports {
        write!(self.writer, "  .export {name:?}, inst{}, ", cs.pc)?;
        cs.num_args.dump(self.writer)?;
        writeln!(self.writer, ", {}", cs.num_rets)?;
        // add to exported PCs
        self
          .exported_pcs
          .entry(cs.pc)
          .or_default()
          .push(name.clone());
      }
    }
    Ok(())
  }

  /// Dumps the instruction section.
  fn dump_insts(&mut self) -> Result<()> {
    if self.module.insts.is_empty() {
      return Ok(());
    }
    // get locations of all functions
    let funcs: HashSet<_> = self
      .module
      .insts
      .iter()
      .enumerate()
      .filter_map(|(pc, inst)| match inst {
        Inst::Call(opr) => Some((pc as i64 + opr) as usize),
        _ => None,
      })
      .collect();
    // dump instruction section
    writeln!(self.writer, "Section `insts`:")?;
    for (pc, inst) in self.module.insts.iter().enumerate() {
      // check if exported
      if let Some(names) = self.exported_pcs.get(&(pc as u64)) {
        if pc != 0 {
          writeln!(self.writer)?;
        }
        for name in names {
          Exported(name).dump(self.writer)?;
        }
      } else if funcs.contains(&pc) && pc != 0 {
        writeln!(self.writer)?;
      }
      // dump instruction
      self.write_label(INST_LABEL, pc, self.module.insts.len())?;
      (pc, inst).dump(self.writer)?;
    }
    Ok(())
  }

  /// Dumps the custom section.
  fn dump_custom(&mut self) -> Result<()> {
    if !self.module.custom.is_empty() {
      writeln!(self.writer, "Section `custom`:")?;
      for bytes in self.module.custom.chunks(32) {
        write!(self.writer, "  .bytes ")?;
        bytes.dump(self.writer)?;
        writeln!(self.writer)?;
      }
    }
    Ok(())
  }

  /// Writes padded label with the given index.
  fn write_label(&mut self, label: &str, index: usize, num_index: usize) -> Result<()> {
    let pad = (num_index.ilog10() - index.checked_ilog10().unwrap_or(0)) as usize;
    write!(self.writer, "  {:<pad$}{label}{index}: ", "")
  }
}

/// Helper trait for dumping data.
trait Dump {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write;
}

impl Dump for Const {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    // dump kind
    let kind = match self.kind() {
      ConstKind::I8 => "i8",
      ConstKind::U8 => "u8",
      ConstKind::I16 => "i16",
      ConstKind::U16 => "u16",
      ConstKind::I32 => "i32",
      ConstKind::U32 => "u32",
      ConstKind::I64 => "i64",
      ConstKind::U64 => "u64",
      ConstKind::F32 => "f32",
      ConstKind::F64 => "f64",
      ConstKind::Str => "str",
      ConstKind::Object => "object",
      ConstKind::Raw => "raw",
    };
    let pad = "object".len() - kind.len();
    write!(writer, "{:<pad$}.{kind} ", "")?;
    // dump data
    match self.kind() {
      ConstKind::I8 => unsafe { self.value::<i8>() }.unwrap().dump(writer),
      ConstKind::U8 => unsafe { self.value::<u8>() }.unwrap().dump(writer),
      ConstKind::I16 => unsafe { self.value::<i16>() }.unwrap().dump(writer),
      ConstKind::U16 => unsafe { self.value::<u16>() }.unwrap().dump(writer),
      ConstKind::I32 => unsafe { self.value::<i32>() }.unwrap().dump(writer),
      ConstKind::U32 => unsafe { self.value::<u32>() }.unwrap().dump(writer),
      ConstKind::I64 => unsafe { self.value::<i64>() }.unwrap().dump(writer),
      ConstKind::U64 => unsafe { self.value::<u64>() }.unwrap().dump(writer),
      ConstKind::F32 => unsafe { self.value::<f32>() }.unwrap().dump(writer),
      ConstKind::F64 => unsafe { self.value::<f64>() }.unwrap().dump(writer),
      ConstKind::Str => unsafe { self.str() }.unwrap().dump(writer),
      ConstKind::Object => unsafe { self.object() }.unwrap().dump(writer),
      ConstKind::Raw => unsafe { self.raw() }.unwrap().dump(writer),
    }?;
    writeln!(writer)
  }
}

macro_rules! impl_dump {
  ($ty:ty) => {
    impl Dump for $ty {
      fn dump<W>(&self, writer: &mut W) -> Result<()>
      where
        W: Write,
      {
        write!(writer, "{self:?}")
      }
    }
  };
}

impl_dump!(i8);
impl_dump!(u8);
impl_dump!(i16);
impl_dump!(u16);
impl_dump!(i32);
impl_dump!(u32);
impl_dump!(i64);
impl_dump!(u64);
impl_dump!(f32);
impl_dump!(f64);
impl_dump!(str);

impl Dump for Str<[u8]> {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    let mut bytes = &self.bytes;
    loop {
      match std::str::from_utf8(bytes) {
        Ok(s) => {
          s.dump(writer)?;
          break;
        }
        Err(e) => {
          // dump valid part
          let index = e.valid_up_to();
          if index != 0 {
            unsafe { std::str::from_utf8_unchecked(&bytes[..index]) }.dump(writer)?;
            write!(writer, ", ")?;
          }
          // dump invalid byte
          bytes[index..index + 1].dump(writer)?;
          // dump the rest bytes
          if index == bytes.len() - 1 {
            break;
          }
          write!(writer, ", ")?;
          bytes = &bytes[index + 1..];
        }
      };
    }
    Ok(())
  }
}

impl Dump for Object<[u64]> {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    write!(writer, "{}, {}", self.size, self.align)?;
    if self.destructor != 0 {
      write!(writer, ", inst{}", self.destructor)?;
    }
    write!(writer, ", [")?;
    for (i, offset) in self.managed_ptr.offsets.iter().enumerate() {
      if i != 0 {
        write!(writer, ", ")?;
      }
      write!(writer, "{offset}")?;
    }
    write!(writer, "]")
  }
}

impl Dump for Raw<[u8]> {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    self.bytes.dump(writer)
  }
}

impl Dump for [u8] {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    for (i, b) in self.iter().enumerate() {
      if i != 0 {
        write!(writer, ", ")?;
      }
      write!(writer, "0x{b:0>2x}")?;
    }
    Ok(())
  }
}

impl Dump for NumArgs {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    match self {
      Self::Variadic => write!(writer, "variadic"),
      Self::PlusOne(n) => write!(writer, "{}", n.get() - 1),
    }
  }
}

/// Exported symbol.
struct Exported<'e>(&'e String);

impl<'e> Dump for Exported<'e> {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    if self.0.chars().any(char::is_control) || self.0.is_empty() {
      writeln!(writer, "<{:?}>:", self.0)
    } else {
      writeln!(writer, "<{}>:", self.0)
    }
  }
}

impl Dump for (usize, &Inst) {
  fn dump<W>(&self, writer: &mut W) -> Result<()>
  where
    W: Write,
  {
    let (pc, inst) = *self;
    write!(writer, "{:?}", inst.opcode())?;
    // get operand kind
    enum Kind {
      Normal,
      Const,
      Cfi,
    }
    let kind = match inst.opcode() {
      Opcode::LdC
      | Opcode::LaC
      | Opcode::NewOC
      | Opcode::NewAC
      | Opcode::LoadC
      | Opcode::CallExtC => Kind::Const,
      Opcode::Bz | Opcode::BzNP | Opcode::Bnz | Opcode::Loop | Opcode::Jmp | Opcode::Call => {
        Kind::Cfi
      }
      _ => Kind::Normal,
    };
    // dump operand
    if let Some(opr) = inst.operand() {
      match opr {
        Operand::Signed(opr) => match kind {
          Kind::Normal => write!(writer, "\t{opr}")?,
          Kind::Cfi => write!(writer, "\t{INST_LABEL}{}", pc as i64 + opr)?,
          _ => unreachable!(),
        },
        Operand::Unsigned(opr) => match kind {
          Kind::Normal => write!(writer, "\t{opr}")?,
          Kind::Const => write!(writer, "\t{CONST_LABEL}{opr}")?,
          _ => unreachable!(),
        },
      }
    }
    writeln!(writer)
  }
}
