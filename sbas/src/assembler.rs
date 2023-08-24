use crate::front::*;
use laps::return_error;
use laps::span::{Result, Span, Spanned};
use sigma_vm::bytecode::builder::Builder;
use sigma_vm::bytecode::consts::{Const, ObjectRef};
use sigma_vm::bytecode::export::CallSite;
use sigma_vm::bytecode::insts::{Inst, Opcode, Operand, OperandType};
use std::collections::HashMap;

/// Bytecode assembler.
pub struct Assembler {
  builder: Builder,
  cur_sec: Section,
  labels: HashMap<String, u64>,
}

impl Assembler {
  /// Creates a new assembler.
  pub fn new() -> Self {
    Self {
      builder: Builder::new(),
      cur_sec: Section::Consts,
      labels: HashMap::new(),
    }
  }

  /// Generates on the given statement.
  pub fn generate(&mut self, stmt: Statement) -> Result<()> {
    match stmt {
      Statement::SectionDecl(sec) => Ok(self.gen_section(sec)),
      Statement::Export(e) => self.gen_export(e),
      Statement::IntConst(c) => self.gen_int_const(c),
      Statement::FloatConst(c) => self.gen_float_const(c),
      Statement::StrConst(c) => self.gen_str_const(c),
      Statement::Object(o) => self.gen_object(o),
      Statement::RawConst(c) => self.gen_raw_const(c),
      Statement::Bytes(b) => self.gen_bytes(b),
      Statement::Instruction(i) => self.gen_inst(i),
      Statement::LabelDef(l) => self.gen_label_def(l),
    }
  }

  /// Generates on the given section declaration.
  fn gen_section(&mut self, sec: SectionDecl) {
    self.cur_sec = sec.sec.unwrap();
  }

  /// Generates on the given export information.
  fn gen_export(&mut self, export: Export) -> Result<()> {
    // get export information
    let span = export.span();
    let name = export.name.unwrap();
    let label = self.gen_label_ref(export.label);
    let num_args = match export.num_args {
      NumArgs::Variadic(_) => None,
      NumArgs::Num(n) => Some(n.unwrap()),
    };
    let num_rets = export.num_rets.unwrap();
    // insert to section
    match self.cur_sec {
      Section::Exports => {
        if !self.builder.export(name, label, num_args, num_rets) {
          return_error!(span, "duplicate export")
        }
      }
      Section::Custom => {
        let call_site = CallSite {
          pc: todo!(),
          num_args: num_args.into(),
          num_rets,
        };
        todo!()
      }
      _ => return_error!(span, "`.export` can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given integer constant.
  fn gen_int_const(&mut self, int_const: IntConst) -> Result<()> {
    let span = int_const.span();
    let value: u64 = int_const.value.unwrap();
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        let index = match int_const.kind {
          IntConstKind::I8(_) => self.builder.constant(value as i8),
          IntConstKind::U8(_) => self.builder.constant(value as u8),
          IntConstKind::I16(_) => self.builder.constant(value as i16),
          IntConstKind::U16(_) => self.builder.constant(value as u16),
          IntConstKind::I32(_) => self.builder.constant(value as i32),
          IntConstKind::U32(_) => self.builder.constant(value as u32),
          IntConstKind::I64(_) => self.builder.constant(value as i64),
          IntConstKind::U64(_) => self.builder.constant(value as u64),
        };
        todo!()
      }
      Section::Custom => match int_const.kind {
        IntConstKind::I8(_) => self.insert_to_custom(value as i8),
        IntConstKind::U8(_) => self.insert_to_custom(value as u8),
        IntConstKind::I16(_) => self.insert_to_custom(value as i16),
        IntConstKind::U16(_) => self.insert_to_custom(value as u16),
        IntConstKind::I32(_) => self.insert_to_custom(value as i32),
        IntConstKind::U32(_) => self.insert_to_custom(value as u32),
        IntConstKind::I64(_) => self.insert_to_custom(value as i64),
        IntConstKind::U64(_) => self.insert_to_custom(value as u64),
      },
      _ => return_error!(span, "integer constant can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given floating point constant.
  fn gen_float_const(&mut self, float_const: FloatConst) -> Result<()> {
    let span = float_const.span();
    let value: f64 = float_const.value.unwrap();
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        let index = match float_const.kind {
          FloatConstKind::F32(_) => self.builder.constant(value as f32),
          FloatConstKind::F64(_) => self.builder.constant(value as f64),
        };
        todo!()
      }
      Section::Custom => match float_const.kind {
        FloatConstKind::F32(_) => self.insert_to_custom(value as f32),
        FloatConstKind::F64(_) => self.insert_to_custom(value as f64),
      },
      _ => return_error!(span, "floating point constant can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given string constant.
  fn gen_str_const(&mut self, str_const: StrConst) -> Result<()> {
    let span = str_const.span();
    let value: String = str_const.value.unwrap();
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        let index = self.builder.constant(value);
        todo!()
      }
      Section::Custom => self.insert_to_custom(value),
      _ => return_error!(span, "string constant can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given object metadata.
  fn gen_object(&mut self, object: Object) -> Result<()> {
    let span = object.span();
    let offsets: Vec<_> = object.offsets.into_iter().map(|o| o.unwrap()).collect();
    let object = ObjectRef {
      size: object.size.unwrap(),
      align: object.align.unwrap(),
      destructor: todo!(),
      offsets: &offsets,
    };
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        let index = self.builder.constant(object);
        todo!()
      }
      Section::Custom => self.insert_to_custom(object),
      _ => return_error!(span, "object metadata can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given raw constant.
  fn gen_raw_const(&mut self, raw_const: RawConst) -> Result<()> {
    let span = raw_const.span();
    let value: Vec<_> = raw_const
      .values
      .into_iter()
      .flat_map(Self::gen_raw_value)
      .collect();
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        let index = self.builder.constant(value.as_slice());
        todo!()
      }
      Section::Custom => self.insert_to_custom(value.as_slice()),
      _ => return_error!(span, "raw constant can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given byte sequence.
  fn gen_bytes(&mut self, bytes: Bytes) -> Result<()> {
    let span = bytes.span();
    let values: Vec<_> = bytes
      .values
      .into_iter()
      .flat_map(Self::gen_raw_value)
      .collect();
    // insert to section
    match self.cur_sec {
      Section::Custom => self.builder.custom(values),
      _ => return_error!(span, "byte sequence can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given instruction.
  fn gen_inst(&mut self, inst: Instruction) -> Result<()> {
    let span = inst.span();
    // get opcode, check if is CFI
    let (opcode, cfi): (_, Option<fn(i64) -> Inst>) =
      match inst.opcode.unwrap::<String, _>().to_lowercase().as_str() {
        "nop" => (Opcode::Nop, None),
        "pushi" => (Opcode::PushI, None),
        "pushu" => (Opcode::PushU, None),
        "pop" => (Opcode::Pop, None),
        "dup" => (Opcode::Dup, None),
        "swap" => (Opcode::Swap, None),
        "ldb" => (Opcode::LdB, None),
        "ldbu" => (Opcode::LdBU, None),
        "ldh" => (Opcode::LdH, None),
        "ldhu" => (Opcode::LdHU, None),
        "ldw" => (Opcode::LdW, None),
        "ldwu" => (Opcode::LdWU, None),
        "ldd" => (Opcode::LdD, None),
        "ldp" => (Opcode::LdP, None),
        "ldbo" => (Opcode::LdBO, None),
        "ldbuo" => (Opcode::LdBUO, None),
        "ldho" => (Opcode::LdHO, None),
        "ldhuo" => (Opcode::LdHUO, None),
        "ldwo" => (Opcode::LdWO, None),
        "ldwuo" => (Opcode::LdWUO, None),
        "lddo" => (Opcode::LdDO, None),
        "ldpo" => (Opcode::LdPO, None),
        "ldv" => (Opcode::LdV, None),
        "ldg" => (Opcode::LdG, None),
        "ldc" => (Opcode::LdC, None),
        "lac" => (Opcode::LaC, None),
        "stb" => (Opcode::StB, None),
        "sth" => (Opcode::StH, None),
        "stw" => (Opcode::StW, None),
        "std" => (Opcode::StD, None),
        "stbo" => (Opcode::StBO, None),
        "stho" => (Opcode::StHO, None),
        "stwo" => (Opcode::StWO, None),
        "stdo" => (Opcode::StDO, None),
        "stv" => (Opcode::StV, None),
        "stg" => (Opcode::StG, None),
        "sta" => (Opcode::StA, None),
        "new" => (Opcode::New, None),
        "newo" => (Opcode::NewO, None),
        "newoc" => (Opcode::NewOC, None),
        "newa" => (Opcode::NewA, None),
        "newac" => (Opcode::NewAC, None),
        "load" => (Opcode::Load, None),
        "loadc" => (Opcode::LoadC, None),
        "loadm" => (Opcode::LoadM, None),
        "bz" => (Opcode::Bz, Some(Inst::Bz)),
        "bnz" => (Opcode::Bnz, Some(Inst::Bnz)),
        "jmp" => (Opcode::Jmp, Some(Inst::Jmp)),
        "call" => (Opcode::Call, Some(Inst::Call)),
        "callext" => (Opcode::CallExt, None),
        "callextc" => (Opcode::CallExtC, None),
        "ret" => (Opcode::Ret, None),
        "sys" => (Opcode::Sys, None),
        "break" => (Opcode::Break, None),
        "not" => (Opcode::Not, None),
        "lnot" => (Opcode::LNot, None),
        "and" => (Opcode::And, None),
        "or" => (Opcode::Or, None),
        "xor" => (Opcode::Xor, None),
        "shl" => (Opcode::Shl, None),
        "shr" => (Opcode::Shr, None),
        "sar" => (Opcode::Sar, None),
        "sext" => (Opcode::Sext, None),
        "zext" => (Opcode::Zext, None),
        "eq" => (Opcode::Eq, None),
        "ne" => (Opcode::Ne, None),
        "lt" => (Opcode::Lt, None),
        "le" => (Opcode::Le, None),
        "gt" => (Opcode::Gt, None),
        "ge" => (Opcode::Ge, None),
        "ltu" => (Opcode::LtU, None),
        "leu" => (Opcode::LeU, None),
        "gtu" => (Opcode::GtU, None),
        "geu" => (Opcode::GeU, None),
        "neg" => (Opcode::Neg, None),
        "add" => (Opcode::Add, None),
        "sub" => (Opcode::Sub, None),
        "mul" => (Opcode::Mul, None),
        "div" => (Opcode::Div, None),
        "divu" => (Opcode::DivU, None),
        "mod" => (Opcode::Mod, None),
        "modu" => (Opcode::ModU, None),
        "ltf" => (Opcode::LtF, None),
        "lef" => (Opcode::LeF, None),
        "gtf" => (Opcode::GtF, None),
        "gef" => (Opcode::GeF, None),
        "negf" => (Opcode::NegF, None),
        "addf" => (Opcode::AddF, None),
        "subf" => (Opcode::SubF, None),
        "mulf" => (Opcode::MulF, None),
        "divf" => (Opcode::DivF, None),
        "modf" => (Opcode::ModF, None),
        "ltd" => (Opcode::LtD, None),
        "led" => (Opcode::LeD, None),
        "gtd" => (Opcode::GtD, None),
        "ged" => (Opcode::GeD, None),
        "negd" => (Opcode::NegD, None),
        "addd" => (Opcode::AddD, None),
        "subd" => (Opcode::SubD, None),
        "muld" => (Opcode::MulD, None),
        "divd" => (Opcode::DivD, None),
        "modd" => (Opcode::ModD, None),
        "i2f" => (Opcode::I2F, None),
        "i2d" => (Opcode::I2D, None),
        "f2i" => (Opcode::F2I, None),
        "f2d" => (Opcode::F2D, None),
        "d2i" => (Opcode::D2I, None),
        "d2f" => (Opcode::D2F, None),
        "itf" => (Opcode::ITF, None),
        "itd" => (Opcode::ITD, None),
        "itp" => (Opcode::ITP, None),
        _ => return_error!(span, "unknown instruction"),
      };
    // get operand
    enum OprOrLabel {
      Opr(Operand),
      Label(u64),
    }
    let opr = match opcode.operand_type() {
      Some(OperandType::Signed) => match (inst.opr, cfi) {
        (Some(InstOperand::Imm(i)), None) => Some(OprOrLabel::Opr(Operand::Signed(
          i.unwrap::<u64, _>() as i64,
        ))),
        (Some(InstOperand::LabelRef(l)), Some(_)) => Some(OprOrLabel::Label(self.gen_label_ref(l))),
        (_, None) => return_error!(span, "expected integer operand"),
        (_, Some(_)) => return_error!(span, "expected label reference"),
      },
      Some(OperandType::Unsigned) => match inst.opr {
        Some(InstOperand::Imm(i)) => Some(OprOrLabel::Opr(Operand::Unsigned(i.unwrap()))),
        _ => return_error!(span, "expected integer operand"),
      },
      None if inst.opr.is_none() => None,
      _ => return_error!(span, "expected no operand"),
    };
    // insert instruction to section
    match self.cur_sec {
      Section::Insts => match opr {
        Some(OprOrLabel::Opr(opr)) => self.builder.inst(Inst::new(opcode, Some(opr))),
        Some(OprOrLabel::Label(l)) => self.builder.cfi(cfi.unwrap(), l),
        None => self.builder.inst(Inst::new(opcode, None)),
      },
      Section::Custom => todo!(),
      _ => return_error!(span, "instruction can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given label definition.
  fn gen_label_def(&mut self, label_def: LabelDef) -> Result<()> {
    todo!("temporary label, constant label, custom label")
  }

  /// Generates on the given label reference.
  fn gen_label_ref(&mut self, label_ref: LabelRef) -> u64 {
    todo!()
  }

  /// Generates on the given raw value.
  fn gen_raw_value(raw_value: RawValue) -> Vec<u8> {
    match raw_value {
      RawValue::Str(s) => s.unwrap::<String, _>().bytes().collect(),
      RawValue::Byte(b) => vec![b.unwrap::<u64, _>() as u8],
    }
  }

  /// Inserts the given constant to the custom section.
  fn insert_to_custom<C>(&mut self, c: C)
  where
    C: Into<Const>,
  {
    let c: Const = c.into();
    self.builder.custom([c.kind() as u8]);
    self.builder.custom(c.data().iter().copied());
  }
}

/// Label information.
struct LabelInfo {
  id: u64,
  span: Span,
}
