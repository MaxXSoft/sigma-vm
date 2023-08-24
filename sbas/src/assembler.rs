use crate::front::*;
use laps::return_error;
use laps::span::{Result, Span, Spanned};
use sigma_vm::bytecode::builder::{Builder, CfInstConstructor};
use sigma_vm::bytecode::consts::{Const, ObjectRef};
use sigma_vm::bytecode::export::CallSite;
use sigma_vm::bytecode::insts::{Inst, Opcode, Operand, OperandType};
use std::collections::HashMap;

/// Bytecode assembler.
pub struct Assembler {
  builder: Builder,
  cur_sec: Section,
  labels: HashMap<String, LabelInfo>,
  last_const_label: Option<String>,
}

impl Assembler {
  /// Creates a new assembler.
  pub fn new() -> Self {
    Self {
      builder: Builder::new(),
      cur_sec: Section::Consts,
      labels: HashMap::new(),
      last_const_label: None,
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
    let label = self.gen_inst_label_ref(export.label)?;
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
      Section::Consts => match int_const.kind {
        IntConstKind::I8(_) => self.insert_to_const(value as i8),
        IntConstKind::U8(_) => self.insert_to_const(value as u8),
        IntConstKind::I16(_) => self.insert_to_const(value as i16),
        IntConstKind::U16(_) => self.insert_to_const(value as u16),
        IntConstKind::I32(_) => self.insert_to_const(value as i32),
        IntConstKind::U32(_) => self.insert_to_const(value as u32),
        IntConstKind::I64(_) => self.insert_to_const(value as i64),
        IntConstKind::U64(_) => self.insert_to_const(value as u64),
      },
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
      Section::Consts => match float_const.kind {
        FloatConstKind::F32(_) => self.insert_to_const(value as f32),
        FloatConstKind::F64(_) => self.insert_to_const(value as f64),
      },
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
      Section::Consts => self.insert_to_const(value),
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
      Section::Consts => self.insert_to_const(object),
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
      Section::Consts => self.insert_to_const(value.as_slice()),
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
    // get kind of instruction
    enum InstKind {
      Normal(Opcode),
      Const(fn(u64) -> Inst),
      Cfi(CfInstConstructor),
    }
    let kind = match inst.opcode.unwrap::<String, _>().to_lowercase().as_str() {
      "nop" => InstKind::Normal(Opcode::Nop),
      "pushi" => InstKind::Normal(Opcode::PushI),
      "pushu" => InstKind::Normal(Opcode::PushU),
      "pop" => InstKind::Normal(Opcode::Pop),
      "dup" => InstKind::Normal(Opcode::Dup),
      "swap" => InstKind::Normal(Opcode::Swap),
      "ldb" => InstKind::Normal(Opcode::LdB),
      "ldbu" => InstKind::Normal(Opcode::LdBU),
      "ldh" => InstKind::Normal(Opcode::LdH),
      "ldhu" => InstKind::Normal(Opcode::LdHU),
      "ldw" => InstKind::Normal(Opcode::LdW),
      "ldwu" => InstKind::Normal(Opcode::LdWU),
      "ldd" => InstKind::Normal(Opcode::LdD),
      "ldp" => InstKind::Normal(Opcode::LdP),
      "ldbo" => InstKind::Normal(Opcode::LdBO),
      "ldbuo" => InstKind::Normal(Opcode::LdBUO),
      "ldho" => InstKind::Normal(Opcode::LdHO),
      "ldhuo" => InstKind::Normal(Opcode::LdHUO),
      "ldwo" => InstKind::Normal(Opcode::LdWO),
      "ldwuo" => InstKind::Normal(Opcode::LdWUO),
      "lddo" => InstKind::Normal(Opcode::LdDO),
      "ldpo" => InstKind::Normal(Opcode::LdPO),
      "ldv" => InstKind::Normal(Opcode::LdV),
      "ldg" => InstKind::Normal(Opcode::LdG),
      "ldc" => InstKind::Const(Inst::LdC),
      "lac" => InstKind::Const(Inst::LaC),
      "stb" => InstKind::Normal(Opcode::StB),
      "sth" => InstKind::Normal(Opcode::StH),
      "stw" => InstKind::Normal(Opcode::StW),
      "std" => InstKind::Normal(Opcode::StD),
      "stbo" => InstKind::Normal(Opcode::StBO),
      "stho" => InstKind::Normal(Opcode::StHO),
      "stwo" => InstKind::Normal(Opcode::StWO),
      "stdo" => InstKind::Normal(Opcode::StDO),
      "stv" => InstKind::Normal(Opcode::StV),
      "stg" => InstKind::Normal(Opcode::StG),
      "sta" => InstKind::Normal(Opcode::StA),
      "new" => InstKind::Normal(Opcode::New),
      "newo" => InstKind::Normal(Opcode::NewO),
      "newoc" => InstKind::Const(Inst::NewOC),
      "newa" => InstKind::Normal(Opcode::NewA),
      "newac" => InstKind::Const(Inst::NewAC),
      "load" => InstKind::Normal(Opcode::Load),
      "loadc" => InstKind::Const(Inst::LoadC),
      "loadm" => InstKind::Normal(Opcode::LoadM),
      "bz" => InstKind::Cfi(Inst::Bz),
      "bnz" => InstKind::Cfi(Inst::Bnz),
      "jmp" => InstKind::Cfi(Inst::Jmp),
      "call" => InstKind::Cfi(Inst::Call),
      "callext" => InstKind::Normal(Opcode::CallExt),
      "callextc" => InstKind::Const(Inst::CallExtC),
      "ret" => InstKind::Normal(Opcode::Ret),
      "sys" => InstKind::Normal(Opcode::Sys),
      "break" => InstKind::Normal(Opcode::Break),
      "not" => InstKind::Normal(Opcode::Not),
      "lnot" => InstKind::Normal(Opcode::LNot),
      "and" => InstKind::Normal(Opcode::And),
      "or" => InstKind::Normal(Opcode::Or),
      "xor" => InstKind::Normal(Opcode::Xor),
      "shl" => InstKind::Normal(Opcode::Shl),
      "shr" => InstKind::Normal(Opcode::Shr),
      "sar" => InstKind::Normal(Opcode::Sar),
      "sext" => InstKind::Normal(Opcode::Sext),
      "zext" => InstKind::Normal(Opcode::Zext),
      "eq" => InstKind::Normal(Opcode::Eq),
      "ne" => InstKind::Normal(Opcode::Ne),
      "lt" => InstKind::Normal(Opcode::Lt),
      "le" => InstKind::Normal(Opcode::Le),
      "gt" => InstKind::Normal(Opcode::Gt),
      "ge" => InstKind::Normal(Opcode::Ge),
      "ltu" => InstKind::Normal(Opcode::LtU),
      "leu" => InstKind::Normal(Opcode::LeU),
      "gtu" => InstKind::Normal(Opcode::GtU),
      "geu" => InstKind::Normal(Opcode::GeU),
      "neg" => InstKind::Normal(Opcode::Neg),
      "add" => InstKind::Normal(Opcode::Add),
      "sub" => InstKind::Normal(Opcode::Sub),
      "mul" => InstKind::Normal(Opcode::Mul),
      "div" => InstKind::Normal(Opcode::Div),
      "divu" => InstKind::Normal(Opcode::DivU),
      "mod" => InstKind::Normal(Opcode::Mod),
      "modu" => InstKind::Normal(Opcode::ModU),
      "ltf" => InstKind::Normal(Opcode::LtF),
      "lef" => InstKind::Normal(Opcode::LeF),
      "gtf" => InstKind::Normal(Opcode::GtF),
      "gef" => InstKind::Normal(Opcode::GeF),
      "negf" => InstKind::Normal(Opcode::NegF),
      "addf" => InstKind::Normal(Opcode::AddF),
      "subf" => InstKind::Normal(Opcode::SubF),
      "mulf" => InstKind::Normal(Opcode::MulF),
      "divf" => InstKind::Normal(Opcode::DivF),
      "modf" => InstKind::Normal(Opcode::ModF),
      "ltd" => InstKind::Normal(Opcode::LtD),
      "led" => InstKind::Normal(Opcode::LeD),
      "gtd" => InstKind::Normal(Opcode::GtD),
      "ged" => InstKind::Normal(Opcode::GeD),
      "negd" => InstKind::Normal(Opcode::NegD),
      "addd" => InstKind::Normal(Opcode::AddD),
      "subd" => InstKind::Normal(Opcode::SubD),
      "muld" => InstKind::Normal(Opcode::MulD),
      "divd" => InstKind::Normal(Opcode::DivD),
      "modd" => InstKind::Normal(Opcode::ModD),
      "i2f" => InstKind::Normal(Opcode::I2F),
      "i2d" => InstKind::Normal(Opcode::I2D),
      "f2i" => InstKind::Normal(Opcode::F2I),
      "f2d" => InstKind::Normal(Opcode::F2D),
      "d2i" => InstKind::Normal(Opcode::D2I),
      "d2f" => InstKind::Normal(Opcode::D2F),
      "itf" => InstKind::Normal(Opcode::ITF),
      "itd" => InstKind::Normal(Opcode::ITD),
      "itp" => InstKind::Normal(Opcode::ITP),
      _ => return_error!(span, "unknown instruction"),
    };
    // get instruction
    enum Instruction {
      Normal(Inst),
      Cfi(CfInstConstructor, u64),
    }
    let inst = match kind {
      InstKind::Normal(opc) => {
        let opr = match (opc.operand_type(), inst.opr) {
          (Some(OperandType::Signed), Some(InstOperand::Imm(i))) => {
            Some(Operand::Signed(i.unwrap::<u64, _>() as i64))
          }
          (Some(OperandType::Unsigned), Some(InstOperand::Imm(i))) => {
            Some(Operand::Unsigned(i.unwrap::<u64, _>()))
          }
          (None, None) => None,
          _ => return_error!(span, "expected no operand"),
        };
        Instruction::Normal(Inst::new(opc, opr))
      }
      InstKind::Const(c) => match inst.opr {
        Some(InstOperand::LabelRef(l)) => Instruction::Normal(c(self.gen_const_label_ref(l)?)),
        _ => return_error!(span, "expected label reference"),
      },
      InstKind::Cfi(cfi) => match inst.opr {
        Some(InstOperand::LabelRef(l)) => Instruction::Cfi(cfi, self.gen_inst_label_ref(l)?),
        _ => return_error!(span, "expected label reference"),
      },
    };
    // insert instruction to section
    match self.cur_sec {
      Section::Insts => match inst {
        Instruction::Normal(inst) => self.builder.inst(inst),
        Instruction::Cfi(cfi, l) => self.builder.cfi(cfi, l),
      },
      _ => return_error!(span, "instruction can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given label definition.
  fn gen_label_def(&mut self, label_def: LabelDef) -> Result<()> {
    let span = label_def.span();
    // insert to section
    match self.cur_sec {
      Section::Consts => match label_def.kind {
        LabelDefKind::Named(l) => {
          if let Some(name) = self.last_const_label.replace(l.unwrap()) {
            return_error!(span, "overriding existing label {name}")
          }
        }
        LabelDefKind::Temp(_) => return_error!(span, "constant label can not be temporary"),
      },
      Section::Insts => match label_def.kind {
        LabelDefKind::Named(l) => {
          let label: String = l.unwrap();
          // try to find the label
          if let Some(info) = self.labels.get_mut(&label) {
            match &mut info.kind {
              LabelKind::Inst(id, inserted) if !*inserted => {
                // insert to builder
                self.builder.insert_label(*id);
                *inserted = true;
              }
              _ => return_error!(span, "duplicate label definition"),
            }
          } else {
            // create and insert label
            let id = self.builder.label();
            self.builder.insert_label(id);
            self.labels.insert(
              label,
              LabelInfo {
                kind: LabelKind::Inst(id, true),
                span: span.clone(),
              },
            );
          }
        }
        LabelDefKind::Temp(t) => todo!(),
      },
      _ => return_error!(span, "label definition can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given constant label reference.
  fn gen_const_label_ref(&mut self, label_ref: LabelRef) -> Result<u64> {
    let span = label_ref.span();
    match label_ref {
      LabelRef::Named(l) => match self.labels.get(l.unwrap_ref::<&String, _>()) {
        Some(LabelInfo { kind, span: s }) => match kind {
          LabelKind::Const(Some(index)) => Ok(*index),
          LabelKind::Const(None) => return_error!(s, "label references an invalid constant"),
          _ => return_error!(span, "expected a constant label"),
        },
        None => todo!("insert to pending labels"),
      },
      LabelRef::Temp(_) => return_error!(span, "constant label can not be temporary"),
    }
  }

  /// Generates on the given instruction label reference.
  fn gen_inst_label_ref(&mut self, label_ref: LabelRef) -> Result<u64> {
    todo!()
  }

  /// Generates on the given raw value.
  fn gen_raw_value(raw_value: RawValue) -> Vec<u8> {
    match raw_value {
      RawValue::Str(s) => s.unwrap::<String, _>().bytes().collect(),
      RawValue::Byte(b) => vec![b.unwrap::<u64, _>() as u8],
    }
  }

  /// Inserts the given constant to the constant section.
  fn insert_to_const<C>(&mut self, c: C)
  where
    C: Into<Const>,
  {
    let id = self.builder.constant(c);
    if let Some(last_const_label) = self.last_const_label.take() {
      match &mut self.labels.get_mut(&last_const_label).unwrap().kind {
        LabelKind::Const(Some(c)) => *c = id,
        _ => unreachable!(),
      }
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
  kind: LabelKind,
  span: Span,
}

/// Kind of label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabelKind {
  /// Constant label, with an optional index.
  /// If index is [`None`], the label is undefined.
  Const(Option<u64>),
  /// Instruction label, with label id and a flag that indicates
  /// whether the label has been inserted.
  Inst(u64, bool),
}
