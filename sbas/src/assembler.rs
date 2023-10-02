use crate::front::*;
use laps::span::{Result, Span, Spanned};
use laps::{log_raw_error, return_error};
use sigma_vm::bytecode::builder::{Builder, CfInstConstructor, PcInstConstructor};
use sigma_vm::bytecode::consts::{Const, ObjectRef};
use sigma_vm::bytecode::export::CallSite;
use sigma_vm::bytecode::insts::{Inst, Opcode, Operand, OperandType};
use sigma_vm::bytecode::writer::{WriteData, Writer};
use std::collections::HashMap;
use std::io::Write;

/// Bytecode assembler.
pub struct Assembler {
  builder: Builder,
  cur_sec: Section,
  labels: HashMap<String, LabelInfo>,
  temp_labels: HashMap<u64, TempLabelInfo>,
  last_const_label: Option<String>,
  pending_const_labels: HashMap<String, PendingLabelInfo>,
}

/// Helper macro for unwrapping a label.
macro_rules! unwrap_label {
  ($l:ident) => {
    match $l.unwrap::<OpcOrLabel, _>() {
      OpcOrLabel::Label(name) => name,
      _ => unreachable!(),
    }
  };
  (&$l:ident) => {
    match $l.unwrap_ref::<&OpcOrLabel, _>() {
      OpcOrLabel::Label(name) => name,
      _ => unreachable!(),
    }
  };
}

impl Assembler {
  /// Creates a new assembler.
  pub fn new() -> Self {
    Self {
      builder: Builder::new(),
      cur_sec: Section::Consts,
      labels: HashMap::new(),
      temp_labels: HashMap::new(),
      last_const_label: None,
      pending_const_labels: HashMap::new(),
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

  /// Writes the generated bytecode to the given writer.
  pub fn write<W>(mut self, span: Span, w: &mut W) -> Result<()>
  where
    W: Write,
  {
    // check for pending constant labels
    for (name, pinfo) in self.pending_const_labels {
      if let Some(info) = self.labels.get(&name) {
        match info.kind {
          LabelKind::Const(Some(index)) => {
            for (pc, ci) in pinfo.pc_consts {
              self.builder.replace_inst(pc, ci(index));
            }
          }
          LabelKind::Const(None) => {
            return_error!(info.span, "label references an invalid constant");
          }
          _ => return_error!(info.span, "label does not corresponding to a constant"),
        }
      } else {
        return_error!(pinfo.span, "label `{name}` is undefined");
      }
    }
    // check if there are undefined labels
    for (name, info) in self.labels {
      if matches!(info.kind, LabelKind::Inst(_, false)) {
        return_error!(info.span, "label `{name}` is undefined");
      }
    }
    // check if there are undefined temporary labels
    for (id, info) in self.temp_labels {
      if let Some((_, span)) = info.next {
        return_error!(span, "temporary label `{id}` is undefined");
      }
    }
    // generate static module
    let module = match self.builder.build() {
      Ok(module) => module,
      Err(e) => return Err(log_raw_error!(span, "{e}")),
    };
    // write module
    match Writer::new(&module).write_to(w) {
      Ok(()) => Ok(()),
      Err(e) => return Err(log_raw_error!(span, "failed to write bytecode file: {e}")),
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
    let end_label = self.gen_inst_label_ref(export.end_label)?;
    let num_args = match export.num_args {
      NumArgs::Variadic(_) => None,
      NumArgs::Num(n) => Some(n.unwrap()),
    };
    let num_rets = export.num_rets.unwrap();
    // insert to section
    match self.cur_sec {
      Section::Exports => {
        let inserted = self
          .builder
          .export(name, label, end_label, num_args, num_rets);
        match inserted {
          Ok(false) => return_error!(span, "duplicate export"),
          Err(e) => return_error!(span, "{e}"),
          _ => {}
        }
      }
      Section::Custom => {
        // get PC of label and end label
        let pc_end = self
          .builder
          .label_pc(label)
          .zip(self.builder.label_pc(end_label));
        let (pc, end) = match pc_end {
          Some(pc_end) => pc_end,
          None => return_error!(span, "export information reference an invalid label"),
        };
        if end < pc {
          return_error!(span, "end label can not come before the function label");
        }
        // write call site
        let mut bytes: Vec<u8> = vec![];
        let call_site = CallSite {
          pc,
          size: end - pc,
          num_args: num_args.into(),
          num_rets,
        };
        call_site.write(&mut bytes).unwrap();
        // write name
        name.write(&mut bytes).unwrap();
        // insert to custom section
        self.builder.custom(bytes);
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
    let destructor = object
      .destructor
      .map(|d| self.gen_inst_label_ref(d.destructor))
      .transpose()?;
    let offsets: Vec<_> = object.offsets.into_iter().map(|o| o.unwrap()).collect();
    let mut object = ObjectRef {
      size: object.size.unwrap(),
      align: object.align.unwrap(),
      destructor: destructor.unwrap_or(0),
      offsets: &offsets,
    };
    // insert to section
    match self.cur_sec {
      Section::Consts => {
        if let Some(label) = destructor {
          let index = self.builder.object(object, label);
          self.handle_const_label(index);
        } else {
          self.insert_to_const(object);
        }
      }
      Section::Custom => {
        // updated destructor
        if let Some(label) = destructor {
          match self.builder.label_pc(label) {
            Some(pc) => object.destructor = pc,
            None => return_error!(span, "destructor references an invalid label"),
          }
        }
        // insert to custom section
        self.insert_to_custom(object);
      }
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
      Const(ConstInst),
      Cfi(CfInstConstructor),
      PcImmOrNormal(PcInstConstructor),
    }
    let opcode: InstOpcode = match inst.opcode.unwrap::<OpcOrLabel, _>() {
      OpcOrLabel::Opcode(opcode) => opcode,
      _ => unreachable!(),
    };
    let kind = match opcode {
      InstOpcode::Nop => InstKind::Normal(Opcode::Nop),
      InstOpcode::PushI => InstKind::Normal(Opcode::PushI),
      InstOpcode::PushU => InstKind::PcImmOrNormal(Inst::PushU),
      InstOpcode::PushPc => InstKind::Normal(Opcode::PushPc),
      InstOpcode::Pop => InstKind::Normal(Opcode::Pop),
      InstOpcode::Dup => InstKind::Normal(Opcode::Dup),
      InstOpcode::DupS1 => InstKind::Normal(Opcode::DupS1),
      InstOpcode::Swap => InstKind::Normal(Opcode::Swap),
      InstOpcode::LdB => InstKind::Normal(Opcode::LdB),
      InstOpcode::LdBU => InstKind::Normal(Opcode::LdBU),
      InstOpcode::LdH => InstKind::Normal(Opcode::LdH),
      InstOpcode::LdHU => InstKind::Normal(Opcode::LdHU),
      InstOpcode::LdW => InstKind::Normal(Opcode::LdW),
      InstOpcode::LdWU => InstKind::Normal(Opcode::LdWU),
      InstOpcode::LdD => InstKind::Normal(Opcode::LdD),
      InstOpcode::LdP => InstKind::Normal(Opcode::LdP),
      InstOpcode::LdBO => InstKind::Normal(Opcode::LdBO),
      InstOpcode::LdBUO => InstKind::Normal(Opcode::LdBUO),
      InstOpcode::LdHO => InstKind::Normal(Opcode::LdHO),
      InstOpcode::LdHUO => InstKind::Normal(Opcode::LdHUO),
      InstOpcode::LdWO => InstKind::Normal(Opcode::LdWO),
      InstOpcode::LdWUO => InstKind::Normal(Opcode::LdWUO),
      InstOpcode::LdDO => InstKind::Normal(Opcode::LdDO),
      InstOpcode::LdPO => InstKind::Normal(Opcode::LdPO),
      InstOpcode::LdV => InstKind::Normal(Opcode::LdV),
      InstOpcode::LdG => InstKind::Normal(Opcode::LdG),
      InstOpcode::LdC => InstKind::Const(Inst::LdC),
      InstOpcode::LaC => InstKind::Const(Inst::LaC),
      InstOpcode::StB => InstKind::Normal(Opcode::StB),
      InstOpcode::StH => InstKind::Normal(Opcode::StH),
      InstOpcode::StW => InstKind::Normal(Opcode::StW),
      InstOpcode::StD => InstKind::Normal(Opcode::StD),
      InstOpcode::StBO => InstKind::Normal(Opcode::StBO),
      InstOpcode::StHO => InstKind::Normal(Opcode::StHO),
      InstOpcode::StWO => InstKind::Normal(Opcode::StWO),
      InstOpcode::StDO => InstKind::Normal(Opcode::StDO),
      InstOpcode::StV => InstKind::Normal(Opcode::StV),
      InstOpcode::StG => InstKind::Normal(Opcode::StG),
      InstOpcode::StA => InstKind::Normal(Opcode::StA),
      InstOpcode::New => InstKind::Normal(Opcode::New),
      InstOpcode::NewO => InstKind::Normal(Opcode::NewO),
      InstOpcode::NewOC => InstKind::Const(Inst::NewOC),
      InstOpcode::NewA => InstKind::Normal(Opcode::NewA),
      InstOpcode::NewAC => InstKind::Const(Inst::NewAC),
      InstOpcode::Load => InstKind::Normal(Opcode::Load),
      InstOpcode::LoadC => InstKind::Const(Inst::LoadC),
      InstOpcode::LoadM => InstKind::Normal(Opcode::LoadM),
      InstOpcode::Bz => InstKind::Cfi(Inst::Bz),
      InstOpcode::BzNP => InstKind::Cfi(Inst::BzNP),
      InstOpcode::Bnz => InstKind::Cfi(Inst::Bnz),
      InstOpcode::Loop => InstKind::Cfi(Inst::Loop),
      InstOpcode::Jmp => InstKind::Cfi(Inst::Jmp),
      InstOpcode::JmpS => InstKind::Normal(Opcode::JmpS),
      InstOpcode::Call => InstKind::Cfi(Inst::Call),
      InstOpcode::CallS => InstKind::Normal(Opcode::CallS),
      InstOpcode::CallExt => InstKind::Normal(Opcode::CallExt),
      InstOpcode::CallExtS => InstKind::Normal(Opcode::CallExtS),
      InstOpcode::CallExtC => InstKind::Const(Inst::CallExtC),
      InstOpcode::Ret => InstKind::Normal(Opcode::Ret),
      InstOpcode::Sys => InstKind::Normal(Opcode::Sys),
      InstOpcode::Break => InstKind::Normal(Opcode::Break),
      InstOpcode::Not => InstKind::Normal(Opcode::Not),
      InstOpcode::LNot => InstKind::Normal(Opcode::LNot),
      InstOpcode::And => InstKind::Normal(Opcode::And),
      InstOpcode::Or => InstKind::Normal(Opcode::Or),
      InstOpcode::Xor => InstKind::Normal(Opcode::Xor),
      InstOpcode::Shl => InstKind::Normal(Opcode::Shl),
      InstOpcode::Shr => InstKind::Normal(Opcode::Shr),
      InstOpcode::Sar => InstKind::Normal(Opcode::Sar),
      InstOpcode::Sext => InstKind::Normal(Opcode::Sext),
      InstOpcode::Zext => InstKind::Normal(Opcode::Zext),
      InstOpcode::Eq => InstKind::Normal(Opcode::Eq),
      InstOpcode::Ne => InstKind::Normal(Opcode::Ne),
      InstOpcode::Lt => InstKind::Normal(Opcode::Lt),
      InstOpcode::Le => InstKind::Normal(Opcode::Le),
      InstOpcode::Gt => InstKind::Normal(Opcode::Gt),
      InstOpcode::Ge => InstKind::Normal(Opcode::Ge),
      InstOpcode::LtU => InstKind::Normal(Opcode::LtU),
      InstOpcode::LeU => InstKind::Normal(Opcode::LeU),
      InstOpcode::GtU => InstKind::Normal(Opcode::GtU),
      InstOpcode::GeU => InstKind::Normal(Opcode::GeU),
      InstOpcode::Neg => InstKind::Normal(Opcode::Neg),
      InstOpcode::Add => InstKind::Normal(Opcode::Add),
      InstOpcode::Sub => InstKind::Normal(Opcode::Sub),
      InstOpcode::Mul => InstKind::Normal(Opcode::Mul),
      InstOpcode::Div => InstKind::Normal(Opcode::Div),
      InstOpcode::DivU => InstKind::Normal(Opcode::DivU),
      InstOpcode::Mod => InstKind::Normal(Opcode::Mod),
      InstOpcode::ModU => InstKind::Normal(Opcode::ModU),
      InstOpcode::LtF => InstKind::Normal(Opcode::LtF),
      InstOpcode::LeF => InstKind::Normal(Opcode::LeF),
      InstOpcode::GtF => InstKind::Normal(Opcode::GtF),
      InstOpcode::GeF => InstKind::Normal(Opcode::GeF),
      InstOpcode::NegF => InstKind::Normal(Opcode::NegF),
      InstOpcode::AddF => InstKind::Normal(Opcode::AddF),
      InstOpcode::SubF => InstKind::Normal(Opcode::SubF),
      InstOpcode::MulF => InstKind::Normal(Opcode::MulF),
      InstOpcode::DivF => InstKind::Normal(Opcode::DivF),
      InstOpcode::ModF => InstKind::Normal(Opcode::ModF),
      InstOpcode::LtD => InstKind::Normal(Opcode::LtD),
      InstOpcode::LeD => InstKind::Normal(Opcode::LeD),
      InstOpcode::GtD => InstKind::Normal(Opcode::GtD),
      InstOpcode::GeD => InstKind::Normal(Opcode::GeD),
      InstOpcode::NegD => InstKind::Normal(Opcode::NegD),
      InstOpcode::AddD => InstKind::Normal(Opcode::AddD),
      InstOpcode::SubD => InstKind::Normal(Opcode::SubD),
      InstOpcode::MulD => InstKind::Normal(Opcode::MulD),
      InstOpcode::DivD => InstKind::Normal(Opcode::DivD),
      InstOpcode::ModD => InstKind::Normal(Opcode::ModD),
      InstOpcode::I2F => InstKind::Normal(Opcode::I2F),
      InstOpcode::I2D => InstKind::Normal(Opcode::I2D),
      InstOpcode::F2I => InstKind::Normal(Opcode::F2I),
      InstOpcode::F2D => InstKind::Normal(Opcode::F2D),
      InstOpcode::D2I => InstKind::Normal(Opcode::D2I),
      InstOpcode::D2F => InstKind::Normal(Opcode::D2F),
      InstOpcode::ITF => InstKind::Normal(Opcode::ITF),
      InstOpcode::ITD => InstKind::Normal(Opcode::ITD),
      InstOpcode::ITP => InstKind::Normal(Opcode::ITP),
    };
    // get instruction
    enum Instruction {
      Normal(Inst),
      Cfi(CfInstConstructor, u64),
      PcImm(PcInstConstructor, u64),
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
        Some(InstOperand::LabelRef(l)) => Instruction::Normal(c(self.gen_const_label_ref(c, l)?)),
        _ => return_error!(span, "expected label reference"),
      },
      InstKind::Cfi(cfi) => match inst.opr {
        Some(InstOperand::LabelRef(l)) => Instruction::Cfi(cfi, self.gen_inst_label_ref(l)?),
        _ => return_error!(span, "expected label reference"),
      },
      InstKind::PcImmOrNormal(pc_imm) => match inst.opr {
        Some(InstOperand::Imm(i)) => Instruction::Normal(pc_imm(i.unwrap::<u64, _>())),
        Some(InstOperand::LabelRef(l)) => Instruction::PcImm(pc_imm, self.gen_inst_label_ref(l)?),
        _ => return_error!(span, "expected immediate or label reference"),
      },
    };
    // insert instruction to section
    match self.cur_sec {
      Section::Insts => match inst {
        Instruction::Normal(inst) => self.builder.inst(inst),
        Instruction::Cfi(cfi, l) => self.builder.cfi(cfi, l),
        Instruction::PcImm(pc_imm, l) => self.builder.pc_imm(pc_imm, l),
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
          let label = unwrap_label!(l);
          // check the last label
          if let Some(name) = self.last_const_label.replace(label.clone()) {
            return_error!(span, "overriding existing label {name}");
          }
          // insert label information
          let info = LabelInfo {
            kind: LabelKind::Const(None),
            span: span.clone(),
          };
          if self.labels.insert(label, info).is_some() {
            return_error!(span, "duplicated label definition");
          }
        }
        LabelDefKind::Temp(_) => return_error!(span, "constant label can not be temporary"),
      },
      Section::Insts => match label_def.kind {
        LabelDefKind::Named(l) => {
          let label = unwrap_label!(l);
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
        LabelDefKind::Temp(t) => {
          // check label information
          let info = self.temp_labels.entry(t.unwrap()).or_default();
          // get label id
          let id = if let Some((id, _)) = info.next.take() {
            self.builder.insert_label(id);
            id
          } else {
            self.builder.label()
          };
          // insert label and update information
          self.builder.insert_label(id);
          info.prev = Some(id);
        }
      },
      _ => return_error!(span, "label definition can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given constant label reference.
  fn gen_const_label_ref(&mut self, ci: ConstInst, label_ref: LabelRef) -> Result<u64> {
    let span = label_ref.span();
    match label_ref {
      LabelRef::Named(l) => match self.labels.get(unwrap_label!(&l)) {
        Some(LabelInfo { kind, span: s }) => match kind {
          LabelKind::Const(Some(index)) => Ok(*index),
          LabelKind::Const(None) => return_error!(s, "label references an invalid constant"),
          _ => return_error!(span, "expected a constant label"),
        },
        None => {
          assert_eq!(self.cur_sec, Section::Insts);
          // insert to pending labels
          let info = self
            .pending_const_labels
            .entry(unwrap_label!(l))
            .or_insert_with(|| PendingLabelInfo {
              pc_consts: vec![],
              span,
            });
          // update informatio
          info.pc_consts.push((self.builder.pc(), ci));
          Ok(0)
        }
      },
      LabelRef::Temp(_) => return_error!(span, "constant label can not be temporary"),
    }
  }

  /// Generates on the given instruction label reference.
  fn gen_inst_label_ref(&mut self, label_ref: LabelRef) -> Result<u64> {
    let span = label_ref.span();
    match label_ref {
      LabelRef::Named(l) => match self.labels.get(unwrap_label!(&l)) {
        Some(LabelInfo { kind, .. }) => match kind {
          LabelKind::Inst(id, _) => Ok(*id),
          _ => return_error!(span, "expected an instruction label"),
        },
        None => {
          let id = self.builder.label();
          self.labels.insert(
            unwrap_label!(l),
            LabelInfo {
              kind: LabelKind::Inst(id, false),
              span,
            },
          );
          Ok(id)
        }
      },
      LabelRef::Temp(t) => {
        let TempLabelRef { label, front } = t.unwrap();
        let info = self.temp_labels.entry(label).or_default();
        if front {
          match info.next {
            Some((id, _)) => Ok(id),
            None => {
              let id = self.builder.label();
              info.next = Some((id, span));
              Ok(id)
            }
          }
        } else {
          match info.prev {
            Some(id) => Ok(id),
            None => return_error!(span, "referencing an invalid temporary label"),
          }
        }
      }
    }
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
    self.handle_const_label(id);
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

  /// Handles label of the constant of the given index.
  fn handle_const_label(&mut self, index: u64) {
    if let Some(last_const_label) = self.last_const_label.take() {
      match &mut self.labels.get_mut(&last_const_label).unwrap().kind {
        LabelKind::Const(c) if c.is_none() => *c = Some(index),
        _ => unreachable!(),
      }
    }
  }
}

/// Label information.
struct LabelInfo {
  kind: LabelKind,
  span: Span,
}

/// Kind of label.
enum LabelKind {
  /// Constant label, with an optional index.
  /// If index is [`None`], the label is undefined.
  Const(Option<u64>),
  /// Instruction label, with label id and a flag that indicates
  /// whether the label has been inserted.
  Inst(u64, bool),
}

/// Temporary label information.
#[derive(Default)]
struct TempLabelInfo {
  prev: Option<u64>,
  next: Option<(u64, Span)>,
}

/// Constant instruction constructor.
type ConstInst = fn(u64) -> Inst;

/// Pending constant label information.
struct PendingLabelInfo {
  pc_consts: Vec<(u64, ConstInst)>,
  span: Span,
}
