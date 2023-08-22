use crate::front::*;
use laps::return_error;
use laps::span::{Result, Span, Spanned};
use sigma_vm::bytecode::builder::Builder;
use sigma_vm::bytecode::consts::Const;
use sigma_vm::bytecode::export::CallSite;
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
      _ => todo!(),
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
      Section::Custom => {
        let c = match int_const.kind {
          IntConstKind::I8(_) => Const::from(value as i8),
          IntConstKind::U8(_) => Const::from(value as u8),
          IntConstKind::I16(_) => Const::from(value as i16),
          IntConstKind::U16(_) => Const::from(value as u16),
          IntConstKind::I32(_) => Const::from(value as i32),
          IntConstKind::U32(_) => Const::from(value as u32),
          IntConstKind::I64(_) => Const::from(value as i64),
          IntConstKind::U64(_) => Const::from(value as u64),
        };
        todo!()
      }
      _ => return_error!(span, "integer constant can not appear here"),
    }
    Ok(())
  }

  /// Generates on the given label reference.
  fn gen_label_ref(&mut self, label_ref: LabelRef) -> u64 {
    todo!()
  }
}

/// Label information.
struct LabelInfo {
  id: u64,
  span: Span,
}
