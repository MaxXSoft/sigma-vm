use crate::front::{Export, Section, SectionDecl, Statement};
use laps::span::{Result, Span};
use sigma_vm::bytecode::builder::Builder;
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
    if self.cur_sec == Section::Exports {
      // self.builder.export(export.name.unwrap(), label, num_args, num_rets)
    }
    todo!()
  }

  // /// Generates on the given label.
  // fn gen_label(&mut self)
}

/// Label information.
struct LabelInfo {
  id: u64,
  span: Span,
}
