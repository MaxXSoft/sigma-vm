use crate::front::{Section, SectionDecl, Statement};
use laps::span::Result;
use sigma_vm::bytecode::builder::Builder;

/// Bytecode assembler.
pub struct Assembler {
  builder: Builder,
  cur_sec: Section,
}

impl Assembler {
  /// Creates a new assembler.
  pub fn new() -> Self {
    Self {
      builder: Builder::new(),
      cur_sec: Section::Consts,
    }
  }

  /// Generates on the given statement.
  pub fn generate(&mut self, stmt: Statement) -> Result<()> {
    match stmt {
      Statement::SectionDecl(sec) => Ok(self.gen_section(sec)),
      _ => todo!(),
    }
  }

  /// Generates on the given section declaration.
  fn gen_section(&mut self, sec: SectionDecl) {
    self.cur_sec = sec.sec.unwrap();
  }
}
