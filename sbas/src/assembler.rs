use crate::front::*;
use laps::return_error;
use laps::span::{Result, Span, Spanned};
use sigma_vm::bytecode::builder::Builder;
use sigma_vm::bytecode::consts::{Const, ObjectRef};
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
    todo!()
  }

  /// Generates on the given label definition.
  fn gen_label_def(&mut self, label_def: LabelDef) -> Result<()> {
    todo!()
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
