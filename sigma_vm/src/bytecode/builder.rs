use crate::bytecode::consts::{Const, ConstKind};
use crate::bytecode::export::{CallSite, ExportInfo};
use crate::bytecode::insts::Inst;
use crate::bytecode::module::StaticModule;
use std::collections::HashMap;
use std::fmt;

/// Bytecode builder for compiler front ends emitting bytecodes.
pub struct Builder {
  /// Constants and their indices.
  consts: HashMap<Const, u64>,
  exports: ExportInfo,
  insts: Vec<Inst>,
  /// Mapping between label handle and label PC.
  labels: HashMap<u64, u64>,
  /// Mapping between label handle and label kinds.
  pending_labels: HashMap<u64, Vec<LabelKind>>,
  next_label: u64,
  custom: Vec<u8>,
}

impl Builder {
  /// Creates a new bytecode builder.
  pub fn new() -> Self {
    Self {
      consts: HashMap::new(),
      exports: ExportInfo::new(),
      insts: vec![],
      labels: HashMap::new(),
      pending_labels: HashMap::new(),
      next_label: 0,
      custom: vec![],
    }
  }

  /// Inserts a new constant, returns the index of the constant.
  pub fn constant<C>(&mut self, c: C) -> u64
  where
    C: Into<Const>,
  {
    let index = self.consts.len() as u64;
    *self.consts.entry(c.into()).or_insert(index)
  }

  /// Inserts an object metadata which destructor references the given label,
  /// returns the index of the constant.
  ///
  /// # Panics
  ///
  /// Panics if the given constant is not an object metadata.
  pub fn object<C>(&mut self, c: C, label: u64) -> u64
  where
    C: Into<Const>,
  {
    let c: Const = c.into();
    assert_eq!(c.kind(), ConstKind::Object);
    let index = self.constant(c);
    self
      .pending_labels
      .entry(label)
      .or_default()
      .push(LabelKind::Object(index));
    index
  }

  /// Returns the current PC.
  pub fn pc(&self) -> u64 {
    self.insts.len() as u64
  }

  /// Declares a new label, returns the handle of the label.
  pub fn label(&mut self) -> u64 {
    let label = self.next_label;
    self.next_label += 1;
    label
  }

  /// Inserts the given label at the current PC.
  pub fn insert_label(&mut self, label: u64) {
    self.labels.insert(label, self.pc());
  }

  /// Returns the PC of the given label. Returns [`None`] if label
  /// has not been inserted yet.
  pub fn label_pc(&self, label: u64) -> Option<u64> {
    self.labels.get(&label).copied()
  }

  /// Inserts a new exported function, with the given name, label, and number
  /// of arguments and return values. The exported function is variadic if
  /// `num_args` is [`None`].
  ///
  /// Returns `true` if the insertion succeeded.
  pub fn export(&mut self, name: String, label: u64, num_args: Option<u64>, num_rets: u64) -> bool {
    if self.exports.get(&name).is_some() {
      return false;
    }
    // get label PC
    let pc = if let Some(pc) = self.labels.get(&label) {
      *pc
    } else {
      self
        .pending_labels
        .entry(label)
        .or_default()
        .push(LabelKind::Export(name.clone()));
      0
    };
    // create call site
    let call_site = CallSite {
      pc,
      num_args: num_args.into(),
      num_rets,
    };
    // add to exports
    self.exports.insert(name, call_site);
    true
  }

  /// Inserts a new instruction at the current PC.
  pub fn inst(&mut self, inst: Inst) {
    self.insts.push(inst);
  }

  /// Inserts a new control flow instruction at the current PC.
  pub fn cfi(&mut self, cfi: CfInstConstructor, label: u64) {
    let pc = self.pc();
    let inst = if let Some(l) = self.labels.get(&label) {
      cfi(*l as i64 - pc as i64)
    } else {
      self
        .pending_labels
        .entry(label)
        .or_default()
        .push(LabelKind::Cfi(pc, cfi));
      cfi(0)
    };
    self.insts.push(inst);
  }

  /// Inserts a new PC-immediate instruction at the current PC.
  pub fn pc_imm(&mut self, pc_imm: PcInstConstructor, label: u64) {
    let inst = if let Some(l) = self.labels.get(&label) {
      pc_imm(*l)
    } else {
      let pc = self.pc();
      self
        .pending_labels
        .entry(label)
        .or_default()
        .push(LabelKind::PcImm(pc, pc_imm));
      pc_imm(0)
    };
    self.insts.push(inst);
  }

  /// Inserts a new instruction for pushing a
  /// 32-bit floating point into the value stack.
  pub fn push_f32(&mut self, value: f32) {
    self.inst(Inst::PushU(
      unsafe { *(&value as *const _ as *const u32) } as u64
    ));
    self.inst(Inst::ITF);
  }

  /// Inserts a new instruction for pushing a
  /// 64-bit floating point into the value stack.
  pub fn push_f64(&mut self, value: f64) {
    self.inst(Inst::PushU(unsafe { *(&value as *const _ as *const u64) }));
    self.inst(Inst::ITD);
  }

  /// Replaces the instruction at the given PC.
  /// Returns the instruction before replacement.
  ///
  /// # Panics
  ///
  /// Panics if the given PC is invalid.
  pub fn replace_inst(&mut self, pc: u64, inst: Inst) -> Inst {
    std::mem::replace(&mut self.insts[pc as usize], inst)
  }

  /// Adds the given bytes to custom metadata.
  pub fn custom<I>(&mut self, bytes: I)
  where
    I: IntoIterator<Item = u8>,
  {
    self.custom.extend(bytes)
  }

  /// Consumes the current builder and builds a static module.
  pub fn build(mut self) -> Result<StaticModule, Error> {
    // create constant pool
    let mut consts: Vec<_> = self.consts.into_iter().map(|(c, i)| (i, c)).collect();
    consts.sort_unstable_by_key(|(i, _)| *i);
    // handle pending labels
    for (label, kinds) in self.pending_labels {
      let pc = *self.labels.get(&label).ok_or(Error::LabelNotFound(label))?;
      for kind in kinds {
        match kind {
          LabelKind::Object(index) => {
            let (i, c) = &mut consts[index as usize];
            assert_eq!(*i, index);
            unsafe { c.object_mut() }.unwrap().destructor = pc;
          }
          LabelKind::Export(name) => self.exports.get_mut(&name).unwrap().pc = pc,
          LabelKind::Cfi(i, cfi) => self.insts[i as usize] = cfi(pc as i64 - i as i64),
          LabelKind::PcImm(i, pc_imm) => self.insts[i as usize] = pc_imm(pc),
        }
      }
    }
    // create static module
    Ok(StaticModule {
      consts: consts.into_iter().map(|(_, c)| c).collect(),
      exports: self.exports,
      insts: self.insts.into_boxed_slice(),
      custom: self.custom.into_boxed_slice(),
    })
  }
}

/// Kind of a pending label.
enum LabelKind {
  /// Label corresponding to an object metadata,
  /// with the constant index.
  Object(u64),
  /// Label corresponding to an export information,
  /// with the name of the export.
  Export(String),
  /// Label corresponding to a control flow instruction,
  /// with its PC and constructor.
  Cfi(u64, CfInstConstructor),
  /// Label corresponding to a PC-immediate instruction,
  /// with its PC and constructor.
  PcImm(u64, PcInstConstructor),
}

/// Constructor of control flow instruction.
pub type CfInstConstructor = fn(i64) -> Inst;

/// Constructor of PC-immediate instruction.
pub type PcInstConstructor = fn(u64) -> Inst;

/// Errors for the bytecode builder.
#[derive(Debug)]
pub enum Error {
  /// Label not found.
  LabelNotFound(u64),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::LabelNotFound(id) => write!(f, "label {id} not found"),
    }
  }
}
