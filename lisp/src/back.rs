use crate::front::{ElemKind, Element};
use laps::{log_warning, span::Result};
use sigma_vm::bytecode::builder::Builder;
use sigma_vm::bytecode::consts::ObjectRef;
use sigma_vm::bytecode::insts::Inst;

pub struct Generator {
  builder: Builder,
  obj_value: u64,
  obj_ptr: u64,
}

impl Generator {
  /// Creates a new generator.
  pub fn new() -> Self {
    let mut builder = Builder::new();
    let obj_value = builder.constant(ObjectRef {
      size: 24,
      align: 8,
      destructor: 0,
      offsets: &[2], // kind, value, next
    });
    let obj_ptr = builder.constant(ObjectRef {
      size: 24,
      align: 8,
      destructor: 0,
      offsets: &[1, 2], // kind, pointer, next
    });
    Self {
      builder,
      obj_value,
      obj_ptr,
    }
  }

  /// Generates on the given element.
  pub fn generate(&mut self, elem: Element) -> Result<()> {
    elem.generate(self)
  }

  /// Generates a quote.
  fn quote(&mut self, elem: Element) {
    match elem.kind {
      ElemKind::Num(num) => self.num(num),
      ElemKind::Str(s) => self.str(&s),
      ElemKind::Sym(s) => self.sym(&s),
      ElemKind::Quote(e) => {
        self.list(vec![
          Element {
            kind: ElemKind::Str("quote".into()),
            span: elem.span,
          },
          *e,
        ]);
      }
      ElemKind::List(elems) => self.list(elems),
    }
  }

  /// Generates a new number value.
  fn num(&mut self, num: f64) {
    self.atom(self.obj_value, AtomKind::Num);
    self.builder.inst(Inst::Dup);
    self.builder.push_f64(num);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new string value.
  fn str(&mut self, s: &str) {
    self.atom(self.obj_ptr, AtomKind::Str);
    self.builder.inst(Inst::Dup);
    self.push_str(s);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new symbol value.
  fn sym(&mut self, s: &str) {
    self.atom(self.obj_ptr, AtomKind::Sym);
    self.builder.inst(Inst::Dup);
    self.push_str(s);
    self.builder.inst(Inst::StDO(1));
  }

  /// Generates a new string, pushes its pointer to the stack.
  fn push_str(&mut self, s: &str) {
    let s = self.builder.constant(s);
    self.builder.inst(Inst::LaC(s));
  }

  /// Generates a new list.
  fn list(&mut self, elems: Vec<Element>) {
    self.atom(self.obj_ptr, AtomKind::List);
    self.builder.inst(Inst::Dup);
    self.chain(elems.into_iter());
    self.builder.inst(Inst::StDO(1));
  }

  /// Chains the given elements into a linked list.
  fn chain<I>(&mut self, mut elems: I)
  where
    I: Iterator<Item = Element>,
  {
    if let Some(elem) = elems.next() {
      self.quote(elem);
      self.builder.inst(Inst::Dup);
      self.chain(elems);
      self.builder.inst(Inst::StDO(2));
    } else {
      self.builder.inst(Inst::PushU(0));
    }
  }

  /// Generates a new atom, leaves the 2nd field uninitialized.
  fn atom(&mut self, obj: u64, kind: AtomKind) {
    self.builder.inst(Inst::NewOC(obj));
    self.builder.inst(Inst::Dup);
    self.builder.inst(Inst::PushU(kind as u64));
    self.builder.inst(Inst::StDO(0));
    self.builder.inst(Inst::Dup);
    self.builder.inst(Inst::PushU(0));
    self.builder.inst(Inst::StDO(2));
  }
}

/// Kind of atom.
enum AtomKind {
  /// Number.
  Num,
  /// String.
  Str,
  /// Symbol.
  Sym,
  /// List.
  List,
}

/// Trait for generating statements.
trait Generate {
  /// Generates the given statement.
  fn generate(self, generator: &mut Generator) -> Result<()>;
}

impl Generate for Element {
  fn generate(self, generator: &mut Generator) -> Result<()> {
    if let ElemKind::List(es) = self.kind {
      todo!()
    } else {
      log_warning!(self.span, "ignored this element");
      Ok(())
    }
  }
}
