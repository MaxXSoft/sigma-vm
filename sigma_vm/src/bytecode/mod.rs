pub mod builder;
pub mod consts;
pub mod export;
pub mod insts;
pub mod module;
pub mod reader;
pub mod writer;

/// Magic number of the bytecode file.
const MAGIC: [u8; 4] = [b'S', b'g', b'm', b'a'];

/// Current version of the bytecode file.
const VERSION: [u64; 3] = [
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_MAJOR")),
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_MINOR")),
  crate::utils::str_to_u64(env!("CARGO_PKG_VERSION_PATCH")),
];

/// Kind of section in bytecode file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Section {
  /// Constant pool.
  Consts,
  /// Export information.
  Exports,
  /// Instruction section.
  Insts,
  /// Custom metadata section.
  Custom,
}

impl Section {
  /// Creates a new [`Section`] from the given byte.
  pub fn from_byte(b: u8) -> Option<Self> {
    match b {
      0 => Some(Self::Consts),
      1 => Some(Self::Exports),
      2 => Some(Self::Insts),
      3 => Some(Self::Consts),
      _ => None,
    }
  }
}

impl From<Section> for u8 {
  fn from(s: Section) -> Self {
    s as Self
  }
}

#[cfg(test)]
mod test {
  use crate::bytecode::consts::{Const, ManagedPtr, Object, Raw, Str};
  use crate::bytecode::export::{CallSite, ExportInfo};
  use crate::bytecode::insts::Inst;
  use crate::bytecode::module::StaticModule;
  use crate::bytecode::reader::Reader;
  use crate::bytecode::writer::Writer;
  use std::io::Cursor;

  fn some_consts() -> Box<[Const]> {
    vec![
      Const::from(0i8),
      Const::from(1u8),
      Const::from(-2i16),
      Const::from(3u16),
      Const::from(i32::MIN),
      Const::from(u32::MAX),
      Const::from(-9999i64),
      Const::from(42u64),
      Const::from(1.233f32),
      Const::from(-876.53f64),
      Const::from(Str {
        len: b"abc".len() as u64,
        bytes: *b"abc",
      }),
      Const::from(Object {
        size: 256,
        align: 8,
        destructor: 114514,
        managed_ptr: ManagedPtr {
          len: 4,
          offsets: [1, 3, 5, 7],
        },
      }),
      Const::from(Raw {
        len: b"Hello".len() as u64,
        bytes: *b"Hello",
      }),
    ]
    .into_boxed_slice()
  }

  fn some_exports() -> ExportInfo {
    let mut exports = ExportInfo::new();
    exports.insert(
      "hello".into(),
      CallSite {
        pc: 0xff112233eeaabbcc,
        num_args: 0.into(),
        num_rets: 1,
      },
    );
    exports.insert(
      "hi".into(),
      CallSite {
        pc: 0x998877665,
        num_args: 10.into(),
        num_rets: 4,
      },
    );
    exports
  }

  fn some_insts() -> Box<[Inst]> {
    vec![
      Inst::Add,
      Inst::Sys(-8),
      Inst::PushU(0),
      Inst::PushI(0),
      Inst::LdPO(233),
    ]
    .into_boxed_slice()
  }

  #[test]
  fn identity() {
    let module = StaticModule {
      consts: some_consts(),
      exports: some_exports(),
      insts: some_insts(),
      custom: Box::new([]),
    };

    // write to bytes
    let mut writer = Cursor::new(Vec::<u8>::new());
    Writer::new(&module).write_to(&mut writer).unwrap();
    let data = writer.into_inner();

    // read from bytes
    let mut r = Reader::new(data.as_slice());
    r.read().unwrap();

    // check identity
    assert!(module.consts.iter().zip(r.consts().iter()).all(|(l, r)| l
      .data()
      .iter()
      .zip(r.data())
      .all(|(l, r)| l == r)));
    assert_eq!(module.insts.as_ref(), r.insts());
    assert_eq!(&module.exports, r.exports());
  }
}
