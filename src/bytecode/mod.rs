pub mod consts;
pub mod insts;
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

#[cfg(test)]
mod test {
  use crate::bytecode::consts::{Const, ManagedPtr, Object, Raw, Str};
  use crate::bytecode::insts::Inst;
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
        len: 3,
        bytes: [b'a', b'b', b'c'],
      }),
      Const::from(Object {
        size: 256,
        align: 8,
        managed_ptr: ManagedPtr {
          len: 4,
          offsets: [1, 3, 5, 7],
        },
      }),
      Const::from(Raw {
        len: 5,
        bytes: [b'H', b'e', b'l', b'l', b'o'],
      }),
    ]
    .into_boxed_slice()
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
    let consts = some_consts();
    let insts = some_insts();
    let mut w = Writer::new(Cursor::new(Vec::<u8>::new()), &consts, &insts);
    w.write().unwrap();
    let data = w.into_inner().into_inner();
    let mut r = Reader::new(data.as_slice());
    r.read().unwrap();
    let (c2, i2) = r.into_consts_insts();
    assert!(consts.iter().zip(c2.iter()).all(|(l, r)| l
      .data()
      .iter()
      .zip(r.data())
      .all(|(l, r)| l == r)));
    assert_eq!(insts, i2);
  }
}
