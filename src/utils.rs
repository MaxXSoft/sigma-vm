use std::alloc::{self, Layout, LayoutError};
use std::ptr::{self, Pointee};

/// Creates an uninitialized `T` on heap, applies the given metadata.
///
/// # Safety
///
/// The created data must be set a valid value first.
pub unsafe fn alloc_uninit<T, M>(
  size: usize,
  align: usize,
  metadata: M,
) -> Result<Box<T>, LayoutError>
where
  T: ?Sized + Pointee<Metadata = M>,
{
  let layout = Layout::from_size_align(size, align)?;
  let ptr = alloc::alloc(layout);
  if ptr.is_null() {
    alloc::handle_alloc_error(layout);
  }
  Ok(Box::from_raw(ptr::from_raw_parts_mut(
    ptr as *mut _,
    metadata,
  )))
}

/// Converts a string to [`u64`] at compile-time.
pub const fn str_to_u64(s: &str) -> u64 {
  let mut bytes = s.as_bytes();
  let mut result = 0;
  while let [byte, rest @ ..] = bytes {
    assert!(b'0' <= *byte && *byte <= b'9', "invalid digit");
    result = result * 10 + (*byte - b'0') as u64;
    bytes = rest;
  }
  result
}
