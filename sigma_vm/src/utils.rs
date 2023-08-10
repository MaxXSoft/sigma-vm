use std::alloc::{self, Layout, LayoutError};
use std::ptr::{self, Pointee};

/// Implements [`TryFrom<integer>`] for the given enumerate.
macro_rules! impl_try_from_int {
  (impl TryFrom<$ty:ty> for $id:ident {
    $($item:ident $(= $e:expr)?),* $(,)?
  }) => {
    impl std::convert::TryFrom<$ty> for $id {
      type Error = ();

      fn try_from(_i: $ty) -> std::result::Result<Self, Self::Error> {
        use std::result::Result::*;
        let mut _k = 0;
        impl_try_from_int!(@item _i, _k $(,$item $(= $e)?)*)
      }
    }
  };
  (@item $i:ident, $k:ident,
    $item:ident $(= $e:expr)?
    $(,$items:ident $(= $es:expr)?)*
  ) => {{
    $($k = $e;)?
    if $i == $k { return Ok(Self::$item) }
    $k += 1;
    impl_try_from_int!(@item $i, $k $(,$items $(= $es)?)*)
  }};
  (@item $i:ident, $k:ident) => {{ Err(()) }};
}
pub(crate) use impl_try_from_int;

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
