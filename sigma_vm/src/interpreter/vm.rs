use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::export::ExportInfo;
use crate::bytecode::insts::Inst;
use crate::interpreter::context::Context;
use crate::interpreter::gc::{GarbageCollector, Roots};
use crate::interpreter::heap::{Heap, Obj, ObjKind};
use crate::interpreter::loader::{Error, Loader, Source};
use crate::interpreter::policy::Policy;
use crate::utils::IntoU64;
use std::alloc::Layout;
use std::collections::HashMap;
use std::mem;
use std::path::Path;

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  global_heap: GlobalHeap<P>,
  loader: Loader,
  contexts: HashMap<Source, ContextInfo<P>>,
}

impl<P: Policy> VM<P> {
  /// Creates a new virtual machine.
  pub fn new(policy: P) -> Self {
    Self {
      global_heap: GlobalHeap::new(policy),
      loader: Loader::new(),
      contexts: HashMap::new(),
    }
  }

  /// Returns a reference to the loader.
  pub fn loader(&self) -> &Loader {
    &self.loader
  }

  /// Returns a mutable reference to the loader.
  pub fn loader_mut(&mut self) -> &mut Loader {
    &mut self.loader
  }

  /// Loads a module from the given path.
  pub fn load_from_path<T>(&mut self, path: T) -> Result<Source, Error>
  where
    T: AsRef<Path>,
  {
    self.loader.load_from_path(path, &mut self.global_heap.heap)
  }

  /// Loads a module from the given bytes.
  pub fn load_from_bytes(&mut self, bytes: &[u8]) -> Result<Source, Error> {
    self
      .loader
      .load_from_bytes(bytes, &mut self.global_heap.heap)
  }

  /// Loads a module from the standard input.
  pub fn load_from_stdin(&mut self) -> Result<Source, Error> {
    self.loader.load_from_stdin(&mut self.global_heap.heap)
  }

  /// Creates a module from the given constants and instructions.
  pub fn new_module(
    &mut self,
    consts: Box<[Const]>,
    exports: ExportInfo,
    insts: Box<[Inst]>,
  ) -> Result<Source, Error> {
    self
      .loader
      .new_module(consts, exports, insts, &mut self.global_heap.heap)
  }

  /// Resets the state of the VM.
  pub fn reset(&mut self) {
    self.contexts.clear();
  }

  /// Returns a mutable reference to the context of the given module.
  ///
  /// If the given context does not exists, it will be created first.
  pub fn context(&mut self, module: Source) -> &mut Context<P> {
    &mut self.contexts.entry(module).or_default().context
  }

  /// Adds the given string to the value stack of the given module.
  ///
  /// This method will allocates a heap memory to store the given string,
  /// and push its address to the value stack.
  pub fn add_str(&mut self, module: Source, s: &str) {
    // allocate heap memory
    let bs = s.as_bytes();
    let len = bs.len() as u64;
    let align = mem::size_of_val(&len);
    let layout = Layout::from_size_align(align + len as usize, align).unwrap();
    let ptr = self.global_heap.heap.alloc(layout);
    // write string data
    let addr = self.global_heap.heap.addr_mut(ptr);
    // safety: `Str`'s memory layout is same as the following code's description
    unsafe {
      *(addr as *mut u64) = len;
      std::ptr::copy_nonoverlapping(bs.as_ptr(), (addr as *mut u8).add(align), bs.len());
    }
    // push to stack
    self.context(module).add_ptr(ptr)
  }

  /// Runs garbage collector.
  fn collect(&mut self) -> Result<(), P::Error> {
    let roots = self.contexts.iter().filter_map(|(s, c)| {
      if c.initialized {
        self.loader.module(*s).map(|m| Roots {
          consts: &m.consts,
          proots: c.context.proots(),
        })
      } else {
        None
      }
    });
    self
      .global_heap
      .policy
      .collect(&mut self.global_heap.gc, &mut self.global_heap.heap, roots)
  }
}

impl<P: Policy> VM<P>
where
  P::Value: Clone,
{
  /// Runs the given module.
  pub fn run(&mut self, module: Source) -> Result<(), P::Error> {
    let mut next_to_run = vec![module];
    while let Some(module) = next_to_run.pop() {
      match self.run_until_cf(module)? {
        ControlFlow::Stop => continue,
        ControlFlow::GC => {
          self.collect()?;
          next_to_run.push(module);
        }
        ControlFlow::CallExt(ci) => todo!(),
      }
    }
    Ok(())
  }

  /// Runs the given module until control flow.
  fn run_until_cf(&mut self, module: Source) -> Result<ControlFlow, P::Error> {
    // get context and module
    let context_info = self.contexts.entry(module).or_default();
    let module = P::unwrap_module(self.loader.module(module))?;
    // the context should not be initialized
    assert!(
      !context_info.initialized,
      "context has already been initialized"
    );
    context_info.initialized = false;
    // run the module
    context_info.context.run(module, &mut self.global_heap)
  }

  /// Calls a function in the given module.
  pub fn call(&mut self, module: Source, func: &str) -> Result<(), P::Error> {
    todo!()
  }

  /// Calls a function by the given call information.
  fn call_by_info(&mut self, info: u64) -> Result<(), P::Error> {
    todo!()
  }
}

/// Global heap for all contexts, containing a heap and a garbage collector.
pub struct GlobalHeap<P: Policy> {
  policy: P,
  heap: P::Heap,
  gc: P::GarbageCollector,
}

impl<P: Policy> GlobalHeap<P> {
  /// Creates a new global heap.
  pub fn new(policy: P) -> Self {
    let heap = policy.new_heap();
    let gc = policy.new_gc();
    Self { policy, heap, gc }
  }

  /// Resets the internal state.
  pub fn reset(&mut self) {
    self.heap.reset();
    self.gc.reset();
  }

  /// Loads the given pointer as type `T`.
  pub(super) fn load<T>(&mut self, ptr: u64) -> Result<u64, P::Error>
  where
    T: Copy + IntoU64,
  {
    let len = mem::size_of::<T>();
    P::check_access(&self.heap, ptr, len, len)?;
    Ok(unsafe { *(self.heap.addr(ptr) as *const T) }.into_u64())
  }

  /// Creates a value from a heap constant.
  pub(super) fn val_from_const(&self, c: &HeapConst) -> P::Value {
    P::val_from_const(&self.heap, c)
  }

  /// Stores the given value (of type `T`) to the memory
  /// pointed by the given pointer.
  pub(super) fn store<T>(&mut self, v: P::Value, ptr: u64) -> Result<(), P::Error>
  where
    T: Copy,
  {
    let len = mem::size_of::<T>();
    P::check_access(&self.heap, ptr, len, len)?;
    unsafe { *(self.heap.addr_mut(ptr) as *mut T) = *(&P::get_any(&v) as *const _ as *const T) };
    Ok(())
  }

  /// Checks if the heap should be collected.
  pub(super) fn should_collect(&self) -> bool {
    self.policy.should_collect(&self.heap)
  }

  /// Allocates a new heap memory.
  pub(super) fn alloc(&mut self, size: u64, align: u64) -> Result<u64, P::Error> {
    let layout = P::layout(size as usize, align as usize)?;
    Ok(self.heap.alloc(layout))
  }

  /// Allocates heap memory for the given object metadata pointer.
  pub(super) fn new_object(&mut self, obj_ptr: u64) -> Result<u64, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    self.alloc_obj(object.size, object.align, ObjKind::Obj, obj_ptr)
  }

  /// Allocates array for the given object metadata pointer.
  pub(super) fn new_array(&mut self, obj_ptr: u64, len: u64) -> Result<u64, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    let size = if len != 0 {
      object.aligned_size() * (len - 1) + object.size
    } else {
      0
    };
    self.alloc_obj(size, object.align, ObjKind::Array(len as usize), obj_ptr)
  }

  /// Deallocates the given pointer.
  pub(super) fn dealloc(&mut self, ptr: u64) {
    self.heap.dealloc(ptr)
  }

  /// Allocates a new memory with object metadata.
  fn alloc_obj(
    &mut self,
    size: u64,
    align: u64,
    kind: ObjKind,
    obj_ptr: u64,
  ) -> Result<u64, P::Error> {
    let layout = P::layout(size as usize, align as usize)?;
    Ok(self.heap.alloc_obj(layout, Obj { kind, ptr: obj_ptr }))
  }
}

/// Context information.
struct ContextInfo<P: Policy> {
  context: Context<P>,
  initialized: bool,
}

impl<P: Policy> Default for ContextInfo<P> {
  fn default() -> Self {
    Self {
      context: Default::default(),
      initialized: false,
    }
  }
}

/// Control flow actions.
pub enum ControlFlow {
  /// Stop execution.
  Stop,
  /// Requests a garbage collection.
  GC,
  /// Requests an external call, with a heap pointer to the call information.
  CallExt(u64),
}
