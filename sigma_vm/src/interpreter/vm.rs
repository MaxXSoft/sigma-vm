use crate::bytecode::consts::{Const, HeapConst};
use crate::bytecode::export::{ExportInfo, NumArgs};
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

  /// Resets the state of the VM. Loaded modules will not be unloaded.
  pub fn reset(&mut self) {
    self.global_heap.reset();
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
    let ptr = self.global_heap.alloc_str(s);
    self.context(module).add_ptr(ptr);
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
  /// Runs the given module's `main` function.
  pub fn run_main<I, S>(&mut self, module: Source, args: I) -> Result<Vec<P::Value>, P::Error>
  where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
  {
    // push arguments
    let mut args: Vec<_> = args
      .into_iter()
      .map(|s| P::ptr_val(self.global_heap.alloc_str(s.as_ref())))
      .collect();
    args.push(P::int_val(args.len() as u64));
    // call main function
    self.call(module, "main", args)
  }

  /// Calls a function in the given module, returns the return values.
  pub fn call<I>(&mut self, module: Source, func: &str, args: I) -> Result<Vec<P::Value>, P::Error>
  where
    I: IntoIterator<Item = P::Value>,
  {
    // get call site information
    let m = P::unwrap_module(self.loader.module(module))?;
    let call_site = P::unwrap_module(m.call_site(func))?;
    // check arguments
    let mut args: Vec<_> = args.into_iter().collect();
    let is_valid = match call_site.num_args {
      NumArgs::Variadic => match args.last() {
        Some(v) => P::get_int_ptr(v)? + 1 == args.len() as u64,
        None => false,
      },
      NumArgs::PlusOne(np1) => np1.get() - 1 == args.len() as u64,
    };
    if !is_valid {
      P::report_invalid_args()?;
    }
    // call the target function
    args.reverse();
    let ci = CallInfo::call(args, call_site.num_rets);
    self.run(module, call_site.pc, ci).map(|mut r| {
      r.reverse();
      r
    })
  }

  /// Runs the given module from the given PC.
  /// Returns return values in reversed order.
  fn run(&mut self, source: Source, pc: u64, ci: CallInfo<P>) -> Result<Vec<P::Value>, P::Error> {
    // check if the context is initialized
    let context_info = self.contexts.entry(source).or_default();
    if !context_info.initialized {
      // prevent from infinite recursion
      context_info.initialized = true;
      if pc != 0 {
        self.run(source, 0, CallInfo::init())?;
      }
    }
    // get module and context
    let module = P::unwrap_module(self.loader.module(source))?;
    let context = &mut self.contexts.entry(source).or_default().context;
    // setup value stack, variable stack and PC
    if let Some(args_rev) = ci.args_rev {
      context.value_stack.extend(args_rev.into_iter().rev());
      context.var_stack.push(Default::default());
    }
    context.set_pc(pc);
    // run the context
    let cf = context.run(module, &mut self.global_heap)?;
    let pc = context.pc();
    // handle control flow
    match cf {
      ControlFlow::Stop => {
        // clean up stacks
        let mut rets_rev = vec![];
        if let Some(num_rets) = ci.num_rets {
          for _ in 0..num_rets {
            rets_rev.push(context.pop()?);
          }
          context.var_stack.pop();
        }
        Ok(rets_rev)
      }
      ControlFlow::GC => {
        self.collect()?;
        return self.run(source, pc, CallInfo::cont(ci.num_rets));
      }
      ControlFlow::LoadModule(ptr) => {
        // load module
        let path = P::utf8_str(&self.global_heap.heap, ptr)?.to_string();
        let handle = Source::from(self.loader.load_from_path(path, &mut self.global_heap.heap));
        // push handle to value stack
        context.add_value(P::int_val(handle.into()));
        return self.run(source, pc + 1, CallInfo::cont(ci.num_rets));
      }
      ControlFlow::UnloadModule(handle) => {
        self.loader.unload(handle.into());
        return self.run(source, pc + 1, CallInfo::cont(ci.num_rets));
      }
      ControlFlow::CallExt(handle, ptr) => {
        // get the target module
        let target = Source::from(handle);
        let module = P::unwrap_module(self.loader.module(target))?;
        // get call site information
        let name = P::utf8_str(&self.global_heap.heap, ptr)?;
        let call_site = P::unwrap_module(module.call_site(name))?;
        // collect arguments
        let mut args_rev = vec![];
        let num_args = match call_site.num_args {
          NumArgs::Variadic => {
            let n = context.pop_int_ptr()?;
            args_rev.push(P::int_val(n));
            n
          }
          NumArgs::PlusOne(np1) => np1.get() - 1,
        };
        for _ in 0..num_args {
          args_rev.push(context.pop()?);
        }
        // perform call
        let call = CallInfo::call(args_rev, call_site.num_rets);
        let rets_rev = self.run(target, call_site.pc, call)?;
        // push return values
        let context = self.context(source);
        context.value_stack.extend(rets_rev.into_iter().rev());
        // continue to run
        return self.run(source, pc + 1, CallInfo::cont(ci.num_rets));
      }
    }
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

  /// Allocates a new string on heap, returns the heap pointer.
  fn alloc_str(&mut self, s: &str) -> u64 {
    // allocate heap memory
    let bs = s.as_bytes();
    let len = bs.len() as u64;
    let align = mem::size_of_val(&len);
    let layout = Layout::from_size_align(align + len as usize, align).unwrap();
    let ptr = self.heap.alloc(layout);
    // write string data
    let addr = self.heap.addr_mut(ptr);
    // safety: `Str`'s memory layout is same as the following code's description
    unsafe {
      *(addr as *mut u64) = len;
      std::ptr::copy_nonoverlapping(bs.as_ptr(), (addr as *mut u8).add(align), bs.len());
    }
    ptr
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

/// Call information.
struct CallInfo<P: Policy> {
  args_rev: Option<Vec<P::Value>>,
  num_rets: Option<u64>,
}

impl<P: Policy> CallInfo<P> {
  /// Creates a call information for initialization.
  fn init() -> Self {
    Self {
      args_rev: None,
      num_rets: None,
    }
  }

  /// Creates a call information for function call.
  fn call(args_rev: Vec<P::Value>, num_rets: u64) -> Self {
    Self {
      args_rev: Some(args_rev),
      num_rets: Some(num_rets),
    }
  }

  /// Creates a call information for continue.
  fn cont(num_rets: Option<u64>) -> Self {
    Self {
      args_rev: None,
      num_rets,
    }
  }
}

/// Control flow actions.
pub enum ControlFlow {
  /// Stop execution.
  Stop,
  /// Requests a garbage collection.
  GC,
  /// Requests to load a external module, with a pointer to the module name.
  LoadModule(u64),
  /// Requests to unload a external module, with a module handle.
  UnloadModule(u64),
  /// Requests an external call, with a module handle and
  /// a pointer to the function name.
  CallExt(u64, u64),
}
