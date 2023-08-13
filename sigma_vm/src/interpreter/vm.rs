use crate::bytecode::consts::{Const, HeapConst, Str};
use crate::bytecode::export::{ExportInfo, NumArgs};
use crate::bytecode::insts::Inst;
use crate::interpreter::context::Context;
use crate::interpreter::gc::{GarbageCollector, Roots};
use crate::interpreter::heap::{Heap, Obj, ObjKind};
use crate::interpreter::loader::{Error, Loader, Source};
use crate::interpreter::policy::Policy;
use crate::utils::{IntoU64, Unsized};
use std::alloc::Layout;
use std::collections::HashMap;
use std::path::Path;
use std::{mem, slice};

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

  /// Runs garbage collector, returns pointers to be deallocated.
  fn collect(&mut self) -> Result<Vec<u64>, P::Error> {
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
    self.global_heap.gc.collect(&self.global_heap.heap, roots)
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
    let ri = RunInfo::call(module, call_site.pc, args, call_site.num_rets);
    Runner::new(self, ri).run()
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
  pub(super) fn new_object(&mut self, obj_ptr: u64, source: Source) -> Result<u64, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    self.alloc_obj(object.size, object.align, ObjKind::Obj, obj_ptr, source)
  }

  /// Allocates array for the given object metadata pointer.
  pub(super) fn new_array(
    &mut self,
    obj_ptr: u64,
    len: u64,
    source: Source,
  ) -> Result<u64, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    let size = if len != 0 {
      object.aligned_size() * (len - 1) + object.size
    } else {
      0
    };
    self.alloc_obj(
      size,
      object.align,
      ObjKind::Array(len as usize),
      obj_ptr,
      source,
    )
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
    source: Source,
  ) -> Result<u64, P::Error> {
    let layout = P::layout(size as usize, align as usize)?;
    Ok(self.heap.alloc_obj(
      layout,
      Obj {
        kind,
        ptr: obj_ptr,
        source,
      },
    ))
  }

  /// Allocates a new string on heap, returns the heap pointer.
  fn alloc_str(&mut self, s: &str) -> u64 {
    // allocate heap memory
    let bs = s.as_bytes();
    let len = bs.len() as u64;
    let layout = Layout::from_size_align(Str::<[u8]>::size(len), Str::<[u8]>::ALIGN).unwrap();
    let ptr = self.heap.alloc(layout);
    // write string data
    let addr = self.heap.addr_mut(ptr);
    // safety: `Str`'s memory layout is same as the following code's description
    unsafe {
      Str::<[u8]>::set_metadata(addr, len);
      std::ptr::copy_nonoverlapping(
        bs.as_ptr(),
        (addr as *mut u8).add(Str::<[u8]>::SIZE),
        bs.len(),
      );
    }
    ptr
  }

  /// Checks if the garbage collector succeeded in reducing the heap size.
  /// Returns an error if necessary.
  fn gc_success(&self, dealloc_ptrs: &[u64]) -> Result<(), P::Error> {
    let dealloc_size: usize = dealloc_ptrs
      .iter()
      .filter_map(|p| self.heap.size_of(*p))
      .sum();
    self.policy.gc_success(self.heap.size() - dealloc_size)
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

/// Runner for running contexts.
struct Runner<'vm, P: Policy> {
  vm: &'vm mut VM<P>,
  ris: Vec<RunInfo<P>>,
}

impl<'vm, P: Policy> Runner<'vm, P> {
  /// Creates a new runner.
  fn new(vm: &'vm mut VM<P>, ri: RunInfo<P>) -> Self {
    Self { vm, ris: vec![ri] }
  }

  /// Runs contexts, returns return values.
  fn run(mut self) -> Result<Vec<P::Value>, P::Error>
  where
    P::Value: Clone,
  {
    while let Some(mut ri) = self.ris.pop() {
      // check if the context is initialized
      let context_info = self.vm.contexts.entry(ri.source).or_default();
      if !context_info.initialized {
        // prevent from infinite loop
        context_info.initialized = true;
        self.init(ri);
        continue;
      }
      // get module and context
      let module = P::unwrap_module(self.vm.loader.module(ri.source))?;
      let context = &mut context_info.context;
      // setup value stack, variable stack and PC
      let obj_ptr = ri.obj_ptr()?;
      ri.setup(context);
      // run the context
      let cf = context.run(ri.source, module, &mut self.vm.global_heap)?;
      ri.pc = context.pc();
      // handle control flow
      match cf {
        ControlFlow::Stop => {
          let rets_rev = ri.cleanup(context)?;
          if let Some(rets) = self.stop(rets_rev, obj_ptr)? {
            return Ok(rets);
          }
        }
        ControlFlow::GC => self.gc(ri)?,
        ControlFlow::LoadModule(ptr) => self.load_module(ri, ptr)?,
        ControlFlow::LoadModuleMem(ptr, len) => self.load_module_mem(ri, ptr, len)?,
        ControlFlow::UnloadModule(handle) => {
          let source = handle.into();
          self.vm.loader.unload(source);
          self.vm.contexts.remove(&source);
          self.ris.push(ri.into_cont());
        }
        ControlFlow::CallExt(handle, ptr) => {
          // get the target module
          let target = Source::from(handle);
          let module = P::unwrap_module(self.vm.loader.module(target))?;
          // get call site information
          let name = P::utf8_str(&self.vm.global_heap.heap, ptr)?;
          let call_site = P::unwrap_module(module.call_site(name))?;
          // collect arguments
          let args_rev = context.args_rev(call_site)?;
          // perform call
          let call = RunInfo::call(target, call_site.pc, args_rev, call_site.num_rets);
          self.ris.push(ri.into_cont());
          self.ris.push(call);
        }
      }
    }
    Ok(vec![])
  }

  /// Initializes the given context information.
  fn init(&mut self, ri: RunInfo<P>) {
    let init = ri.to_init();
    if ri.pc != 0 {
      self.ris.push(ri);
    }
    self.ris.push(init);
  }

  /// Stops the current run. Returns some return value if need to stop running.
  fn stop(
    &mut self,
    rets_rev: Option<Vec<P::Value>>,
    obj_ptr: Option<u64>,
  ) -> Result<Option<Vec<P::Value>>, P::Error> {
    // handle return
    if let Some(mut rets_rev) = rets_rev {
      // update the last run info, or return
      if let Some(last) = self.ris.last_mut() {
        last.values_rev = rets_rev;
      } else {
        // TODO: destructors
        rets_rev.reverse();
        return Ok(Some(rets_rev));
      }
    }
    // handle destructor
    if let Some(obj_ptr) = obj_ptr {
      self.vm.global_heap.heap.dealloc(obj_ptr);
    }
    Ok(None)
  }

  /// Runs garbage collector.
  fn gc(&mut self, ri: RunInfo<P>) -> Result<(), P::Error> {
    let ptrs = self.vm.collect()?;
    self.vm.global_heap.gc_success(&ptrs)?;
    self.ris.push(ri.into_cur());
    // schedule destructors to run
    for ptr in ptrs {
      if let Some(obj) = self.vm.global_heap.heap.obj(ptr) {
        // get object metadata
        let object = P::object(&self.vm.global_heap.heap, obj.ptr)?;
        if object.destructor == 0 {
          // no destructor, just deallocate
          self.vm.global_heap.heap.dealloc(ptr);
        } else {
          match obj.kind {
            ObjKind::Obj => self
              .ris
              .push(RunInfo::destructor(obj.source, object.destructor, ptr)),
            ObjKind::Array(len) => {
              // visit all objects
              let step = object.aligned_size();
              if len != 0 {
                self
                  .ris
                  .push(RunInfo::destructor(obj.source, object.destructor, ptr));
              }
              for i in 1..len as u64 {
                let ptr = P::ptr_val(ptr + i * step);
                self
                  .ris
                  .push(RunInfo::call(obj.source, object.destructor, vec![ptr], 0));
              }
            }
          }
        }
      } else {
        // not an object, just deallocate
        self.vm.global_heap.heap.dealloc(ptr);
      };
    }
    Ok(())
  }

  /// Loads module from the given path pointer.
  fn load_module(&mut self, ri: RunInfo<P>, ptr: u64) -> Result<(), P::Error> {
    // load module
    let path = P::utf8_str(&self.vm.global_heap.heap, ptr)?.to_string();
    let handle = Source::from(
      self
        .vm
        .loader
        .load_from_path(path, &mut self.vm.global_heap.heap),
    );
    // push handle to value stack
    let mut ri = ri.into_cont();
    ri.values_rev.push(P::int_val(handle.into()));
    self.ris.push(ri);
    Ok(())
  }

  /// Loads module from the given memory.
  fn load_module_mem(&mut self, ri: RunInfo<P>, ptr: u64, len: u64) -> Result<(), P::Error> {
    // get byte slice
    P::check_access(&self.vm.global_heap.heap, ptr, len as usize, 1)?;
    let addr = self.vm.global_heap.heap.addr(ptr);
    let bytes = unsafe { slice::from_raw_parts(addr as *const u8, len as usize) };
    // load module
    let handle = Source::from(
      self
        .vm
        .loader
        .load_from_bytes(bytes, &mut self.vm.global_heap.heap),
    );
    // push handle to value stack
    let mut ri = ri.into_cont();
    ri.values_rev.push(P::int_val(handle.into()));
    self.ris.push(ri);
    Ok(())
  }
}

/// Run information.
struct RunInfo<P: Policy> {
  source: Source,
  pc: u64,
  is_call: bool,
  is_destructor: bool,
  values_rev: Vec<P::Value>,
  num_rets: Option<u64>,
}

impl<P: Policy> RunInfo<P> {
  /// Creates a new run information for function call.
  fn call(source: Source, pc: u64, args_rev: Vec<P::Value>, num_rets: u64) -> Self {
    Self {
      source,
      pc,
      is_call: true,
      is_destructor: false,
      values_rev: args_rev,
      num_rets: Some(num_rets),
    }
  }

  /// Creates a new run information for destructor.
  fn destructor(source: Source, pc: u64, ptr: u64) -> Self {
    Self {
      source,
      pc,
      is_call: true,
      is_destructor: true,
      values_rev: vec![P::ptr_val(ptr)],
      num_rets: Some(0),
    }
  }

  /// Converts the current run information to a new one for initialization.
  fn to_init(&self) -> Self {
    Self {
      source: self.source,
      pc: 0,
      is_call: false,
      is_destructor: false,
      values_rev: vec![],
      num_rets: None,
    }
  }

  /// Converts the current run information into a new one for re-run.
  fn into_cur(self) -> Self {
    Self {
      source: self.source,
      pc: self.pc,
      is_call: false,
      is_destructor: false,
      values_rev: vec![],
      num_rets: self.num_rets,
    }
  }

  /// Converts the current run information into a new one for continute.
  fn into_cont(self) -> Self {
    Self {
      source: self.source,
      pc: self.pc + 1,
      is_call: false,
      is_destructor: false,
      values_rev: vec![],
      num_rets: self.num_rets,
    }
  }

  /// Takes the values out of the current run information.
  fn take_values(&mut self) -> impl Iterator<Item = P::Value> {
    mem::take(&mut self.values_rev).into_iter().rev()
  }

  /// Returns the pointer of the object to be destructed
  /// if the current run information is for destructor.
  fn obj_ptr(&self) -> Result<Option<u64>, P::Error> {
    self
      .is_destructor
      .then(|| P::unwrap_val(self.values_rev.last()).and_then(|v| P::get_ptr(v)))
      .transpose()
  }

  /// Sets up the given context.
  fn setup(&mut self, context: &mut Context<P>) {
    context.value_stack.extend(self.take_values());
    if self.is_call {
      context.var_stack.push(Default::default());
    }
    context.set_pc(self.pc);
  }

  /// Cleans up the given context. Returns return values
  /// if the current run information is for function return.
  fn cleanup(&mut self, context: &mut Context<P>) -> Result<Option<Vec<P::Value>>, P::Error> {
    self
      .num_rets
      .map(|num_rets| {
        let mut rets_rev = vec![];
        for _ in 0..num_rets {
          rets_rev.push(context.pop()?);
        }
        context.var_stack.pop();
        Ok(rets_rev)
      })
      .transpose()
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
  /// Requests to load a external module, with a pointer to the module data
  /// and the size of the data.
  LoadModuleMem(u64, u64),
  /// Requests to unload a external module, with a module handle.
  UnloadModule(u64),
  /// Requests an external call, with a module handle and
  /// a pointer to the function name.
  CallExt(u64, u64),
}
