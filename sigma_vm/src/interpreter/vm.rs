use crate::bytecode::consts::{Const, HeapConst, Str};
use crate::bytecode::export::{ExportInfo, NumArgs};
use crate::bytecode::insts::Inst;
use crate::interpreter::context::{Context, DestructorKind, GlobalContext};
use crate::interpreter::gc::{GarbageCollector, ModuleRoots, Roots};
use crate::interpreter::heap::{Heap, Obj, ObjKind, Ptr};
use crate::interpreter::loader::{Error, Loader, Source};
use crate::interpreter::policy::Policy;
use crate::interpreter::syscall::{Resolver, VmState};
use crate::utils::{IntoU64, Unsized};
use std::alloc::Layout;
use std::collections::HashMap;
use std::iter::{self, Flatten};
use std::path::Path;
use std::slice::Iter;
use std::{mem, slice};

/// Virtual machine for running bytecode.
pub struct VM<P: Policy> {
  loader: Loader,
  resolver: Resolver<P, P::Heap>,
  global_heap: GlobalHeap<P>,
  value_stack: Vec<P::Value>,
  module_globals: HashMap<Source, Vars<P::Value>>,
}

impl<P: Policy> VM<P> {
  /// Creates a new virtual machine.
  pub fn new(policy: P) -> Self {
    Self {
      loader: Loader::new(),
      resolver: Resolver::new(),
      global_heap: GlobalHeap::new(policy),
      value_stack: vec![],
      module_globals: HashMap::new(),
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

  /// Returns a mutable reference to the system call resolver.
  pub fn resolver_mut(&mut self) -> &mut Resolver<P, P::Heap> {
    &mut self.resolver
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

  /// Returns a reference to the heap.
  pub fn heap(&self) -> &P::Heap {
    &self.global_heap.heap
  }

  /// Returns global variables of the given module,
  /// or [`None`] if the module does not exist, not loaded or not initialized.
  pub fn globals(&self, module: Source) -> Option<&Vars<P::Value>> {
    self.module_globals.get(&module)
  }

  /// Runs garbage collector, returns pointers to be deallocated.
  fn collect(
    &mut self,
    contexts: &[Context<P>],
    context: &Context<P>,
  ) -> Result<Vec<Ptr>, P::Error> {
    let mroots = self.module_globals.iter().flat_map(|(s, g)| {
      self.loader.module(*s).map(|m| ModuleRoots::<P> {
        consts: &m.consts,
        globals: g,
      })
    });
    let croots = contexts
      .iter()
      .chain(iter::once(context))
      .map(|c| c.roots());
    self.global_heap.gc.collect(
      &self.global_heap.heap,
      Roots {
        values: &self.value_stack,
        mroots,
        croots,
      },
    )
  }
}

impl<P: Policy> VM<P>
where
  P::Value: Clone,
{
  /// Runs the given module's `main` function.
  ///
  /// This method will retain the state of all contexts,
  /// call [`terminate`](VM#method.terminate) to stop the VM completely.
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
  ///
  /// This method will retain the state of all contexts,
  /// call [`terminate`](VM#method.terminate) to stop the VM completely.
  pub fn call<I>(&mut self, module: Source, func: &str, args: I) -> Result<Vec<P::Value>, P::Error>
  where
    I: IntoIterator<Item = P::Value>,
  {
    // get call site information
    let m = P::unwrap_module(self.loader.module(module))?;
    let call_site = P::unwrap_module(m.call_site(func))?;
    // check arguments
    let args: Vec<_> = args.into_iter().collect();
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
    self.value_stack.extend(args);
    let num_rets = call_site.num_rets;
    Scheduler::new(self, Context::call(module, call_site.pc)).run()?;
    // get return values
    let mut rets = vec![];
    for _ in 0..num_rets {
      rets.push(P::unwrap_val(self.value_stack.pop())?);
    }
    rets.reverse();
    Ok(rets)
  }

  /// Terminates all VM contexts.
  pub fn terminate(&mut self) -> Result<(), P::Error> {
    Scheduler::new(self, Context::terminator()).run()
  }

  /// Resets the internal state.
  pub fn reset(&mut self) {
    self.loader.unload_all();
    self.global_heap.reset();
    self.value_stack.clear();
    self.module_globals.clear();
  }
}

/// Global heap for all contexts, containing a heap and a garbage collector.
pub(super) struct GlobalHeap<P: Policy> {
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
  pub(super) fn load<T>(&mut self, ptr: Ptr) -> Result<u64, P::Error>
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
  pub(super) fn store<T>(&mut self, v: P::Value, ptr: Ptr) -> Result<(), P::Error>
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
  pub(super) fn alloc(&mut self, size: u64, align: u64) -> Result<Ptr, P::Error> {
    let layout = P::layout(size as usize, align as usize)?;
    Ok(self.heap.alloc(layout))
  }

  /// Allocates heap memory for the given object metadata pointer.
  pub(super) fn new_object(&mut self, obj_ptr: Ptr, source: Source) -> Result<Ptr, P::Error> {
    let object = P::object(&self.heap, obj_ptr)?;
    self.alloc_obj(object.size, object.align, ObjKind::Obj, obj_ptr, source)
  }

  /// Allocates array for the given object metadata pointer.
  pub(super) fn new_array(
    &mut self,
    obj_ptr: Ptr,
    len: u64,
    source: Source,
  ) -> Result<Ptr, P::Error> {
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

  /// Allocates a new memory with object metadata.
  fn alloc_obj(
    &mut self,
    size: u64,
    align: u64,
    kind: ObjKind,
    obj_ptr: Ptr,
    source: Source,
  ) -> Result<Ptr, P::Error> {
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
  fn alloc_str(&mut self, s: &str) -> Ptr {
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
  fn gc_success(&self, dealloc_ptrs: &[Ptr]) -> Result<(), P::Error> {
    let dealloc_size: usize = dealloc_ptrs
      .iter()
      .filter_map(|p| self.heap.size_of(*p))
      .sum();
    self.policy.gc_success(self.heap.size() - dealloc_size)
  }
}

/// Scheduler for running contexts.
struct Scheduler<'vm, P: Policy> {
  vm: &'vm mut VM<P>,
  /// Context stack.
  contexts: Vec<Context<P>>,
  /// Pointers to be deallocated.
  ///
  /// GC is running if this vector is not empty. All pointers in this vector
  /// should be deallocated when running run information for destructor.
  pending_ptrs: Vec<Ptr>,
}

impl<'vm, P: Policy> Scheduler<'vm, P> {
  /// Creates a new runner.
  fn new(vm: &'vm mut VM<P>, context: Context<P>) -> Self {
    Self {
      vm,
      contexts: vec![context],
      pending_ptrs: vec![],
    }
  }

  /// Runs contexts, returns return values.
  fn run(mut self) -> Result<(), P::Error>
  where
    P::Value: Clone,
  {
    while let Some(context) = self.contexts.pop() {
      // handle destructor and terminator
      let mut context = match self.handle_destructors(context)? {
        Some(context) => context,
        None => continue,
      };
      // check if the module is initialized
      let globals = if let Some(globals) = self.vm.module_globals.get_mut(&context.source) {
        globals
      } else {
        self.vm.module_globals.insert(context.source, Vars::new());
        self.init(context);
        continue;
      };
      // run the context
      let module = P::unwrap_module(self.vm.loader.module(context.source))?;
      let cf = context.run(GlobalContext {
        module,
        global_heap: &mut self.vm.global_heap,
        global_vars: globals,
        value_stack: &mut self.vm.value_stack,
      })?;
      // handle control flow
      match cf {
        ControlFlow::Stop => continue,
        ControlFlow::GC => self.gc(context)?,
        ControlFlow::LoadModule(ptr) => self.load_module(context, ptr)?,
        ControlFlow::LoadModuleMem(ptr, len) => self.load_module_mem(context, ptr, len)?,
        ControlFlow::CallExt(handle, ptr) => self.call_ext(context, handle, ptr)?,
        ControlFlow::Syscall(syscall) => self.syscall(context, syscall)?,
      }
    }
    Ok(())
  }

  /// Handles destructors and terminators.
  fn handle_destructors(&mut self, context: Context<P>) -> Result<Option<Context<P>>, P::Error> {
    // deallocate all pending pointers
    if context.destructor_kind.is_some() {
      for ptr in mem::take(&mut self.pending_ptrs) {
        self.vm.global_heap.heap.dealloc(ptr);
      }
    }
    // handle terminator
    if context.destructor_kind == Some(DestructorKind::Terminator) {
      self.contexts.push(context);
      // call destructors for all heap objects
      for ptr in self.vm.global_heap.heap.ptrs() {
        if self.schedule_destructor(ptr)? {
          self.pending_ptrs.push(ptr);
        }
      }
      // stop if no scheduled destructors
      if self.contexts.len() == 1 {
        self.contexts.pop();
      }
      Ok(None)
    } else {
      Ok(Some(context))
    }
  }

  /// Initializes the given context information.
  fn init(&mut self, context: Context<P>) {
    let init = Context::init(context.source);
    // check if some one is calling initializer
    if context.pc != 0 {
      // Push argument only when the initializer is called implicitly.
      // In other words, if it's called explicitly, the argument should
      // be pushed by the caller.
      self.vm.value_stack.push(P::int_val(context.source.into()));
      self.contexts.push(context);
    }
    self.contexts.push(init);
  }

  /// Runs garbage collector.
  fn gc(&mut self, context: Context<P>) -> Result<(), P::Error> {
    // skip if garbage collector is already running
    // this means the module is trying to allocate memory in the destructor
    if !self.pending_ptrs.is_empty() {
      return Ok(());
    }
    // run garbage collector
    let ptrs = self.vm.collect(&self.contexts, &context)?;
    self.vm.global_heap.gc_success(&ptrs)?;
    self.contexts.push(context.into_destructor());
    // schedule destructors to run
    for ptr in ptrs {
      if self.schedule_destructor(ptr)? {
        self.pending_ptrs.push(ptr);
      } else {
        // no destructor, just deallocate
        self.vm.global_heap.heap.dealloc(ptr);
      }
    }
    Ok(())
  }

  /// Schedules the destructor of the given pointer to run.
  /// Returns `true` if the pointer has a destructor.
  fn schedule_destructor(&mut self, ptr: Ptr) -> Result<bool, P::Error> {
    if let Some(obj) = self.vm.global_heap.heap.obj(ptr) {
      // get object metadata
      let object = P::object(&self.vm.global_heap.heap, obj.ptr)?;
      if object.destructor == 0 {
        // object has no destructor
        Ok(false)
      } else {
        // issue destructors to run
        match obj.kind {
          ObjKind::Obj => {
            self.vm.value_stack.push(P::ptr_val(ptr));
            self
              .contexts
              .push(Context::call(obj.source, object.destructor))
          }
          ObjKind::Array(len) => {
            // visit all objects
            let step = object.aligned_size();
            for i in 0..len as u64 {
              let ptr = ptr + i * step;
              self.vm.value_stack.push(P::ptr_val(ptr));
              self
                .contexts
                .push(Context::call(obj.source, object.destructor));
            }
          }
        }
        Ok(true)
      }
    } else {
      // not an object
      Ok(false)
    }
  }

  /// Loads module from the given path pointer.
  fn load_module(&mut self, context: Context<P>, ptr: Ptr) -> Result<(), P::Error> {
    // load module
    let path = P::utf8_str(&self.vm.global_heap.heap, ptr)?.to_string();
    let handle = Source::from(
      self
        .vm
        .loader
        .load_from_path(path, &mut self.vm.global_heap.heap),
    );
    // push handle to value stack
    self.vm.value_stack.push(P::int_val(handle.into()));
    self.contexts.push(context.into_cont());
    Ok(())
  }

  /// Loads module from the given memory.
  fn load_module_mem(&mut self, context: Context<P>, ptr: Ptr, len: u64) -> Result<(), P::Error> {
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
    self.vm.value_stack.push(P::int_val(handle.into()));
    self.contexts.push(context.into_cont());
    Ok(())
  }

  /// Calls an external function by the given handle and name pointer.
  fn call_ext(&mut self, context: Context<P>, handle: u64, ptr: Ptr) -> Result<(), P::Error> {
    // get the target module
    let target = Source::from(handle);
    let module = P::unwrap_module(self.vm.loader.module(target))?;
    // get call site information
    let name = P::utf8_str(&self.vm.global_heap.heap, ptr)?;
    let call_site = P::unwrap_module(module.call_site(name))?;
    // perform call
    self.contexts.push(context.into_cont());
    self.contexts.push(Context::call(target, call_site.pc));
    Ok(())
  }

  /// Calls a system call with the given system call number.
  fn syscall(&mut self, context: Context<P>, syscall: i64) -> Result<(), P::Error> {
    use crate::interpreter::syscall::ControlFlow;
    let scf = self.vm.resolver.call(
      syscall,
      VmState {
        loader: &mut self.vm.loader,
        heap: &mut self.vm.global_heap.heap,
        value_stack: &mut self.vm.value_stack,
        module_globals: &mut self.vm.module_globals,
      },
    )?;
    match scf {
      ControlFlow::Continue => self.contexts.push(context.into_cont()),
      ControlFlow::Terminate => {
        self.contexts.clear();
        self.contexts.push(Context::terminator());
      }
      ControlFlow::GC => self.gc(context.into_cont())?,
    }
    Ok(())
  }
}

/// Variable storage.
#[derive(Debug)]
pub struct Vars<V> {
  vars: Vec<Option<V>>,
}

impl<V> Vars<V> {
  /// Creates a new variable storage.
  pub fn new() -> Self {
    Self { vars: vec![] }
  }

  /// Returns a reference of the variable at the given index,
  /// or [`None`] if no such variable.
  pub fn get(&self, index: usize) -> Option<&V> {
    match self.vars.get(index) {
      Some(v) => v.as_ref(),
      None => None,
    }
  }

  /// Returns a mutable reference of the variable at the given index,
  /// or [`None`] if no such variable.
  pub fn get_mut(&mut self, index: usize) -> Option<&mut V> {
    match self.vars.get_mut(index) {
      Some(v) => v.as_mut(),
      None => None,
    }
  }

  /// Sets the variable at the given index to the given value.
  /// Creates a new variable with the value if no such variable.
  pub fn set_or_create(&mut self, index: usize, v: V) {
    if let Some(var) = self.vars.get_mut(index) {
      *var = Some(v);
    } else {
      self.vars.resize_with(index + 1, || None);
      self.vars[index] = Some(v);
    }
  }

  /// Returns an iterator of all variables.
  pub fn iter(&self) -> Flatten<Iter<Option<V>>> {
    self.vars.iter().flatten()
  }
}

impl<V> Default for Vars<V> {
  fn default() -> Self {
    Self::new()
  }
}

impl<'a, V> IntoIterator for &'a Vars<V> {
  type Item = &'a V;
  type IntoIter = Flatten<Iter<'a, Option<V>>>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

/// Control flow actions.
pub(super) enum ControlFlow {
  /// Stop execution.
  Stop,
  /// Requests a garbage collection.
  GC,
  /// Requests to load a external module, with a pointer to the module name.
  LoadModule(Ptr),
  /// Requests to load a external module, with a pointer to the module data
  /// and the size of the data.
  LoadModuleMem(Ptr, u64),
  /// Requests an external call, with a module handle and
  /// a pointer to the function name.
  CallExt(u64, Ptr),
  /// Requests a system call, with a system call number.
  Syscall(i64),
}
