#ifndef SIGMA_VM_NATIVE_H_
#define SIGMA_VM_NATIVE_H_

#include <stddef.h>
#include <stdint.h>

///
/// Virtual machine heap.
///
typedef void *sigma_vm_heap_t;

///
/// Heap pointer.
///
typedef uint64_t sigma_vm_ptr_t;

///
/// Virtual machine state.
///
typedef struct {
  sigma_vm_heap_t heap;
  size_t num_args;
  const uint64_t *args;
  const void *heap_alloc;
  const void *heap_addr;
} sigma_vm_state_t;

///
/// Return values of native call.
///
typedef struct {
  size_t num_rets;
  const uint64_t *rets;
} sigma_vm_ret_vals_t;

///
/// String.
///
typedef struct {
  uint64_t len;
  uint8_t bytes[];
} sigma_vm_str_t;

///
/// Managed pointer information.
///
typedef struct {
  uint64_t len;
  uint64_t offsets[];
} sigma_vm_managed_ptr_t;

///
/// Object metadata.
///
typedef struct {
  uint64_t size;
  uint64_t align;
  uint64_t destructor;
  sigma_vm_managed_ptr_t managed_ptr;
} sigma_vm_object_t;

///
/// Raw data.
///
typedef struct {
  uint64_t len;
  uint8_t bytes[];
} sigma_vm_raw_t;

///
/// Allocates a new memory with the given size and align.
/// Returns the heap pointer of the allocated memory.
///
/// Panics if size or align are invalid.
///
static inline sigma_vm_ptr_t sigma_vm_heap_alloc(const sigma_vm_state_t *vm,
                                                 size_t size, size_t align) {
  typedef sigma_vm_ptr_t (*heap_alloc_t)(sigma_vm_heap_t, size_t, size_t);
  return ((heap_alloc_t)vm->heap_alloc)(vm->heap, size, align);
}

///
/// Returns the memory address of the given pointer.
///
static inline void *sigma_vm_heap_addr(const sigma_vm_state_t *vm,
                                       sigma_vm_ptr_t ptr) {
  typedef void *(*heap_addr_t)(sigma_vm_heap_t, sigma_vm_ptr_t);
  return ((heap_addr_t)vm->heap_addr)(vm->heap, ptr);
}

#endif  // SIGMA_VM_NATIVE_H_
