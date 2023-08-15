#ifndef SIGMA_VM_NATIVE_H_
#define SIGMA_VM_NATIVE_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/// Virtual machine heap.
typedef void *sigma_vm_heap_t;

///
/// Virtual machine state.
///
typedef struct {
  sigma_vm_heap_t heap;
  size_t num_args;
  const uint64_t *args;
} sigma_vm_state_t;

///
/// Return values of native call.
///
typedef struct {
  size_t num_rets;
  const uint64_t *rets;
} sigma_vm_ret_vals_t;

///
/// Allocates a new memory with the given size and align.
/// Returns the heap pointer of the allocated memory.
///
/// Panics if size or align are invalid.
///
uint64_t sigma_vm_heap_alloc(sigma_vm_heap_t heap, size_t size, size_t align);

///
/// Returns the memory address of the given pointer.
///
void *sigma_vm_heap_addr(sigma_vm_heap_t heap, uint64_t ptr);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // SIGMA_VM_NATIVE_H_
