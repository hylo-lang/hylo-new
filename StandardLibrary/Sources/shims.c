/// C implementations of standard library functions declared with `@c_ffi`.

#include <inttypes.h>
#include <stddef.h>
#include <stdlib.h>

/// Allocates `n` bytes of heap memory and sets `results to the allocation's address, 
/// or 0 on failure.
void c_malloc_indirect(intptr_t const* n, void** result){
  *result = malloc((size_t)(*n));
  // TODO accept `size_t` (UInt) parameter.
}

/// Deallocates heap memory at `address`.
/// 
/// - Requires: there is a live heap allocation starting at `address`.
void c_free_indirect(void** address){
  free(*address);
}