/// C implementations of standard library functions declared with `@extern_c_indirect`.

#include <inttypes.h>
#include <stddef.h>
#include <stdlib.h>

/// Allocates `n` bytes of memory on the heap and sets `results` to the allocation's address or `0`
/// if the allocation failed.
void c_malloc_indirect(intptr_t const* n, void** result){
  *result = malloc((size_t)(*n));
  // TODO accept `size_t` (UInt) parameter.
}

/// Deallocates the memory at `address`.
///
/// - Requires: The memory at `address` is the start of an allocation made via `c_malloc_indirect`.
void c_free_indirect(void** address){
  free(*address);
}
