/// C implementations of standard library functions declared with `@extern_c_indirect`.

#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

/// Allocates `n` bytes of heap memory and sets `results` to the allocation's address,
/// or 0 on failure.
void c_malloc_indirect(intptr_t const* n, void** result) {
  *result = malloc((size_t)(*n));
  // TODO accept `size_t` (UInt) parameter.
}

/// Deallocates heap memory at `address`.
///
/// - Requires: there is a live heap allocation starting at `address`.
void c_free_indirect(void** address) {
  free(*address);
}

/// Associates a stream with `descriptor`, which is an existing file descriptor, and `mode`, which
/// describes the behavior of the stream.
void c_fdopen_indirect(intptr_t const* descriptor, void** mode, void** result) {
  int d = (int)(*descriptor);
  *result = fdopen(d, *mode);
}

/// Writes to `stream` the contents of `data`, which contains `count` elements of `size` bytes,
/// reporting the number of elements written to `result`.
void c_fwrite_indirect(
  void** data, intptr_t const* size, intptr_t const* count, void** stream,
  intptr_t* result
) {
  size_t s = (size_t)(*size);
  size_t c = (size_t)(*count);
  int written = fwrite(*data, s, c, *stream);
  *result = (intptr_t)(written);
}
