/// C implementations of standard library functions declared with `@c_ffi`.
///
/// These functions follow the indirect calling convention: they accept one pointer for each
/// parameter of the corresponding Hylo declaration, in order, followed by a pointer to the
/// storage receiving the result, and return `void`. The result pointer is present even when
/// there is nothing to return.

#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>

void c_print_int_indirect(intptr_t const* n) {
  printf("%" PRIdPTR "\n", *n);
}

struct Point {
  intptr_t x;
  intptr_t y;
};

void c_point_add_indirect(
  struct Point const* a, struct Point const* b, struct Point* result
) {
  result->x = a->x + b->x;
  result->y = a->y + b->y;
}
