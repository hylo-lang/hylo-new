#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

/// Prints the Hylo `Int32` pointed to by `x` followed by a newline.
///
/// `result` is the Hylo output parameter for the `Void` return value; it is ignored.
void hylo_print_int(intptr_t *x, void *result) {
    printf("%" PRId64 "\n", *x);
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Int.zero(:) -> Int`.
void hylo_make_zero_int(intptr_t * result) {
    *result = 0;
}

/// Sets `result` to `self + 1`.
///
/// Definition of `Hylo.Int.successor(self: Int) -> Int`.
void hylo_successor_int(intptr_t const* self, intptr_t* result) {
    *result = *self + 1;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Int32.zero(:) -> Int32`.
void hylo_make_zero_i32(int32_t* result) {
    *result = 0;
}
