#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>

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

/// Sets `result` to zero.
///
/// Definition of `Hylo.Int.init()`.
void hylo_init_int(intptr_t * result) {
    *result = 0;
}

/// Sets `result` to 1.
///
/// Definition of `Hylo.Int.one(:) -> Int`.
void hylo_make_one_int(intptr_t * result) {
    *result = 1;
}

/// Sets `result` to `self + 1`.
///
/// Definition of `Hylo.Int.successor(self: Int) -> Int`.
void hylo_successor_int(intptr_t const* self, intptr_t* result) {
    *result = *self + 1;
}

void hylo_int_infix_add(intptr_t* self, intptr_t* other, intptr_t* result) {
    *result = *self + *other;
}

void hylo_int_infix_subtract(intptr_t* self, intptr_t* other, intptr_t* result) {
    *result = *self - *other;
}

void hylo_int_infix_multiply(intptr_t* self, intptr_t* other, intptr_t* result) {
    *result = *self * *other;
}

void hylo_init_int_from_raw(intptr_t* self, intptr_t* value) {
    *self = *value;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Int32.zero(:) -> Int32`.
void hylo_make_zero_i32(int32_t* result) {
    *result = 0;
}

void malloc_shim(intptr_t const* size, void** result) {
    *result = malloc(*size);
}

void free_shim(void** ptr) {
    free(*ptr);
}


/// Bool.makeFalse()
void hylo_make_false(char* result) {
    *result = 0;
}

/// Bool.makeTrue()
void hylo_make_true(char* result) {
    *result = 1;
}


void hylo_bool_memberwise_init(char* result, char* value) {
    *result = *value;
}

void hylo_int_get_value(intptr_t* self, intptr_t* result) {
    *result = *self;
}

void hylo_int_eq(intptr_t* self, intptr_t* other, char* result) {
    *result = *self == *other;
}

void hylo_int_ne(intptr_t* self, intptr_t* other, char* result) {
    *result = *self != *other;
}

void hylo_int_lt(intptr_t* self, intptr_t* other, char* result) {
    *result = *self < *other;
}

void hylo_int_le(intptr_t* self, intptr_t* other, char* result) {
    *result = *self <= *other;
}

void hylo_int_gt(intptr_t* self, intptr_t* other, char* result) {
    *result = *self > *other;
}

void hylo_int_ge(intptr_t* self, intptr_t* other, char* result) {
    *result = *self >= *other;
}
