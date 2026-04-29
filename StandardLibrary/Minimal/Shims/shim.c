#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>

/// Prints the Hylo `Int` pointed to by `x` followed by a newline.
///
/// `result` is the Hylo output parameter for the `Void` return value; it is ignored.
void hylo_print_int(const intptr_t *x, void *result) {
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

/// Sets `result` to `self + other`.
void hylo_int_infix_add(const intptr_t* self, const intptr_t* other, intptr_t* result) {
    *result = *self + *other;
}

/// Sets `result` to `self - other`.
void hylo_int_infix_subtract(const intptr_t* self, const intptr_t* other, intptr_t* result) {
    *result = *self - *other;
}

/// Sets `result` to `self * other`.
void hylo_int_infix_multiply(const intptr_t* self, const intptr_t* other, intptr_t* result) {
    *result = *self * *other;
}

/// Initializes `self` with the raw integer value in `value`.
void hylo_init_int_from_raw(intptr_t* self, const intptr_t* value) {
    *self = *value;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Int32.zero(:) -> Int32`.
void hylo_make_zero_i32(int32_t* result) {
    *result = 0;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.UInt8.init()`.
void hylo_init_uint8(uint8_t* result) {
    *result = 0;
}

/// Initializes `self` with the raw integer value in `value`.
void hylo_init_uint8_from_raw(uint8_t* self, const uint8_t* value) {
    *self = *value;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.UInt8.zero(:) -> UInt8`.
void hylo_make_zero_uint8(uint8_t* result) {
    *result = 0;
}

/// Sets `result` to one.
///
/// Definition of `Hylo.UInt8.one(:) -> UInt8`.
void hylo_make_one_uint8(uint8_t* result) {
    *result = 1;
}

/// Sets `result` to `self + 1`.
///
/// Definition of `Hylo.UInt8.successor(self: UInt8) -> UInt8`.
void hylo_successor_uint8(const uint8_t* self, uint8_t* result) {
    *result = (uint8_t)(*self + 1);
}

/// Sets `result` to the value of `self`.
void hylo_uint8_get_value(const uint8_t* self, uint8_t* result) {
    *result = *self;
}

/// Sets `result` to `self == other`.
void hylo_uint8_eq(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self == *other);
}

/// Sets `result` to `self != other`.
void hylo_uint8_ne(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self != *other);
}

/// Sets `result` to `self < other`.
void hylo_uint8_lt(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self < *other);
}

/// Sets `result` to `self <= other`.
void hylo_uint8_le(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self <= *other);
}

/// Sets `result` to `self > other`.
void hylo_uint8_gt(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self > *other);
}

/// Sets `result` to `self >= other`.
void hylo_uint8_ge(const uint8_t* self, const uint8_t* other, char* result) {
    *result = (char)(*self >= *other);
}

/// Sets `result` to `self + other`.
void hylo_uint8_infix_add(const uint8_t* self, const uint8_t* other, uint8_t* result) {
    *result = (uint8_t)(*self + *other);
}

/// Sets `result` to `self - other`.
void hylo_uint8_infix_subtract(const uint8_t* self, const uint8_t* other, uint8_t* result) {
    *result = (uint8_t)(*self - *other);
}

/// Sets `result` to `self * other`.
void hylo_uint8_infix_multiply(const uint8_t* self, const uint8_t* other, uint8_t* result) {
    *result = (uint8_t)(*self * *other);
}

/// Allocates `size` bytes and stores the address in `result`.
void malloc_shim(intptr_t const* size, void** result) {
    *result = malloc(*size);
}

/// Frees the heap allocation referenced by `*ptr`.
void free_shim(void** ptr, void* voidResult) {
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

/// Initializes `result` with `value`.
void hylo_bool_memberwise_init(char* result, const char* value) {
    *result = *value;
}

/// Bool.init() — sets `result` to false.
void hylo_init_bool(char* result) {
    *result = 0;
}

/// Sets `result` to the logical negation of `*self`.
void hylo_bool_prefix_not(const char* self, char* result) {
    *result = (char)(*self == 0);
}

/// Sets `result` to `self == other`.
void hylo_bool_eq(const char* self, const char* other, char* result) {
    *result = (char)((*self != 0) == (*other != 0));
}

/// Sets `result` to `self != other`.
void hylo_bool_ne(const char* self, const char* other, char* result) {
    *result = (char)((*self != 0) != (*other != 0));
}

/// Sets `result` to the value of `self`.
void hylo_int_get_value(const intptr_t* self, intptr_t* result) {
    *result = *self;
}

/// Sets `result` to `self == other`.
void hylo_int_eq(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self == *other);
}

/// Sets `result` to `self != other`.
void hylo_int_ne(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self != *other);
}

/// Sets `result` to `self < other`.
void hylo_int_lt(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self < *other);
}

/// Sets `result` to `self <= other`.
void hylo_int_le(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self <= *other);
}

/// Sets `result` to `self > other`.
void hylo_int_gt(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self > *other);
}

/// Sets `result` to `self >= other`.
void hylo_int_ge(const intptr_t* self, const intptr_t* other, char* result) {
    *result = (char)(*self >= *other);
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Float32.init()`.
void hylo_float32_init(float* result) {
    *result = 0.0f;
}

/// Sets `result` to `self == other`.
void hylo_float32_eq(const float* self, const float* other, char* result) {
    *result = (char)(*self == *other);
}

/// Sets `result` to `self != other`.
void hylo_float32_ne(const float* self, const float* other, char* result) {
    *result = (char)(*self != *other);
}

/// Sets `result` to `self < other`.
void hylo_float32_lt(const float* self, const float* other, char* result) {
    *result = (char)(*self < *other);
}

/// Sets `result` to `self <= other`.
void hylo_float32_le(const float* self, const float* other, char* result) {
    *result = (char)(*self <= *other);
}

/// Sets `result` to `self > other`.
void hylo_float32_gt(const float* self, const float* other, char* result) {
    *result = (char)(*self > *other);
}

/// Sets `result` to `self >= other`.
void hylo_float32_ge(const float* self, const float* other, char* result) {
    *result = (char)(*self >= *other);
}

/// Sets `result` to `self + other`.
void hylo_float32_infix_add(const float* self, const float* other, float* result) {
    *result = *self + *other;
}

/// Sets `result` to `self - other`.
void hylo_float32_infix_subtract(const float* self, const float* other, float* result) {
    *result = *self - *other;
}

/// Sets `result` to `self * other`.
void hylo_float32_infix_multiply(const float* self, const float* other, float* result) {
    *result = *self * *other;
}

/// Sets `result` to `self / other`.
void hylo_float32_infix_divide(const float* self, const float* other, float* result) {
    *result = *self / *other;
}

/// Sets `result` to zero.
///
/// Definition of `Hylo.Float64.init()`.
void hylo_float64_init(double* result) {
    *result = 0.0;
}

/// Sets `result` to `self == other`.
void hylo_float64_eq(const double* self, const double* other, char* result) {
    *result = (char)(*self == *other);
}

/// Sets `result` to `self != other`.
void hylo_float64_ne(const double* self, const double* other, char* result) {
    *result = (char)(*self != *other);
}

/// Sets `result` to `self < other`.
void hylo_float64_lt(const double* self, const double* other, char* result) {
    *result = (char)(*self < *other);
}

/// Sets `result` to `self <= other`.
void hylo_float64_le(const double* self, const double* other, char* result) {
    *result = (char)(*self <= *other);
}

/// Sets `result` to `self > other`.
void hylo_float64_gt(const double* self, const double* other, char* result) {
    *result = (char)(*self > *other);
}

/// Sets `result` to `self >= other`.
void hylo_float64_ge(const double* self, const double* other, char* result) {
    *result = (char)(*self >= *other);
}

/// Sets `result` to `self + other`.
void hylo_float64_infix_add(const double* self, const double* other, double* result) {
    *result = *self + *other;
}

/// Sets `result` to `self - other`.
void hylo_float64_infix_subtract(const double* self, const double* other, double* result) {
    *result = *self - *other;
}

/// Sets `result` to `self * other`.
void hylo_float64_infix_multiply(const double* self, const double* other, double* result) {
    *result = *self * *other;
}

/// Sets `result` to `self / other`.
void hylo_float64_infix_divide(const double* self, const double* other, double* result) {
    *result = *self / *other;
}

/// Prints `x` with 4 fractional digits, followed by a newline.
void hylo_print_float32(float* x, void* result) {
    printf("%.4f\n", *x);
}

/// Prints `x` with 4 fractional digits, followed by a newline.
void hylo_print_float64(double* x, void* result) {
    printf("%.4f\n", *x);
}
