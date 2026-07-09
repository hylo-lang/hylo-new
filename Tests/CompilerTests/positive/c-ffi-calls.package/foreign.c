#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>

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

void c_add_int_indirect(
  intptr_t const* a, intptr_t const* b, intptr_t* result
) {
    *result = *a + *b;
}

void c_int_to_i32_indirect(
  intptr_t const* self, int32_t* result
) {
  *result = (int32_t)*self;
}

void c_byte_set_value_to_3_indirect(char** p) {
  *(*p) = (char)3;
}

void c_byte_get_value(char const** p, intptr_t* result) {
  *result = (intptr_t)**p;
}