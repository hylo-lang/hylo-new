#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>

struct Point {
  intptr_t x;
  intptr_t y;
};

void Point_init_indirect(
  struct Point* self, intptr_t const* x, intptr_t const* y
) {
  self->x = *x;
  self->y = *y;
}


void Point_get_x_indirect(struct Point const* self, intptr_t* result) {
  *result = self->x;
}

void Point_get_y_indirect(struct Point const* self, intptr_t* result) {
  *result = self->y;
}

void Point_set_x_indirect(struct Point* self, intptr_t const* new_value) {
  self->x = *new_value;
}

void Point_set_y_indirect(struct Point* self, intptr_t const* new_value) {
  self->y = *new_value;
}

void Point_add_indirect(
  struct Point const* a, struct Point const* b, struct Point* result
) {
  result->x = a->x + b->x;
  result->y = a->y + b->y;
}

void Int_add_indirect(
  intptr_t const* a, intptr_t const* b, intptr_t* result
) {
    *result = *a + *b;
}

void Int_to_i32_indirect(
  intptr_t const* self, int32_t* result
) {
  *result = (int32_t)*self;
}

void set_value_to_3_at_address_indirect(char** p) {
  *(*p) = (char)3;
}

void get_byte_value_at_address_indirect(char const** p, intptr_t* result) {
  *result = (intptr_t)**p;
}
