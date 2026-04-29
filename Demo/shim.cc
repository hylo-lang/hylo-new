#include "raylib.h"
#include "raylib/include/raylib.h"
#include "rlgl.h"
#include <stdio.h>
#include <cstdint>

extern "C" void raylib_init_window(std::intptr_t* w, std::intptr_t* h, void* r) {
  InitWindow(*w, *h, "Demo");
}

extern "C" void raylib_window_should_close(bool* result) {
  *result = WindowShouldClose();
}

extern "C" void raylib_clear_background(Color const* color, void* r) {
  ClearBackground(*color);
}

extern "C" void raylib_begin_drawing(void* r) {
  BeginDrawing();
}

extern "C" void raylib_end_drawing(void* r) {
  EndDrawing();
}

extern "C" void raylib_push_matrix(void* r) {
  rlPushMatrix();
}

extern "C" void raylib_pop_matrix(void* r) {
  rlPopMatrix();
}

extern "C" void raylib_mouse_x(intptr_t* r) {
  *r = static_cast<intptr_t>(GetMouseX());
}

extern "C" void raylib_mouse_y(intptr_t* r) {
  *r = static_cast<intptr_t>(GetMouseY());
}

extern "C" void float_to_intptr(float const* f, intptr_t* r) {
  *r = static_cast<intptr_t>(*f);
}

extern "C" void raylib_rotate(float const* degrees, Vector3 const* axis, void* result) {
  rlRotatef(*degrees, axis->x, axis->y, axis->z);
}

extern "C" void raylib_rectangle(float const* x, float const* y, float const* width, float const* height, Color const* color, void* result) {
  DrawRectangle(*x, *y, *width, *height, *color);
}

extern "C" void int_to_float(intptr_t const* i, float* f) {
  *f = static_cast<float>(*i);
}

extern "C" void raylib_translate(float const* x, float const* y, void* result) {
  rlTranslatef(*x, *y, 0.0f);
}