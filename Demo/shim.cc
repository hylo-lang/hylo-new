#include "raylib.h"
#include <stdio.h>
#include <cstdint>

extern "C" void raylib_init_window(std::intptr_t* w, std::intptr_t* h, void* r) {
  InitWindow(*w, *h, "Demo");
}

extern "C" void raylib_window_should_close(bool* result) {
  *result = WindowShouldClose();
}
