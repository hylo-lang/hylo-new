#include "raylib.h"
#include <stdio.h>

void exposed(void* result) {
    printf("Hello from shim!");
}