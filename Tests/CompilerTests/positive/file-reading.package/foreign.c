#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

/// Reads an integer from a file named "input.txt" and stores it in the provided pointer.
///
/// Stores -1 in `result` on failure.
void hylo_read_int_from_file_indirect(intptr_t* result)  {
  FILE* file = fopen("input.txt", "r");
  if (file) {
    if (fscanf(file, "%" PRIdPTR, result) != 1) {
      *result = -1;
    }
    fclose(file);
  } else {
    *result = -1;
  }
}