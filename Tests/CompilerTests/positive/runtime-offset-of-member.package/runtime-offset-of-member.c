#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void hylo_open_test_cases_file_for_reading_indirect(FILE** result) {
  *result = fopen("test-cases.txt", "r");
}

/*
void hylo_print_Int_indirect(intptr_t *x) {
  printf("%td\n", *x);
  fflush(stdout);
}
*/

void hylo_read_test_case_indirect(
    FILE **f, intptr_t s[10],
    intptr_t a[10], intptr_t o[10], intptr_t *result) {
  int scan0 = fscanf(*f, "%td", &s[0]);
  if (scan0 != 0 && s[0] == -1) {
    // Normal termination
    *result = -1;
    return;
  }
  if (scan0 == 0 || scan0 == EOF) {
    *result = -2;
    return;
  }
  if (s[0] < 0 && s[0] != -1) {
    *result = -3;
    return;
  }
  int scan1 = fscanf(*f,
                     "%td   %td %td   %td %td   %td %td   %td %td   %td %td   "
                     "%td %td   %td %td   %td %td   %td %td",
                     &a[0], &s[1], &a[1], &s[2], &a[2], &s[3], &a[3], &s[4],
                     &a[4], &s[5], &a[5], &s[6], &a[6], &s[7], &a[7], &s[8],
                     &a[8], &s[9], &a[9]);
  if (scan1 == 0 || scan1 == EOF) {
    *result = -4;
    return;
  }

  int scan2 =
      fscanf(*f, "%td %td %td %td %td %td %td %td %td %td", &o[0], &o[1], &o[2],
             &o[3], &o[4], &o[5], &o[6], &o[7], &o[8], &o[9]);
  if (scan2 == 0 || scan2 == EOF) {
    *result = -5;
    return;
  }

  *result = 0;
  for (int i = 0; i < 10 && a[i] != 0; i++) {
    ++*result;
  }
}

void hylo_close_file_indirect(void* result, FILE** f) {
  fclose(*f);
}


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
