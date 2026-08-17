#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/// Opens the test case file for reading, returning the file handle,
/// or 0 if opening failed.
void hylo_open_test_cases_file_for_reading_indirect(FILE** result) {
  *result = fopen("test-cases.txt", "r");
}

/// Reads a test case from `f` into `s` representing the sizes of
/// members, `a` representing their alignments, `o` representing
/// their expected offsets, and `e` representing the expected size and
/// alignment of the record, returning the number of significant
/// elements of each of those arrays.
///
/// If there are no more test cases (the sentinel value -1 is
/// reached in the input), returns -1.
///
/// If errors occur, returns a negative value indicating how far along
/// the call got.
void hylo_read_test_case_indirect(
    FILE **f, intptr_t s[10],
    intptr_t a[10], intptr_t o[10], intptr_t e[2], intptr_t *result) {
  /// Try to read the first [size] field of the test case.
  int scan0 = fscanf(*f, "%td", &s[0]);

  // A leading `-1` indicates the end of input.
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

  /// [size] [alignment] of all 10 fields (except the first member's size that's already read)
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

  /// [expected offset] of each member
  int scan2 =
      fscanf(*f, "%td %td %td %td %td %td %td %td %td %td", &o[0], &o[1], &o[2],
             &o[3], &o[4], &o[5], &o[6], &o[7], &o[8], &o[9]);
  if (scan2 == 0 || scan2 == EOF) {
    *result = -5;
    return;
  }

  // [expected size] [expected alignment]
  int scan3 = fscanf(*f, "%td %td", &e[0], &e[1]);
  if (scan3 == 0 || scan3 == EOF) {
    *result = -9;
    return;
  }

  *result = 0;
  for (int i = 0; i < 10 && a[i] != 0; i++) {
    ++*result;
  }
}
