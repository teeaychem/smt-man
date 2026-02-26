#pragma once

// #include <stdio.h>
#include <stdlib.h>

#include "slog.h"

enum result_e {
  RESULT_OK,
  RESULT_KO,
};
typedef enum result_e Result;

static inline void ensure(bool result_) {
  if (result_ != RESULT_OK) {
    /* printf("Pausing on panic...\n"); \ */
    /* getc(stdin);                     \ */
    exit(1);
  }
}

static inline void panic(bool condition, const char *msg, int code) {
  if (condition) {
    slog_error(msg);
    exit(code);
  }
}
