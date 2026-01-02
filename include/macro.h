#pragma once

#include "enums.h"

#define ARRAY_LEN(array_) (sizeof(array_) / sizeof((array_)[0]))

#define TRIP(result_)          \
  {                            \
    Result result = result_;   \
    if (result != RESULT_OK) { \
      return result;           \
    }                          \
  }

#define PANIC(result_)         \
  {                            \
    Result result = result_;   \
    if (result != RESULT_OK) { \
      exit(1);                 \
    }                          \
  }
