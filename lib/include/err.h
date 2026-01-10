#pragma once

enum result_e {
  RESULT_OK,
  RESULT_KO,
};
typedef enum result_e Result;

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
