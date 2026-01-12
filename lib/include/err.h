#pragma once

enum result_e {
  RESULT_OK,
  RESULT_KO,
};
typedef enum result_e Result;

#define ENSURE(result_)         \
  {                             \
    if (result_ != RESULT_OK) { \
      exit(1);                  \
    }                           \
  }
