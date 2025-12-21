#pragma once

#include <stdio.h>
#include <stdlib.h>

static inline void pause_panic() {
  printf("Panic!\n");
  getchar();
  exit(1);
  return;
}
