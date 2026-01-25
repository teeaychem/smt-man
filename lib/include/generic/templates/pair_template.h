#ifndef TYPE
#error Generic header requires defined TYPE
#else

#ifndef SUFFIX
#define SUFFIX TYPE
#endif

#include <slog.h>
#include <stddef.h>

#define _CAT(A, B) A##_##B
#define CAT(A, B) _CAT(A, B)

#define S_TYPE CAT(Pair, SUFFIX)

typedef struct {
  TYPE x;
  TYPE y;
} S_TYPE;

S_TYPE CAT(S_TYPE, create)(const TYPE x, const TYPE y);

size_t CAT(S_TYPE, flatten)(const S_TYPE *self, const TYPE x, const TYPE y);

S_TYPE CAT(S_TYPE, scale)(const S_TYPE *self, const TYPE factor);

S_TYPE CAT(S_TYPE, abstract_by)(const S_TYPE *self, const TYPE interval);

#ifdef PAIR_IMPLEMENTATION

#include <assert.h>

S_TYPE CAT(S_TYPE, create)(const TYPE x, const TYPE y) {
  return (S_TYPE){.x = x, .y = y};
}

size_t CAT(S_TYPE, flatten)(const S_TYPE *self, const TYPE x, const TYPE y) {
  if (!(x < self->x && y < self->y)) {
    slog_display(SLOG_ERROR, 0, "Invalid x: %d !< %d\n", x, self->x);
    slog_display(SLOG_ERROR, 0, "Invalid y: %d !< %d\n", y, self->y);
    assert(false);
  };

  return ((size_t)x * self->y) + (size_t)y;
}

S_TYPE CAT(S_TYPE, scale)(const S_TYPE *self, const TYPE factor) {
  return (S_TYPE){
      .x = (self->x * factor),
      .y = (self->y * factor)};
}

S_TYPE CAT(S_TYPE, abstract_by)(const S_TYPE *self, const TYPE interval) {
  return (S_TYPE){
      .x = (self->x / interval),
      .y = (self->y / interval)};
}

#endif

#undef S_TYPE
#undef CAT
#undef _CAT
#undef SUFFIX
#undef TYPE
#endif
