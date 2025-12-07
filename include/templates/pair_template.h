#ifndef TYPE
#error Generic header requires defined TYPE
#else

#ifndef SUFFIX
#define SUFFIX TYPE
#endif

#define _CAT(A, B) A##_##B
#define CAT(A, B) _CAT(A, B)

#define S_TYPE CAT(Pair, SUFFIX)

typedef struct {
  TYPE x;
  TYPE y;
} S_TYPE;

S_TYPE CAT(S_TYPE, create)(TYPE x, TYPE y);

TYPE CAT(S_TYPE, area)(const S_TYPE *self);

S_TYPE CAT(S_TYPE, scale)(const S_TYPE *self, const TYPE factor);

S_TYPE CAT(S_TYPE, abstract_by)(const S_TYPE *self, const TYPE interval);

#ifdef PAIR_IMPLEMENTATION

S_TYPE CAT(S_TYPE, create)(TYPE x, TYPE y) {
  return (S_TYPE){.x = x, .y = y};
}

TYPE CAT(S_TYPE, area)(const S_TYPE *self) {
  return self->x * self->y;
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
