#ifndef TYPE
#error Generic header requires defined TYPE
#else

#ifndef ALIAS
#define ALIAS TYPE
#endif

#define _CAT(A, B) A##_##B
#define CAT(A, B) _CAT(A, B)

TYPE CAT(ALIAS, max)(TYPE x, TYPE y);

TYPE CAT(ALIAS, min)(TYPE x, TYPE y);

#ifdef ARITHMETIC_IMPLEMENTATION

TYPE CAT(ALIAS, max)(TYPE x, TYPE y) {
  return x >= y ? x : y;
}

TYPE CAT(ALIAS, min)(TYPE x, TYPE y) {
  return x <= y ? x : y;
}

#endif

#undef CAT
#undef _CAT
#undef ALIAS
#undef TYPE
#endif
