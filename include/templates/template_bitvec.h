#ifndef TYPE
#error Bitvec template requires defined TYPE
#else

#ifndef ALIAS
#define ALIAS TYPE
#endif

#define _CAT(A, B) A##_##B
#define CAT(A, B) _CAT(A, B)

TYPE CAT(ALIAS, rotl1)(TYPE vec);

TYPE CAT(ALIAS, rotr1)(TYPE vec);

TYPE CAT(ALIAS, rotl)(TYPE vec, size_t bits);

TYPE CAT(ALIAS, rotr)(TYPE vec, size_t bits);

#ifdef BITVEC_IMPLEMENTATION

constexpr TYPE CAT(ALIAS, bitsize) = (sizeof(TYPE) * 8);

constexpr TYPE CAT(ALIAS, bitsize_minus_one) = (sizeof(TYPE) * 8) - 1;

TYPE CAT(ALIAS, rotl1)(TYPE vec) { return (vec << 1) | (vec >> CAT(ALIAS, bitsize_minus_one)); }

TYPE CAT(ALIAS, rotr1)(TYPE vec) { return (vec >> 1) | (vec << CAT(ALIAS, bitsize_minus_one)); }

TYPE CAT(ALIAS, rotl)(TYPE vec, size_t bits) { return (vec << bits) | (vec >> (CAT(ALIAS, bitsize) - bits)); }

TYPE CAT(ALIAS, rotr)(TYPE vec, size_t bits) { return (vec >> bits) | (vec << (CAT(ALIAS, bitsize) - bits)); }

#endif

#undef CAT
#undef _CAT
#undef ALIAS
#undef TYPE
#endif
