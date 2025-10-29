#include "cvc5/c/cvc5.h"
#include "logic.h"



Cvc5TermManager *l_tm;
struct language_t llang;

void setup_logic() {
  l_tm = cvc5_term_manager_new();

  llang.sorts.anima = cvc5_mk_uninterpreted_sort(l_tm, "Anima");
  llang.sorts.direction = cvc5_mk_uninterpreted_sort(l_tm, "Direction");

  llang.sorts.is_anima = cvc5_mk_fun_sort(l_tm, 1, (Cvc5Sort[1]){llang.sorts.anima}, cvc5_get_boolean_sort(l_tm));

  llang.sorts.is_anima_facing = cvc5_mk_fun_sort(l_tm, 2, (Cvc5Sort[2]){llang.sorts.anima, llang.sorts.direction}, cvc5_get_boolean_sort(l_tm));
}
