
#include "cvc5/c/cvc5.h"
#include <stdio.h>

void Anima_deduction_scratch() {
  Cvc5TermManager *tm = cvc5_term_manager_new();
  Cvc5 *slv = cvc5_new(tm);

  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_option(slv, "finite-model-find", "true");

  Cvc5Sort animaSort = cvc5_mk_uninterpreted_sort(tm, "Anima");

  Cvc5Sort anima_fun_sorts[1] = {animaSort};
  Cvc5Sort animaPredicate = cvc5_mk_fun_sort(tm, 1, anima_fun_sorts, cvc5_get_boolean_sort(tm));
  Cvc5Sort directionSort = cvc5_mk_uninterpreted_sort(tm, "Direction");

  Cvc5Sort fun_sorts[2] = {animaSort, directionSort};
  Cvc5Sort facingSort = cvc5_mk_fun_sort(tm, 2, fun_sorts, cvc5_get_boolean_sort(tm));

  Cvc5Term facingFn = cvc5_mk_const(tm, facingSort, "Facing");
  Cvc5Term blinky = cvc5_mk_const(tm, animaSort, "blinky");

  Cvc5Term up = cvc5_mk_const(tm, directionSort, "up");
  Cvc5Term right = cvc5_mk_const(tm, directionSort, "right");
  Cvc5Term down = cvc5_mk_const(tm, directionSort, "down");
  Cvc5Term left = cvc5_mk_const(tm, directionSort, "left");

  Cvc5Term direction_children[3] = {facingFn, blinky, up};
  Cvc5Term bu = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, direction_children);

  direction_children[2] = right;
  Cvc5Term br = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, direction_children);

  direction_children[2] = down;
  Cvc5Term bd = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, direction_children);

  direction_children[2] = left;
  Cvc5Term bl = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, direction_children);

  Cvc5Term burd_children[3] = {bu, br, bd};
  Cvc5Term burd = cvc5_mk_term(tm, CVC5_KIND_OR, 3, burd_children);

  Cvc5Term budl_children[3] = {bu, bd, bl};
  Cvc5Term budl = cvc5_mk_term(tm, CVC5_KIND_OR, 3, budl_children);

  Cvc5Term burl_children[3] = {bu, br, bl};
  Cvc5Term burl = cvc5_mk_term(tm, CVC5_KIND_OR, 3, burl_children);

  Cvc5Term brdl_children[3] = {br, bd, bl};
  Cvc5Term brdl = cvc5_mk_term(tm, CVC5_KIND_OR, 3, brdl_children);

  Cvc5Term some_direction_children[4] = {bu, br, bd, bl};
  Cvc5Term some_direction = cvc5_mk_term(tm, CVC5_KIND_XOR, 4, some_direction_children);

  Cvc5Term not_up_children[1] = {bu};
  Cvc5Term not_up = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, not_up_children);

  cvc5_assert_formula(slv, some_direction);
  cvc5_assert_formula(slv, not_up);

  cvc5_check_sat(slv);

  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, bu)));
  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, br)));
  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, bd)));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, bl)));
}
