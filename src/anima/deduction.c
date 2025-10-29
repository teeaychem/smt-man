
#include "logic.h"
#include <stdio.h>

void Anima_deduction_scratch() {

  Cvc5 *slv = cvc5_new(l_tm);

  cvc5_set_option(slv, "produce-models", "true");
  cvc5_set_option(slv, "finite-model-find", "true");

  Cvc5Term facingFn = cvc5_mk_const(l_tm, llang.sorts.is_anima_facing, "Facing");
  Cvc5Term blinky = cvc5_mk_const(l_tm, llang.sorts.anima, "blinky");

  Cvc5Term up = cvc5_mk_const(l_tm, llang.sorts.direction, "up");
  Cvc5Term right = cvc5_mk_const(l_tm, llang.sorts.direction, "right");
  Cvc5Term down = cvc5_mk_const(l_tm, llang.sorts.direction, "down");
  Cvc5Term left = cvc5_mk_const(l_tm, llang.sorts.direction, "left");

  Cvc5Term bu = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){facingFn, blinky, up});

  Cvc5Term br = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){facingFn, blinky, right});

  Cvc5Term bd = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){facingFn, blinky, down});

  Cvc5Term bl = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){facingFn, blinky, left});

  Cvc5Term some_direction = cvc5_mk_term(l_tm, CVC5_KIND_XOR, 4, (Cvc5Term[4]){bu, br, bd, bl});

  Cvc5Term not_up = cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){bu});

  cvc5_assert_formula(slv, some_direction);
  cvc5_assert_formula(slv, not_up);

  cvc5_check_sat(slv);

  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, bu)));
  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, br)));
  printf("%s ", cvc5_term_to_string(cvc5_get_value(slv, bd)));
  printf("%s\n", cvc5_term_to_string(cvc5_get_value(slv, bl)));
}
