
#include "anima.h"
#include "logic.h"
#include <stdio.h>

void Anima_deduction_known(Anima *self) {

  Cvc5Term some_direction = cvc5_mk_term(l_tm, CVC5_KIND_XOR, 4, (Cvc5Term[4]){
                                                                     self->terms.facing_u,
                                                                     self->terms.facing_r,
                                                                     self->terms.facing_d,
                                                                     self->terms.facing_l,
                                                                 });



  cvc5_assert_formula(self->mind, some_direction);

}
