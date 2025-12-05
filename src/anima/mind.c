#include "anima.h"
#include "constants.h"
#include "logic.h"
#include "stdatomic.h"
#include "z3.h"

#include <stdlib.h>

Mind Mind_default() {

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  Mind mind = {
      .ctx = ctx,
      .solver = optimizer,
      .lang = {},
      .lot = {},
  };

  return mind;
}

/* void Anima_LoT_facing(Anima *self, Mind *mind) { */
/*   char smt_input_buffer[SMT_INPUT_BUFFER_SIZE]; */
/*   const char *smt_error_msg; */

/*   for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) { */

/*     snprintf(smt_input_buffer, SMT_INPUT_BUFFER_SIZE, "(anima_is_facing %s up)", self->name); */
/*     cvc5_parser_set_str_input(mind->parser, CVC5_LANG, smt_input_buffer, ""); */
/*     mind->lot.anima[idx].facing.up = cvc5_parser_next_term(mind->parser, &smt_error_msg); */

/*     snprintf(smt_input_buffer, SMT_INPUT_BUFFER_SIZE, "(anima_is_facing %s right)", self->name); */
/*     cvc5_parser_set_str_input(mind->parser, CVC5_LANG, smt_input_buffer, ""); */
/*     mind->lot.anima[idx].facing.right = cvc5_parser_next_term(mind->parser, &smt_error_msg); */

/*     snprintf(smt_input_buffer, SMT_INPUT_BUFFER_SIZE, "(anima_is_facing %s down)", self->name); */
/*     cvc5_parser_set_str_input(mind->parser, CVC5_LANG, smt_input_buffer, ""); */
/*     mind->lot.anima[idx].facing.down = cvc5_parser_next_term(mind->parser, &smt_error_msg); */

/*     snprintf(smt_input_buffer, SMT_INPUT_BUFFER_SIZE, "(anima_is_facing %s left)", self->name); */
/*     cvc5_parser_set_str_input(mind->parser, CVC5_LANG, smt_input_buffer, ""); */
/*     mind->lot.anima[idx].facing.left = cvc5_parser_next_term(mind->parser, &smt_error_msg); */
/*   } */
/* } */

/* void Anima_LoT_animas(Anima *self, Mind *mind) { */

/*   char smt_input_buffer[SMT_INPUT_BUFFER_SIZE]; */
/*   Cvc5Command smt_cmd; */
/*   const char *smt_error_msg; */

/*   cvc5_parser_set_str_input( */
/*       mind->parser, */
/*       CVC5_LANG, */
/*       "(declare-sort Anima 0)" */
/*       "(declare-const anima Anima)", */
/*       "animas"); */
/*   do { */
/*     smt_cmd = cvc5_parser_next_command(mind->parser, &smt_error_msg); */
/*     if (smt_error_msg) { */
/*       printf("%s", smt_error_msg), exit(-1); */
/*     } */
/*     if (smt_cmd) { */
/*       cvc5_cmd_invoke(smt_cmd, mind->solver, mind->sm); */
/*     } */
/*   } while (smt_cmd); */

/*   for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) { */
/*     snprintf(smt_input_buffer, SMT_INPUT_BUFFER_SIZE, "(declare-const %s Anima)", ANIMA_NAMES[idx]); */
/*     cvc5_parser_set_str_input(mind->parser, CVC5_LANG, smt_input_buffer, ""); */
/*     cvc5_cmd_invoke(cvc5_parser_next_command(mind->parser, &smt_error_msg), mind->solver, mind->sm); */
/*   } */
/* } */

/* void Anima_LoT_direction(Anima *self, Mind *mind) { */

/*   Cvc5Command smt_cmd; */
/*   const char *smt_error_msg; */

/*   cvc5_parser_set_str_input( */
/*       mind->parser, */
/*       CVC5_LANG, */
/*       "(declare-sort Direction 0)" */

/*       "(declare-const up    Direction)" */
/*       "(declare-const right Direction)" */
/*       "(declare-const down  Direction)" */
/*       "(declare-const left  Direction)" */

/*       "(declare-fun anima_is_facing (Anima Direction) Bool)" */

/*       "(assert (distinct up right down left))" */
/*       "(assert (forall ((anima Anima)) (xor (anima_is_facing anima up) (xor (anima_is_facing anima right) (xor (anima_is_facing anima down) (anima_is_facing anima left))))))", */
/*       "anima_innate"); */
/*   do { */
/*     smt_cmd = cvc5_parser_next_command(mind->parser, &smt_error_msg); */
/*     if (smt_error_msg) { */
/*       printf("%s", smt_error_msg), exit(-1); */
/*     } */
/*     if (smt_cmd) { */
/*       cvc5_cmd_invoke(smt_cmd, mind->solver, mind->sm); */
/*     } */
/*   } while (smt_cmd); */
/* } */

void Anima_touch(Anima *self, Mind *mind) {

  mind->lang.u8_sort = Z3_mk_bv_sort(mind->ctx, 8);
  Lang_path_setup(&mind->lang, mind->ctx);
  Lang_anima_setup(&mind->lang, mind->ctx);
  Lang_anima_facing_setup(&mind->lang, mind->ctx);

  /* Anima_LoT_animas(self, mind); */
  /* Anima_LoT_direction(self, mind); */
  /* Anima_LoT_facing(self, mind); */
};

// deduction

void Anima_deduct(Anima *self, Mind *mind) {
  Z3_ast anima_ast = Z3_mk_app(mind->ctx, mind->lang.anima.enum_consts[self->id], 0, 0);
  auto anima_is_facing = Z3_mk_app(mind->ctx, mind->lang.anima.is_facing, 1, (Z3_ast[1]){anima_ast});

  auto up = Z3_mk_app(mind->ctx, mind->lang.anima.facing.enum_consts[0], 0, 0);
  auto rt = Z3_mk_app(mind->ctx, mind->lang.anima.facing.enum_consts[1], 0, 0);
  auto dn = Z3_mk_app(mind->ctx, mind->lang.anima.facing.enum_consts[2], 0, 0);
  auto lt = Z3_mk_app(mind->ctx, mind->lang.anima.facing.enum_consts[3], 0, 0);

  auto facing_up = Z3_mk_eq(mind->ctx, anima_is_facing, up);
  auto facing_rt = Z3_mk_eq(mind->ctx, anima_is_facing, rt);
  auto facing_dn = Z3_mk_eq(mind->ctx, anima_is_facing, dn);
  auto facing_lt = Z3_mk_eq(mind->ctx, anima_is_facing, lt);

  Z3_optimize_push(mind->ctx, mind->solver);

  int tmp_direction = random_in_range(1, 4);

  switch (tmp_direction) {
  case 1: {
    auto rt_dn_lt = Z3_mk_or(mind->ctx, 3, (Z3_ast[3]){facing_rt, facing_dn, facing_lt});
    auto not_rt_dn_lt = Z3_mk_not(mind->ctx, rt_dn_lt);
    Z3_optimize_assert(mind->ctx, mind->solver, not_rt_dn_lt);
  } break;

  case 2: {
    auto up_dn_lt = Z3_mk_or(mind->ctx, 3, (Z3_ast[3]){facing_up, facing_dn, facing_lt});
    auto not_up_dn_lt = Z3_mk_not(mind->ctx, up_dn_lt);
    Z3_optimize_assert(mind->ctx, mind->solver, not_up_dn_lt);
  } break;

  case 3: {
    auto up_rt_lt = Z3_mk_or(mind->ctx, 3, (Z3_ast[3]){facing_up, facing_rt, facing_lt});
    auto not_up_rt_lt = Z3_mk_not(mind->ctx, up_rt_lt);
    Z3_optimize_assert(mind->ctx, mind->solver, not_up_rt_lt);

  } break;

  case 4: {
    auto up_rt_dn = Z3_mk_or(mind->ctx, 3, (Z3_ast[3]){facing_up, facing_rt, facing_dn});
    auto not_up_rt_dn = Z3_mk_not(mind->ctx, up_rt_dn);
    Z3_optimize_assert(mind->ctx, mind->solver, not_up_rt_dn);

  } break;
  }

  switch (Z3_optimize_check(mind->ctx, mind->solver, 0, NULL)) {
  case Z3_L_TRUE: {
  } break;
  default: {
    printf("UNSAT deduction %d\n", self->id);
    exit(-3);
  } break;
  }

  auto model = Z3_optimize_get_model(mind->ctx, mind->solver);
  Z3_model_inc_ref(mind->ctx, model);

  Z3_ast anima_direction = NULL;
  Z3_model_eval(mind->ctx, model, Z3_mk_app(mind->ctx, mind->lang.anima.is_facing, 1, &anima_ast), false, &anima_direction);

  if (anima_direction == up) {
    atomic_store(&self->pov.anima[self->id].intent, UP);
  } else if (anima_direction == rt) {
    atomic_store(&self->pov.anima[self->id].intent, RIGHT);

  } else if (anima_direction == dn) {
    atomic_store(&self->pov.anima[self->id].intent, DOWN);

  } else if (anima_direction == lt) {
    atomic_store(&self->pov.anima[self->id].intent, LEFT);
  } else {
    printf("No direction"), exit(-1);
  }

  Z3_model_dec_ref(mind->ctx, model);
  Z3_optimize_pop(mind->ctx, mind->solver);
};
