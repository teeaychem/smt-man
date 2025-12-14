#include <stdatomic.h>
#include <stdlib.h>

#include "anima.h"
#include "logic.h"

void Mind_default(Mind *mind) {

  Z3_context ctx = z3_mk_anima_ctx();
  Z3_optimize optimizer = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, optimizer);

  *mind = (Mind){
      .ctx = ctx,
      .solver = optimizer,
      .lang = {},
  };
}

void Anima_touch(Anima *self, Mind *mind) {
  assert(self != nullptr);

  Lang_base_setup(&mind->lang, mind->ctx);
  Lang_path_setup(&mind->lang, mind->ctx);
  Lang_anima_setup(&mind->lang, mind->ctx);
  Lang_facing_setup(&mind->lang, mind->ctx);
}

// deduction

void Anima_deduct(Anima *self, Mind *mind) {
  Z3_ast anima_ast = Z3_mk_app(mind->ctx, mind->lang.anima.enum_consts[self->id], 0, 0);
  auto anima_is_facing = Z3_mk_app(mind->ctx, mind->lang.anima.is_facing, 1, (Z3_ast[1]){anima_ast});

  auto up = Z3_mk_app(mind->ctx, mind->lang.direction.enum_consts[0], 0, 0);
  auto rt = Z3_mk_app(mind->ctx, mind->lang.direction.enum_consts[1], 0, 0);
  auto dn = Z3_mk_app(mind->ctx, mind->lang.direction.enum_consts[2], 0, 0);
  auto lt = Z3_mk_app(mind->ctx, mind->lang.direction.enum_consts[3], 0, 0);

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

  switch (Z3_optimize_check(mind->ctx, mind->solver, 0, nullptr)) {
  case Z3_L_TRUE: {
  } break;
  default: {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "UNSAT deduction %d", self->id);
    exit(-3);
  } break;
  }

  auto model = Z3_optimize_get_model(mind->ctx, mind->solver);
  Z3_model_inc_ref(mind->ctx, model);

  Z3_ast anima_direction = nullptr;
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
    g_log(nullptr, G_LOG_LEVEL_WARNING, "No direction");
    exit(-1);
  }

  Z3_model_dec_ref(mind->ctx, model);
  Z3_optimize_pop(mind->ctx, mind->solver);
}
