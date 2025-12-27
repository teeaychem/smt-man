#include <stdatomic.h>
#include <stdlib.h>

#include "logic.h"
#include "lyf/anima/mind.h"
#include "random.h"

void Mind_default(Mind *mind, uint8_t id, Pair_uint8 location, Direction direction) {

  mind->id = id;

  atomic_init(&mind->view.anima[id].intent, direction);
  atomic_init(&mind->view.anima[id].momentum, direction);

  atomic_init(&mind->view.anima[id].location, location);

  atomic_init(&mind->view.anima[id].status, ANIMA_STATUS_SEARCH);

  atomic_init(&mind->view.anima[id].velocity, 1);
}

void Mind_touch(Mind *self) {
  assert(self != nullptr);

  Lang_base_setup(&self->lang, self->ctx);
  Lang_path_setup(&self->lang, self->ctx);
  Lang_anima_setup(&self->lang, self->ctx);
  Lang_facing_setup(&self->lang, self->ctx);
}

// deduction

void Mind_deduct(Mind *self) {

  Z3_ast anima_ast = Z3_mk_app(self->ctx, self->lang.anima.enum_consts[self->id], 0, 0);
  auto anima_is_facing = Z3_mk_app(self->ctx, self->lang.anima.is_facing, 1, (Z3_ast[1]){anima_ast});

  auto up = Z3_mk_app(self->ctx, self->lang.direction.enum_consts[0], 0, 0);
  auto rt = Z3_mk_app(self->ctx, self->lang.direction.enum_consts[1], 0, 0);
  auto dn = Z3_mk_app(self->ctx, self->lang.direction.enum_consts[2], 0, 0);
  auto lt = Z3_mk_app(self->ctx, self->lang.direction.enum_consts[3], 0, 0);

  auto facing_up = Z3_mk_eq(self->ctx, anima_is_facing, up);
  auto facing_rt = Z3_mk_eq(self->ctx, anima_is_facing, rt);
  auto facing_dn = Z3_mk_eq(self->ctx, anima_is_facing, dn);
  auto facing_lt = Z3_mk_eq(self->ctx, anima_is_facing, lt);

  Z3_optimize_push(self->ctx, self->solver);

  int tmp_direction = random_in_range(1, 4);

  switch (tmp_direction) {
  case 1: {
    auto rt_dn_lt = Z3_mk_or(self->ctx, 3, (Z3_ast[3]){facing_rt, facing_dn, facing_lt});
    auto not_rt_dn_lt = Z3_mk_not(self->ctx, rt_dn_lt);
    Z3_optimize_assert(self->ctx, self->solver, not_rt_dn_lt);
  } break;

  case 2: {
    auto up_dn_lt = Z3_mk_or(self->ctx, 3, (Z3_ast[3]){facing_up, facing_dn, facing_lt});
    auto not_up_dn_lt = Z3_mk_not(self->ctx, up_dn_lt);
    Z3_optimize_assert(self->ctx, self->solver, not_up_dn_lt);
  } break;

  case 3: {
    auto up_rt_lt = Z3_mk_or(self->ctx, 3, (Z3_ast[3]){facing_up, facing_rt, facing_lt});
    auto not_up_rt_lt = Z3_mk_not(self->ctx, up_rt_lt);
    Z3_optimize_assert(self->ctx, self->solver, not_up_rt_lt);

  } break;

  case 4: {
    auto up_rt_dn = Z3_mk_or(self->ctx, 3, (Z3_ast[3]){facing_up, facing_rt, facing_dn});
    auto not_up_rt_dn = Z3_mk_not(self->ctx, up_rt_dn);
    Z3_optimize_assert(self->ctx, self->solver, not_up_rt_dn);

  } break;
  }

  switch (Z3_optimize_check(self->ctx, self->solver, 0, nullptr)) {
  case Z3_L_TRUE: {
  } break;
  default: {
    g_log(nullptr, G_LOG_LEVEL_CRITICAL, "UNSAT deduction %d", self->id);
    exit(-3);
  } break;
  }

  auto model = Z3_optimize_get_model(self->ctx, self->solver);
  Z3_model_inc_ref(self->ctx, model);

  Z3_ast anima_direction = nullptr;
  Z3_model_eval(self->ctx, model, Z3_mk_app(self->ctx, self->lang.anima.is_facing, 1, &anima_ast), false, &anima_direction);

  if (anima_direction == up) {
    atomic_store(&self->view.anima[self->id].intent, NORTH);
  } else if (anima_direction == rt) {
    atomic_store(&self->view.anima[self->id].intent, EAST);

  } else if (anima_direction == dn) {
    atomic_store(&self->view.anima[self->id].intent, SOUTH);

  } else if (anima_direction == lt) {
    atomic_store(&self->view.anima[self->id].intent, WEST);
  } else {
    g_log(nullptr, G_LOG_LEVEL_WARNING, "No direction");
    exit(-1);
  }

  Z3_model_dec_ref(self->ctx, model);
  Z3_optimize_pop(self->ctx, self->solver);
}
