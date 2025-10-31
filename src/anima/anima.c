#include "anima.h"
#include "cvc5/c/cvc5.h"
#include "logic.h"
#include "maze.h"
#include "sprite.h"
#include "utils.h"
#include "utils/pairs.h"
#include <stdio.h>

Anima Anima_default(char *name, Sprite sprite) {
  return Anima_create(name, PairI32_create(1, 1), DOWN, DOWN, sprite);
}

Anima Anima_create(char *name, PairI32 pos, Direction intent, Direction momentum, Sprite sprite) {
  Anima self = {.name = name,
                .pos = pos,
                .intent = intent,
                .momentum = momentum,
                .mVel = 2,
                .sprite = sprite,
                .mind = cvc5_mind_default()};

  self.term = cvc5_mk_const(l_tm, llang.sorts.anima, self.name);

  self.terms.facing_u = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){llang.pFacing, self.term, llang.direction.up});
  self.terms.facing_r = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){llang.pFacing, self.term, llang.direction.right});
  self.terms.facing_d = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){llang.pFacing, self.term, llang.direction.down});
  self.terms.facing_l = cvc5_mk_term(l_tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[3]){llang.pFacing, self.term, llang.direction.left});

  self.sprite.pos = PairI32_create(self.pos.x * sprite.size.x, self.pos.y * sprite.size.y);

  return self;
}

void Anima_destory(Anima *self) {
  Sprite_destroy(&self->sprite);
}

void Anima_handle_event(Anima *self, SDL_Event *event) {

  if (event->type == SDL_EVENT_KEY_DOWN && !event->key.repeat) {

    switch (event->key.key) {
    case SDLK_UP:
      self->intent = UP;
      break;
    case SDLK_DOWN:
      self->intent = DOWN;
      break;
    case SDLK_LEFT:
      self->intent = LEFT;
      break;
    case SDLK_RIGHT:
      self->intent = RIGHT;
      break;
    }
  }
}

void Anima_move_within(Anima *self, Maze *maze) {

  if (self->sprite.pos.x % self->sprite.size.x == 0 && self->sprite.pos.y % self->sprite.size.y == 0) {
    self->pos.x = self->sprite.pos.x / 16;
    self->pos.y = self->sprite.pos.y / 16;

    self->momentum = self->intent;

    PairI32 destination;

    steps_in_direction(&self->pos, self->momentum, 1, &destination);

    if (Maze_is_open(maze, &destination)) {
      self->mVel = 1;
    } else {
      self->mVel = 0;
    }
  }

  switch (self->momentum) {
  case UP: {
    self->sprite.pos.y -= self->mVel;
  } break;
  case RIGHT: {
    self->sprite.pos.x += self->mVel;
  } break;
  case DOWN: {
    self->sprite.pos.y += self->mVel;
  } break;
  case LEFT: {
    self->sprite.pos.x -= self->mVel;
  } break;
  }
}

void Anima_deduct(Anima *self) {

  cvc5_push(self->mind, 1);

  int tmp_direction = random_in_range(1, 4);

  switch (tmp_direction) {
  case 1: {
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_r}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_d}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_l}));
  } break;

  case 2: {
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_u}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_d}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_l}));
  } break;

  case 3: {
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_u}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_r}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_l}));
  } break;

  case 4: {
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_u}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_r}));
    cvc5_assert_formula(self->mind, cvc5_mk_term(l_tm, CVC5_KIND_NOT, 1, (Cvc5Term[1]){self->terms.facing_d}));
  } break;
  }

  cvc5_check_sat(self->mind);

  if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_u))) {
    self->intent = UP;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_r))) {
    self->intent = RIGHT;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_d))) {
    self->intent = DOWN;

  } else if (cvc5_term_get_boolean_value(cvc5_get_value(self->mind, self->terms.facing_l))) {
    self->intent = LEFT;
  }

  cvc5_pop(self->mind, 1);
};
