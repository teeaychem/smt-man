#pragma once

#include <stddef.h>

#include "generic/enums.h"
#include "generic/pairs.h"

#include "SML/logic/enums.h"

struct situation_t {

  struct {
    // The count of animas
    size_t count;
    // At least `count` state structs for each anima
    struct anima_state_t {
      // The (actual) direction of an anima
      _Atomic(cardinal_e) direction_actual;
      // The location of an anima
      _Atomic(Pair_uint8) location;
      // The movement pattern of an anima
      _Atomic(uint32_t) movement_pattern;
      // The status of an anima
      _Atomic(anima_status_e) status;
    } *data;
  } animas;

  //
  struct persona_state_t {
    // The (actual) direction of the persona
    _Atomic(cardinal_e) direction_actual;
    // The location of the persona
    _Atomic(Pair_uint8) location;
    // The movement pattern of the persona
    _Atomic(uint32_t) movement_pattern;
  } persona;
};
typedef struct situation_t situation_s;

// Methods

void situation_ctor(situation_s *self, size_t anima_count);

void situation_dtor(situation_s *self);

void situation_reset(situation_s *self);

void situation_copy(const situation_s *src, situation_s *dst);

void situation_copy_anima(const situation_s *src, situation_s *dst, uint8_t idx);
