#pragma once

#include "SML/logic/situation.h"
#include "SML/sprite/anima.h"

void Sync_update_animas(const Situation *situation, anima_s *animas);

void Sync_update_situation(Situation *situation, const anima_s *animas);

void sync_situation_to_situation(const Situation *from, Situation *to);
