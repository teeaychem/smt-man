#pragma once

#include "SML/logic/situation.h"
#include "SML/sprite/anima.h"

void Sync_update_animas(const Situation *situation, Anima *animas);

void Sync_update_situation(Situation *situation, const Anima *animas);
