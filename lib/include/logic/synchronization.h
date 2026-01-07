#pragma once

#include "constants.h"
#include "logic/situation.h"
#include "sprites/anima.h"

void Sync_update_animas(const Situation *situation, Anima animas[ANIMA_COUNT]);

void Sync_update_situation(Situation *situation, const Anima animas[ANIMA_COUNT]);
