#pragma once

#include <stdint.h>

#define TYPE uint32_t
#define SUFFIX uint32
#include "templates/pair_template.h"
#undef SUFFIX
#undef TYPE

#define TYPE uint8_t
#define SUFFIX uint8
#include "templates/pair_template.h"
#undef SUFFIX
#undef TYPE
