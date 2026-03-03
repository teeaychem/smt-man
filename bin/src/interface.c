#include "interface.h"
#include "cwalk.h"

void interface_ctor(interface_s *self, const state_s *core_logic, const char *source_path) {

  *self = (interface_s){
      .renderer = {},
      .sprites = {
          .animas = {
              .count = core_logic->animas.count,
              .data = malloc(core_logic->animas.count * sizeof(sprite_s)),
          },
      },
  };

  char path_buffer[FILENAME_MAX];

  cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);
  slog_display(SLOG_INFO, 0, "Renderer with sheet from: %s\n", path_buffer);

  renderer_ctor(&self->renderer, core_logic->maze.dimensions, path_buffer);

  { // Sprite block
    // Animas
    for (uint8_t idx = 0; idx < core_logic->animas.count; ++idx) {
      sprite_ctor(&self->sprites.animas.data[idx], 16, atomic_load(&core_logic->situation.animas.data[idx].location));
    }

    // Persona
    sprite_ctor(&self->sprites.persona, 16, atomic_load(&core_logic->situation.persona.location));
  }
}

void interface_reset(interface_s *self, const state_s *state) {

  { // sprites
    for (size_t idx = 0; idx < state->animas.count; ++idx) {
      auto maze_location = atomic_load(&state->situation.animas.data[idx].location);

      self->sprites.animas.data[idx].location = (Pair_uint32){
          .x = (((uint32_t)maze_location.x) + RENDER_TOP) * TILE_PIXELS,
          .y = (uint32_t)maze_location.y * TILE_PIXELS,
      };
    }

    { // persona
      auto maze_location = atomic_load(&state->situation.persona.location);

      self->sprites.persona.location = (Pair_uint32){
          .x = (((uint32_t)maze_location.x) + RENDER_TOP) * TILE_PIXELS,
          .y = (uint32_t)maze_location.y * TILE_PIXELS,
      };
    }
  }
}
