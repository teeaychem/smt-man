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
      sprite_ctor(&self->sprites.animas.data[idx], 16, atomic_load(&core_logic->situation.animas.data[idx].location), RENDER_TOP);
    }

    // Persona
    sprite_ctor(&self->sprites.persona, 16, atomic_load(&core_logic->situation.persona.location), RENDER_TOP);
  }
}
