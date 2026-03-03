#include "renderer.h"
#include "state.h"

struct interface {
  renderer_s renderer;

  struct {
    // Anima sprites
    struct {
      size_t count;
      sprite_s *data;
    } animas;

    // Persona sprite
    sprite_s persona;
  } sprites;
};
typedef struct interface interface_s;

void interface_ctor(interface_s *self, const state_s *core_logic, const char *source_path);

void interface_reset(interface_s *self, const state_s *state);
