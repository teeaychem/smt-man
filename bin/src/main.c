#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>

#include "config.h"
#include "interface.h"
#include "render/rgb_momentum.h"
#include "render/timer_nano.h"
#include "renderer.h"
#include "spirit.h"
#include "state.h"

constexpr size_t ANIMA_COUNT = 2;

pthread_t ANIMA_THREADS[ANIMA_COUNT];
spirit_setup_s ANIMA_SPIRITS[ANIMA_COUNT];

void game_state(state_s *logic, interface_s *render) {
  SDL_Event event;
  SDL_zero(event);

  bool game_loop = true;

  uint64_t frame_nanoseconds = 0;
  TimerNano frame_cap_timer = TimerNano_default();

  RGBMomentum colour = {};

  printf("New game\n");
  logic->hold = false;
  situation_reset(&logic->situation);
  interface_reset(render, logic);

  //
  situation_s game_situation = {
      .animas = {
          .count = ANIMA_COUNT,
          .data = alloca(ANIMA_COUNT * sizeof(*game_situation.animas.data)),
      }};

  while (game_loop) {
    TimerNano_start(&frame_cap_timer);

    situation_copy(&logic->situation, &game_situation);
    renderer_draw_maze(&render->renderer, &logic->maze);

    while (SDL_PollEvent(&event)) {
      if (event.type == SDL_EVENT_QUIT) {
        exit(101);
        game_loop = false;
      }

      persona_handle_event(&logic->persona, &event);
    }

    { // logic block
      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        pthread_cond_broadcast(&ANIMA_SPIRITS[id].cond_frame);
      }
    }

    { /// Pre-render block

      rgb_momentum_advance(&colour);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        anima_on_frame(&logic->animas.data[id], &game_situation, &render->sprites.animas.data[id], &logic->maze, TILE_PIXELS, RENDER_TOP);
      }
      persona_on_frame(&logic->persona, &render->sprites.persona, &logic->maze, &game_situation, TILE_PIXELS, RENDER_TOP);
    }

    { /// Render_block
      SDL_RenderClear(render->renderer.renderer);

      SDL_SetRenderDrawColor(render->renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        renderer_anima(&render->renderer, &logic->animas.data[id], &game_situation, &render->sprites.animas.data[id], RENDER_DRAW);
      }
      renderer_persona(&render->renderer, &logic->persona, &render->sprites.persona, &game_situation, RENDER_DRAW);

      renderer_render_frame_buffer(&render->renderer);
    }

    { /// Post-render block
      renderer_clear(&render->renderer);
      situation_copy(&game_situation, &logic->situation);
    }

    if (logic->hold) {
      for (size_t idx = 0; idx < logic->animas.count; ++idx) {
        pthread_mutex_lock(&ANIMA_SPIRITS[idx].mtx_held);
        pthread_cond_wait(&ANIMA_SPIRITS[idx].cond_held, &ANIMA_SPIRITS[idx].mtx_held);
        printf("Held\n");
        pthread_mutex_unlock(&ANIMA_SPIRITS[idx].mtx_held);
      }

      game_loop = false;
    }

    { // wait block
      frame_nanoseconds = TimerNano_get_ticks(&frame_cap_timer);
      if (frame_nanoseconds < NS_PER_FRAME) {
        SDL_DelayNS(NS_PER_FRAME - frame_nanoseconds);
      }
    }
  }
}

int main() { // int main(int argc, char *argv[]) {

  int exit_code = 0;

  { // slog setup
    uint16_t slog_level_flags = SLOG_ERROR | SLOG_WARN | SLOG_DEBUG;
    slog_init("logfile", slog_level_flags, 1);
  }

  char *source_path;
  { // Set source path, static lifetime
    int source_path_length;
    source_path_build(&source_path, &source_path_length);
  }

  state_s core_logic = {};
  state_ctor(&core_logic, ANIMA_COUNT, source_path);

  { // Core logic
    for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {

      ANIMA_SPIRITS[idx] = (spirit_setup_s){
          .hold = &core_logic.hold,
          .anima = &core_logic.animas.data[idx],
          .anima_count = ANIMA_COUNT,
          .maze = &core_logic.maze,
          .source_path = source_path,
          .the_situation = &core_logic.situation,
          .cond_frame = PTHREAD_COND_INITIALIZER,
          .mtx_spirit = PTHREAD_MUTEX_INITIALIZER,
      };

      anima_ctor(&core_logic.animas.data[idx], &core_logic.situation, idx, &core_logic.maze);

      pthread_create(&ANIMA_THREADS[ANIMA_SPIRITS[idx].anima->id], nullptr, spirit_ctor, (void *)&ANIMA_SPIRITS[idx]);
    }
  }

  interface_s core_render = {};
  interface_ctor(&core_render, &core_logic, source_path);

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }

  { // core block
    bool core_loop = true;

    while (core_loop) {
      game_state(&core_logic, &core_render);
    }
  }

exit_block: {
  renderer_dtor(&core_render.renderer);
  SDL_Quit();

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], nullptr);
  }

  maze_dtor((maze_s *)&core_logic.maze);
  free(source_path);
  slog_destroy();

  return exit_code;
}
}
