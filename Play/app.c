/*
 * The live player as SDL3 app callbacks (SDL_AppInit/Iterate/Event/Quit), shared by the
 * native window (`Play/native.c` includes this file) and the browser build (compiled alone
 * with Emscripten, where SDL drives the callbacks from requestAnimationFrame).
 *
 * The emulator is `Play.Core` (Lean): `nes_core_load`, `nes_core_frame`, `nes_core_rgb`,
 * `nes_core_pcm`. This file only moves pixels, samples and key states.
 *
 * Pacing: frames are due every 1/60.0988 s by the clock (at most 4 per callback, then the
 * schedule restarts); audio is queued as produced and dropped if the queue grows past
 * 250 ms (for example while a browser keeps audio suspended).
 */
#include <lean/lean.h>
#include <SDL3/SDL.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef __EMSCRIPTEN__
#define SDL_MAIN_USE_CALLBACKS 1
#include <SDL3/SDL_main.h>
#include <emscripten.h>
#endif

void lean_initialize_runtime_module(void); /* not declared in lean.h */

lean_object *nes_core_load(lean_object *rom);
lean_object *nes_core_frame(lean_object *s, uint32_t keys);
lean_object *nes_core_rgb(lean_object *s); /* consumes s */
lean_object *nes_core_pcm(lean_object *s); /* consumes s */

#define FRAME_NS 16639267ull /* NTSC: 60.0988 frames/s */
#define AUDIO_MAX (44100 * 2 / 4)

static SDL_Window *win;
static SDL_Renderer *ren;
static SDL_Texture *tex;
static SDL_AudioStream *aud;
static lean_object *sess; /* owned Play.Session, or NULL before a ROM is loaded */
static int paused, reset_req;
static uint64_t next_ns;
static uint32_t frames_run; /* emulated frames since start (for the page's fps readout) */
static char status[256] = "drop or open a .nes ROM";

const char *nes_play_status(void) { return status; }

/* Load a ROM image; returns 0 on success (the message is in nes_play_status()). */
int nes_play_load_bytes(const uint8_t *data, size_t len, const char *name) {
  lean_object *ba = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(ba), data, len);
  lean_object *r = nes_core_load(ba);
  if (lean_obj_tag(r) == 0) { /* Except.error msg */
    snprintf(status, sizeof status, "%s: %s", name, lean_string_cstr(lean_ctor_get(r, 0)));
    lean_dec(r);
    return 1;
  }
  lean_object *s = lean_ctor_get(r, 0);
  lean_inc(s);
  lean_dec(r);
  if (sess) lean_dec(sess);
  sess = s;
  paused = 0;
  next_ns = SDL_GetTicksNS();
  if (aud) SDL_ClearAudioStream(aud);
  snprintf(status, sizeof status, "playing %s", name);
  if (win) SDL_SetWindowTitle(win, status);
  return 0;
}

int nes_play_load_file(const char *path) {
  size_t len = 0;
  void *data = SDL_LoadFile(path, &len);
  if (!data) { snprintf(status, sizeof status, "%s: %s", path, SDL_GetError()); return 1; }
  const char *base = strrchr(path, '/');
  int rc = nes_play_load_bytes(data, len, base ? base + 1 : path);
  SDL_free(data);
  return rc;
}

/* Controller-1 bit for a key (A B Select Start Up Down Left Right), or 0. */
static uint32_t pad_bit(SDL_Scancode k) {
  switch (k) {
  case SDL_SCANCODE_X: return 0x01;                            /* A */
  case SDL_SCANCODE_Z: return 0x02;                            /* B */
  case SDL_SCANCODE_RSHIFT: case SDL_SCANCODE_TAB: return 0x04; /* Select */
  case SDL_SCANCODE_RETURN: return 0x08;                       /* Start */
  case SDL_SCANCODE_UP: return 0x10;
  case SDL_SCANCODE_DOWN: return 0x20;
  case SDL_SCANCODE_LEFT: return 0x40;
  case SDL_SCANCODE_RIGHT: return 0x80;
  default: return 0;
  }
}

/* Buttons pressed since the last frame read the pad: a tap shorter than a frame still
   reaches the game. */
static uint32_t pad_latch;

static uint32_t read_pad(void) {
  int n = 0;
  const bool *k = SDL_GetKeyboardState(&n);
  uint32_t b = pad_latch;
  pad_latch = 0;
  for (int i = 0; i < n; i++)
    if (k[i]) b |= pad_bit((SDL_Scancode)i);
  /* The NES pad cannot press opposite directions at once; some games break if it does. */
  if ((b & 0x30) == 0x30) b &= ~0x30u;
  if ((b & 0xC0) == 0xC0) b &= ~0xC0u;
  return b;
}

SDL_AppResult SDL_AppInit(void **appstate, int argc, char **argv) {
  (void)appstate;
#ifdef __EMSCRIPTEN__
  /* In the browser C owns `main`, so the Lean runtime and modules start here. */
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  extern lean_object *initialize_nes_Play_Core(uint8_t builtin);
  lean_object *res = initialize_nes_Play_Core(1);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); return SDL_APP_FAILURE; }
  lean_dec_ref(res);
#endif
  int scale = 3;
  for (int i = 1; i + 1 < argc; i++)
    if (!strcmp(argv[i], "--scale")) scale = SDL_max(1, SDL_min(8, atoi(argv[i + 1])));
  SDL_SetHint(SDL_HINT_MAIN_CALLBACK_RATE, "240"); /* native: wake often, run frames by clock */
  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO)) {
    fprintf(stderr, "nes-play: SDL init failed: %s\n", SDL_GetError());
    return SDL_APP_FAILURE;
  }
  if (!SDL_CreateWindowAndRenderer("nes-lean", 256 * scale, 240 * scale, SDL_WINDOW_RESIZABLE,
                                   &win, &ren)) {
    fprintf(stderr, "nes-play: SDL window failed: %s\n", SDL_GetError());
    return SDL_APP_FAILURE;
  }
  SDL_SetRenderLogicalPresentation(ren, 256, 240, SDL_LOGICAL_PRESENTATION_LETTERBOX);
  tex = SDL_CreateTexture(ren, SDL_PIXELFORMAT_RGB24, SDL_TEXTUREACCESS_STREAMING, 256, 240);
  SDL_SetTextureScaleMode(tex, SDL_SCALEMODE_NEAREST);
  SDL_AudioSpec spec = { SDL_AUDIO_S16LE, 1, 44100 };
  aud = SDL_OpenAudioDeviceStream(SDL_AUDIO_DEVICE_DEFAULT_PLAYBACK, &spec, NULL, NULL);
  if (aud) SDL_ResumeAudioStreamDevice(aud);
  else fprintf(stderr, "nes-play: no audio device (%s); playing silently\n", SDL_GetError());
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--scale")) { i++; continue; }
    if (nes_play_load_file(argv[i]) != 0) {
      fprintf(stderr, "nes-play: %s\n", status);
      return SDL_APP_FAILURE;
    }
  }
  return SDL_APP_CONTINUE;
}

SDL_AppResult SDL_AppEvent(void *appstate, SDL_Event *e) {
  (void)appstate;
  if (e->type == SDL_EVENT_QUIT) return SDL_APP_SUCCESS;
  if (e->type == SDL_EVENT_KEY_DOWN) pad_latch |= pad_bit(e->key.scancode);
  if (e->type == SDL_EVENT_KEY_DOWN && !e->key.repeat) {
#ifndef __EMSCRIPTEN__
    if (e->key.scancode == SDL_SCANCODE_ESCAPE) return SDL_APP_SUCCESS;
#endif
    if (e->key.scancode == SDL_SCANCODE_R) reset_req = 1;
    if (e->key.scancode == SDL_SCANCODE_P && sess) {
      paused = !paused;
      next_ns = SDL_GetTicksNS();
    }
  }
  if (e->type == SDL_EVENT_DROP_FILE && e->drop.data) nes_play_load_file(e->drop.data);
  return SDL_APP_CONTINUE;
}

SDL_AppResult SDL_AppIterate(void *appstate) {
  (void)appstate;
  if (sess && !paused) {
    uint64_t now = SDL_GetTicksNS();
    int ran = 0;
    while (now >= next_ns && ran < 4) {
      uint32_t keys = read_pad() | (reset_req ? 0x200u : 0u);
      reset_req = 0;
      sess = nes_core_frame(sess, keys);
      if (aud) {
        lean_inc(sess);
        lean_object *pcm = nes_core_pcm(sess);
        SDL_PutAudioStreamData(aud, lean_sarray_cptr(pcm), (int)lean_sarray_size(pcm));
        lean_dec(pcm);
      }
      next_ns += FRAME_NS;
      frames_run++;
      ran++;
    }
    if (now >= next_ns) next_ns = now + FRAME_NS; /* too far behind: drop the backlog */
    if (aud && SDL_GetAudioStreamQueued(aud) > AUDIO_MAX) SDL_ClearAudioStream(aud);
  }
  SDL_SetRenderDrawColor(ren, 0, 0, 0, 255);
  SDL_RenderClear(ren);
  if (sess) {
    lean_inc(sess);
    lean_object *rgb = nes_core_rgb(sess);
    SDL_UpdateTexture(tex, NULL, lean_sarray_cptr(rgb), 256 * 3);
    lean_dec(rgb);
    SDL_RenderTexture(ren, tex, NULL, NULL);
  }
  SDL_RenderPresent(ren);
  return SDL_APP_CONTINUE;
}

void SDL_AppQuit(void *appstate, SDL_AppResult result) {
  (void)appstate; (void)result;
  if (sess) { lean_dec(sess); sess = NULL; }
  /* SDL destroys the window, renderer and audio stream itself after this returns. */
}

#ifdef __EMSCRIPTEN__
/* Called from the page: the ROM was written to the in-memory file system at `path`. */
EMSCRIPTEN_KEEPALIVE int nes_web_load(const char *path) { return nes_play_load_file(path); }
EMSCRIPTEN_KEEPALIVE const char *nes_web_status(void) { return status; }
EMSCRIPTEN_KEEPALIVE uint32_t nes_web_frames(void) { return frames_run; }
EMSCRIPTEN_KEEPALIVE void nes_web_pause(int p) { if (sess) { paused = p; next_ns = SDL_GetTicksNS(); } }
#endif
