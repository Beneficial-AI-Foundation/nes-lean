/*
 * SDL3 shim for `nes-play` (the live window). Not part of the verified `Nes` library: this
 * is the platform layer only — a window showing the 256x240 RGB frame, a 44.1 kHz mono
 * 16-bit audio stream, and the keyboard read as controller-1 buttons.
 *
 * Lean v4.36 calling convention for `BaseIO` externs: no world argument, the value is
 * returned directly (scalars unboxed, `Unit` as `lean_box(0)`).
 *
 * macOS threading: Cocoa only allows windows and event handling on the process's main
 * thread, but Lean's generated `main` runs the program on a worker thread
 * (`lean_run_main`) and parks the main thread in a join. So on macOS the executable is
 * linked with `-e _nes_play_entry` (see lakefile.lean): the entry point starts the usual
 * `main` on a big-stack thread and keeps the real main thread waiting for jobs; every SDL
 * window/event call below is handed to it (`on_main`: one job slot, mutex + condvars) and
 * the caller waits for it to finish. Elsewhere the calls run directly.
 */
#include <lean/lean.h>
#include <SDL3/SDL.h>

#ifdef __APPLE__
#include <pthread.h>
#include <stdlib.h>

extern int main(int argc, char **argv);

static int entry_argc;
static char **entry_argv;

static pthread_mutex_t job_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t job_posted = PTHREAD_COND_INITIALIZER;
static pthread_cond_t job_done = PTHREAD_COND_INITIALIZER;
static void (*job_fn)(void *); /* non-NULL while a job is pending or running */
static void *job_ctx;
static int job_finished;

static void *run_lean_main(void *unused) {
  (void)unused;
  exit(main(entry_argc, entry_argv)); /* exit() ends the process, main thread included */
}

/* Process entry point (`-e _nes_play_entry`); dyld has already run all initializers. */
int nes_play_entry(int argc, char **argv) {
  entry_argc = argc;
  entry_argv = argv;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)64 << 20);
  pthread_t t;
  if (pthread_create(&t, &attr, run_lean_main, NULL) != 0) return main(argc, argv);
  pthread_mutex_lock(&job_mu);
  for (;;) {
    while (!job_fn || job_finished) pthread_cond_wait(&job_posted, &job_mu);
    void (*fn)(void *) = job_fn;
    void *ctx = job_ctx;
    pthread_mutex_unlock(&job_mu);
    fn(ctx); /* on the real main thread */
    pthread_mutex_lock(&job_mu);
    job_finished = 1;
    pthread_cond_broadcast(&job_done);
  }
}

/* Run fn(ctx) on the main thread and wait for it. Only the Lean thread calls this. */
static void on_main(void *ctx, void (*fn)(void *)) {
  if (pthread_main_np()) { fn(ctx); return; }
  pthread_mutex_lock(&job_mu);
  job_fn = fn;
  job_ctx = ctx;
  job_finished = 0;
  pthread_cond_signal(&job_posted);
  while (!job_finished) pthread_cond_wait(&job_done, &job_mu);
  job_fn = NULL;
  pthread_mutex_unlock(&job_mu);
}
#else
static void on_main(void *ctx, void (*fn)(void *)) { fn(ctx); }
#endif

static SDL_Window *win;
static SDL_Renderer *ren;
static SDL_Texture *tex;
static SDL_AudioStream *aud;
static int quit_req, reset_req, pause_req;

/* ---- open ------------------------------------------------------------------------------ */

struct open_args { const char *title; int scale; uint32_t result; };

static void do_open(void *p) {
  struct open_args *a = p;
  a->result = 1;
  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO)) return;
  a->result = 2;
  if (!SDL_CreateWindowAndRenderer(a->title, 256 * a->scale, 240 * a->scale,
                                   SDL_WINDOW_RESIZABLE, &win, &ren))
    return;
  SDL_SetRenderLogicalPresentation(ren, 256, 240, SDL_LOGICAL_PRESENTATION_LETTERBOX);
  a->result = 3;
  tex = SDL_CreateTexture(ren, SDL_PIXELFORMAT_RGB24, SDL_TEXTUREACCESS_STREAMING, 256, 240);
  if (!tex) return;
  SDL_SetTextureScaleMode(tex, SDL_SCALEMODE_NEAREST);
  SDL_AudioSpec spec = { SDL_AUDIO_S16LE, 1, 44100 };
  aud = SDL_OpenAudioDeviceStream(SDL_AUDIO_DEVICE_DEFAULT_PLAYBACK, &spec, NULL, NULL);
  if (aud) SDL_ResumeAudioStreamDevice(aud); /* no audio device: play silently */
  SDL_RaiseWindow(win);
  a->result = 0;
}

/* 0 = ok; otherwise an error code (the message is in nes_play_error). */
uint32_t nes_play_open(b_lean_obj_arg title, uint32_t scale) {
  struct open_args a = { lean_string_cstr(title), (int)scale, 1 };
  on_main(&a, do_open);
  return a.result;
}

lean_obj_res nes_play_error(void) { return lean_mk_string(SDL_GetError()); }

/* ---- input ----------------------------------------------------------------------------- */

static void do_poll(void *p) {
  uint32_t *out = p;
  SDL_Event e;
  while (SDL_PollEvent(&e)) {
    if (e.type == SDL_EVENT_QUIT) quit_req = 1;
    if (e.type == SDL_EVENT_KEY_DOWN && !e.key.repeat) {
      if (e.key.scancode == SDL_SCANCODE_ESCAPE) quit_req = 1;
      if (e.key.scancode == SDL_SCANCODE_R) reset_req = 1;
      if (e.key.scancode == SDL_SCANCODE_P) pause_req = 1;
    }
  }
  const bool *k = SDL_GetKeyboardState(NULL);
  uint32_t b = 0;
  if (k[SDL_SCANCODE_X]) b |= 0x01;                             /* A */
  if (k[SDL_SCANCODE_Z]) b |= 0x02;                             /* B */
  if (k[SDL_SCANCODE_RSHIFT] || k[SDL_SCANCODE_TAB]) b |= 0x04; /* Select */
  if (k[SDL_SCANCODE_RETURN]) b |= 0x08;                        /* Start */
  if (k[SDL_SCANCODE_UP]) b |= 0x10;
  if (k[SDL_SCANCODE_DOWN]) b |= 0x20;
  if (k[SDL_SCANCODE_LEFT]) b |= 0x40;
  if (k[SDL_SCANCODE_RIGHT]) b |= 0x80;
  /* The NES pad cannot press opposite directions at once; some games break if it does. */
  if ((b & 0x30) == 0x30) b &= ~0x30u;
  if ((b & 0xC0) == 0xC0) b &= ~0xC0u;
  if (quit_req) b |= 0x100;
  if (reset_req) b |= 0x200;
  if (pause_req) b |= 0x400;
  reset_req = pause_req = 0;
  *out = b;
}

/*
 * Pump events and read the keyboard. Bits 0..7: controller-1 buttons
 * (A B Select Start Up Down Left Right); bit 8: quit; bit 9: reset pressed;
 * bit 10: pause toggled.
 */
uint32_t nes_play_poll(void) {
  uint32_t b = 0;
  on_main(&b, do_poll);
  return b;
}

/* ---- video ----------------------------------------------------------------------------- */

static void do_present(void *p) {
  SDL_UpdateTexture(tex, NULL, p, 256 * 3);
  SDL_SetRenderDrawColor(ren, 0, 0, 0, 255);
  SDL_RenderClear(ren);
  SDL_RenderTexture(ren, tex, NULL, NULL);
  SDL_RenderPresent(ren);
}

/* Show one 256x240 RGB24 frame (row-major, 3 bytes per pixel). */
lean_obj_res nes_play_present(b_lean_obj_arg rgb) {
  if (lean_sarray_size(rgb) >= 256 * 240 * 3) on_main(lean_sarray_cptr(rgb), do_present);
  return lean_box(0);
}

/* ---- audio (SDL audio streams are thread-safe; no main-thread hop needed) -------------- */

/* Queue 16-bit little-endian mono PCM at 44.1 kHz. */
lean_obj_res nes_play_audio(b_lean_obj_arg pcm) {
  if (aud) SDL_PutAudioStreamData(aud, lean_sarray_cptr(pcm), (int)lean_sarray_size(pcm));
  return lean_box(0);
}

/* Bytes of audio queued but not yet played (0 when there is no audio device). */
uint32_t nes_play_queued(void) {
  if (!aud) return 0;
  int q = SDL_GetAudioStreamQueued(aud);
  return q < 0 ? 0 : (uint32_t)q;
}

uint32_t nes_play_has_audio(void) { return aud != NULL; }

/* ---- close ----------------------------------------------------------------------------- */

static void do_close(void *unused) {
  (void)unused;
  if (aud) SDL_DestroyAudioStream(aud);
  if (tex) SDL_DestroyTexture(tex);
  if (ren) SDL_DestroyRenderer(ren);
  if (win) SDL_DestroyWindow(win);
  aud = NULL; tex = NULL; ren = NULL; win = NULL;
  SDL_Quit();
}

lean_obj_res nes_play_close(void) {
  on_main(NULL, do_close);
  return lean_box(0);
}
