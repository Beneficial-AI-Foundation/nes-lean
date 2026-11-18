/*
 * Native `nes-play`: the SDL3 app (`app.c`) run from Lean's `main`
 * (`Play.lean` calls `nes_play_run`).
 *
 * macOS threading: Cocoa only allows windows and event handling on the process's main
 * thread, but Lean's generated `main` runs the program on a worker thread
 * (`lean_run_main`) and parks the main thread in a join. So on macOS the executable is
 * linked with `-e _nes_play_entry` (see lakefile.lean): the entry point starts the usual
 * `main` on a big-stack thread and keeps the real main thread waiting for one job, which
 * `nes_play_run` hands it: the whole SDL callback loop. The Lean thread waits meanwhile.
 * Elsewhere the loop runs directly on the calling thread.
 */
#include "app.c"

#define SDL_MAIN_HANDLED
#define SDL_MAIN_NOIMPL
#include <SDL3/SDL_main.h>
#include <stdlib.h>

void lean_initialize_thread(void);
void lean_finalize_thread(void);

struct run_args { int argc; char **argv; int result; };

static void run_app(void *p) {
  struct run_args *a = p;
  lean_initialize_thread(); /* Lean objects are allocated from this thread too */
  a->result = SDL_EnterAppMainCallbacks(a->argc, a->argv, SDL_AppInit, SDL_AppIterate,
                                        SDL_AppEvent, SDL_AppQuit);
  lean_finalize_thread();
}

#ifdef __APPLE__
#include <pthread.h>

extern int main(int argc, char **argv);

static int entry_argc;
static char **entry_argv;
static pthread_mutex_t job_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t job_cv = PTHREAD_COND_INITIALIZER;
static struct run_args *job;
static int job_done;

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
  for (;;) {
    pthread_mutex_lock(&job_mu);
    while (!job || job_done) pthread_cond_wait(&job_cv, &job_mu);
    struct run_args *a = job;
    pthread_mutex_unlock(&job_mu);
    run_app(a); /* on the real main thread */
    pthread_mutex_lock(&job_mu);
    job_done = 1;
    pthread_cond_broadcast(&job_cv);
    pthread_mutex_unlock(&job_mu);
  }
}

static void run_on_main(struct run_args *a) {
  if (pthread_main_np()) { run_app(a); return; }
  pthread_mutex_lock(&job_mu);
  job = a;
  job_done = 0;
  pthread_cond_broadcast(&job_cv);
  while (!job_done) pthread_cond_wait(&job_cv, &job_mu);
  job = NULL;
  pthread_mutex_unlock(&job_mu);
}
#else
static void run_on_main(struct run_args *a) { run_app(a); }
#endif

/* `Play.run : List String → BaseIO UInt32`: argv[1..] = the Lean `main` arguments. */
uint32_t nes_play_run(b_lean_obj_arg args) {
  int argc = 1;
  for (b_lean_obj_arg l = args; !lean_is_scalar(l); l = lean_ctor_get(l, 1)) argc++;
  char **argv = calloc((size_t)argc + 1, sizeof(char *));
  argv[0] = "nes-play";
  int i = 1;
  for (b_lean_obj_arg l = args; !lean_is_scalar(l); l = lean_ctor_get(l, 1))
    argv[i++] = (char *)lean_string_cstr(lean_ctor_get(l, 0));
  struct run_args a = { argc, argv, 1 };
  run_on_main(&a);
  free(argv);
  return (uint32_t)a.result;
}
