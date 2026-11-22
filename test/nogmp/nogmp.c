// LD_PRELOAD shim: report (REL_NOGMP=log) or abort on (REL_NOGMP=abort) every GMP allocation made while code of this
// package is on the stack. libleanshared is linked -Bsymbolic, so its own calls to lean_nat_pow, lean_big_*_to_nat,
// lean_nat_big_* bind internally and interposing those names misses every call the runtime or the interpreter makes;
// every bignum, whichever entry point made it, is allocated through GMP's allocator pointers, so those are hooked.
// A stack is ours when one of its frames lies in a shared object under a directory of REL_NOGMP_OURS (`:`-separated);
// a stack with none is the elaborator, the kernel or the interpreter, counted and never aborted on.
#define _GNU_SOURCE
#include <dlfcn.h>
#include <execinfo.h>
#include <limits.h>
#include <link.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define DEPTH 64
#define SITES 4096
#define OBJS 256
#define DIRS 16

typedef void *(*alloc_fn)(size_t);
typedef void *(*realloc_fn)(void *, size_t, size_t);
static alloc_fn *alloc_ptr, orig_alloc;
static realloc_fn *realloc_ptr, orig_realloc;
static int abort_mode;
static char dirs[DIRS][PATH_MAX];
static int ndirs;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static __thread int busy;

// one entry per loaded object seen in a stack: whether it lies under a REL_NOGMP_OURS directory
static struct { uintptr_t lo, hi; int ours; } objs[OBJS];
static int nobjs;
// one entry per call site: the return address into our code (ours) or the innermost frame outside GMP and the shim
static struct { void *key; int ours, load; unsigned long n; } sites[SITES];
static int nsites;
static unsigned long total_ours, total_lean, dropped;

static int under(const char *path) {
  char real[PATH_MAX];
  if (!realpath(path, real)) return 0;
  for (int i = 0; i < ndirs; i++) {
    size_t l = strlen(dirs[i]);
    if (strncmp(real, dirs[i], l) == 0 && real[l] == '/') return 1;
  }
  return 0;
}

static int add_obj(struct dl_phdr_info *info, size_t size, void *data) {
  (void)size; (void)data;
  if (nobjs == OBJS) { fprintf(stderr, "nogmp: more than %d loaded objects; raise OBJS in nogmp.c\n", OBJS); abort(); }
  uintptr_t lo = UINTPTR_MAX, hi = 0;
  for (int i = 0; i < info->dlpi_phnum; i++) {
    const ElfW(Phdr) *p = &info->dlpi_phdr[i];
    if (p->p_type != PT_LOAD) continue;
    uintptr_t a = info->dlpi_addr + p->p_vaddr;
    if (a < lo) lo = a;
    if (a + p->p_memsz > hi) hi = a + p->p_memsz;
  }
  objs[nobjs].lo = lo; objs[nobjs].hi = hi;
  objs[nobjs].ours = info->dlpi_name && info->dlpi_name[0] && under(info->dlpi_name);
  nobjs++;
  return 0;
}

// dladdr scans the dynamic symbols of the object (libleanshared has hundreds of thousands) on every call, so an
// address is placed by the PT_LOAD ranges of the loaded objects; a miss re-reads them, since modules are dlopened late
static int ours(void *addr) {
  uintptr_t a = (uintptr_t)addr;
  for (int pass = 0; pass < 2; pass++) {
    for (int i = 0; i < nobjs; i++) if (objs[i].lo <= a && a < objs[i].hi) return objs[i].ours;
    if (pass == 0) { nobjs = 0; dl_iterate_phdr(add_obj, 0); }
  }
  return 0;
}

// `addr2line -f -C` on the object's offset names static functions too, which dladdr (dynamic symbols only) cannot
static void frame(FILE *out, int i, void *addr) {
  Dl_info d;
  if (!dladdr(addr, &d) || !d.dli_fname) { fprintf(out, "  #%-2d %p ?\n", i, addr); return; }
  uintptr_t off = (uintptr_t)addr - (uintptr_t)d.dli_fbase - 1;
  char cmd[PATH_MAX + 64], fn[1024] = "";
  snprintf(cmd, sizeof cmd, "addr2line -f -C -e '%s' 0x%lx", d.dli_fname, (unsigned long)off);
  FILE *p = popen(cmd, "r");
  if (!p) { fprintf(out, "nogmp: popen %s failed\n", cmd); abort(); }
  if (!fgets(fn, sizeof fn, p)) fn[0] = 0;
  pclose(p);
  fn[strcspn(fn, "\n")] = 0;
  if (!fn[0] || fn[0] == '?') snprintf(fn, sizeof fn, "%s", d.dli_sname ? d.dli_sname : "?");
  fprintf(out, "  #%-2d %s+0x%lx  %s\n", i, d.dli_fname, (unsigned long)off, fn);
}

// a module initializer computes the module's closed terms once, when the module loads (a Float literal goes through
// Float.ofScientific, a big literal through lean_cstr_to_nat): listed, never aborted on, since no call repeats it.
// The initializer is the exported C function the Lean ABI names `initialize_<package>_<module>`.
static int at_load(void *addr) {
  Dl_info d;
  const ElfW(Sym) *sym = 0;
  if (!dladdr1(addr, &d, (void **)&sym, RTLD_DL_SYMENT) || !d.dli_sname || !sym) return 0;
  uintptr_t a = (uintptr_t)addr - 1, lo = (uintptr_t)d.dli_saddr;
  return lo <= a && a < lo + sym->st_size && strncmp(d.dli_sname, "initialize_", 11) == 0;
}

// at_load per return address, memoised: dladdr1 scans the object's symbols, and a stack is classified on every hit
#define MEMO 16384
static struct { void *addr; int v; } memo[MEMO];
static int in_init(void *addr) {
  for (unsigned h = ((uintptr_t)addr >> 2) % MEMO, k = 0; k < MEMO; k++, h = (h + 1) % MEMO) {
    if (memo[h].addr == addr) return memo[h].v;
    if (!memo[h].addr) { memo[h].addr = addr; return memo[h].v = at_load(addr); }
  }
  return at_load(addr);
}

// a stack is load-time when any frame of ours on it is a module initializer: an initializer may call a run-path
// function (`Arr.bools` → `Coc.encodeAt`), and that call is made once, at load
// Unwinding is nearly all the shim's cost, so a hit first takes SHALLOW frames: one whose innermost frame of ours is a
// known run-time site is counted there; any other is unwound to DEPTH and classified. A run-time site is never keyed
// by a shallow stack alone before a deep one has classified it, so a load-time key cannot hide a run-time call.
#define SHALLOW 16
static void hit(void) {
  void *bt[DEPTH];
  int n = backtrace(bt, SHALLOW), first = -1, load = 0;
  pthread_mutex_lock(&mu);
  for (int i = 2; i < n && first < 0; i++) if (ours(bt[i])) first = i;
  if (first >= 0)
    for (int s = 0; s < nsites; s++)
      if (sites[s].key == bt[first] && sites[s].ours && !sites[s].load) { sites[s].n++; total_ours++; pthread_mutex_unlock(&mu); return; }
  if (n == SHALLOW) n = backtrace(bt, DEPTH);
  first = -1;
  for (int i = 2; i < n && !load; i++) if (ours(bt[i])) { if (first < 0) first = i; load = in_init(bt[i]); }
  void *key = first >= 0 ? bt[first] : (n > 4 ? bt[4] : 0);
  if (first >= 0) total_ours++; else total_lean++;
  int s = 0;
  while (s < nsites && !(sites[s].key == key && sites[s].load == load)) s++;
  int fresh = s == nsites;
  if (fresh) {
    if (nsites < SITES) { sites[s].key = key; sites[s].ours = first >= 0; sites[s].load = load; nsites++; }
    else { dropped++; s = -1; }
  }
  if (s >= 0) sites[s].n++;
  if (fresh && first >= 0) {
    fprintf(stderr, "nogmp: GMP allocation from this package's code%s (pid %d), call site #%d:\n",
            load ? ", under a module initializer" : "", (int)getpid(), first);
    for (int i = 2; i < n && i <= first + 3; i++) frame(stderr, i, bt[i]);
    if (abort_mode && !load) { fprintf(stderr, "nogmp: REL_NOGMP=abort, aborting\n"); abort(); }
  }
  pthread_mutex_unlock(&mu);
}


static void *my_alloc(size_t n) {
  void *r = orig_alloc(n);
  if (!busy) { busy = 1; hit(); busy = 0; }
  return r;
}

static void *my_realloc(void *p, size_t o, size_t n) {
  void *r = orig_realloc(p, o, n);
  if (!busy) { busy = 1; hit(); busy = 0; }
  return r;
}

static void summary(void) {
  if (!alloc_ptr) return;
  pthread_mutex_lock(&mu);
  fprintf(stderr, "nogmp: pid %d: %lu GMP allocations from this package's code, %lu from Lean's own (%d sites, %lu past the table)\n",
          (int)getpid(), total_ours, total_lean, nsites, dropped);
  for (int s = 0; s < nsites; s++) if (sites[s].ours) { fprintf(stderr, "nogmp: %s %lu at", sites[s].load ? "load" : "ours", sites[s].n); frame(stderr, 0, sites[s].key); }
  pthread_mutex_unlock(&mu);
}

__attribute__((constructor)) static void init(void) {
  const char *m = getenv("REL_NOGMP");
  if (!m || !m[0]) return;
  if (!strcmp(m, "abort")) abort_mode = 1;
  else if (strcmp(m, "log")) { fprintf(stderr, "nogmp: REL_NOGMP=%s, expected log or abort\n", m); abort(); }
  const char *o = getenv("REL_NOGMP_OURS");
  if (!o || !o[0]) { fprintf(stderr, "nogmp: REL_NOGMP_OURS is unset; set it to the package's .lake/build/lib\n"); abort(); }
  char buf[PATH_MAX * 4];
  snprintf(buf, sizeof buf, "%s", o);
  for (char *save, *t = strtok_r(buf, ":", &save); t; t = strtok_r(0, ":", &save)) {
    if (ndirs == DIRS) { fprintf(stderr, "nogmp: REL_NOGMP_OURS names more than %d directories\n", DIRS); abort(); }
    if (!realpath(t, dirs[ndirs])) { fprintf(stderr, "nogmp: REL_NOGMP_OURS directory %s: cannot resolve\n", t); abort(); }
    ndirs++;
  }
  // a process without GMP (lake's children: cc, git, the native program) has nothing to hook
  alloc_ptr = dlsym(RTLD_DEFAULT, "__gmp_allocate_func");
  realloc_ptr = dlsym(RTLD_DEFAULT, "__gmp_reallocate_func");
  if (!alloc_ptr || !realloc_ptr) { alloc_ptr = 0; return; }
  orig_alloc = *alloc_ptr; orig_realloc = *realloc_ptr;
  *alloc_ptr = my_alloc; *realloc_ptr = my_realloc;
  if (!abort_mode) atexit(summary);
}
