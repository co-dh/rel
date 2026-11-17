/* The count of the blocks the Rust runtime (rust/rt, `build.sh rt`) holds. `build.sh rt` also writes qrt-count.o: qrt.o
   with its `malloc` and `free` renamed `qrt_malloc` and `qrt_free`, which this file defines as the libc calls plus a
   counter. The runtime makes and frees every object of a link without Lean (lean.rs and lean.h allocate through it too).
   The Lean-level differential (phase-2 §2.8) and test/abi.c read `qlean_rt_live()` before and after a call: an owned
   argument leaked or a borrowed one freed moves it. Link this file and qrt-count.o in place of qrt.o. */
#include <stdlib.h>

static long rtc_live;
void *qrt_malloc(size_t n) { void *p = malloc(n); if (p) rtc_live++; return p; }
void qrt_free(void *p) { if (p) rtc_live--; free(p); }

long qlean_rt_live(void) { return rtc_live; }
