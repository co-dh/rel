# `make check` runs every gate, one target each; a failing gate prints the offending declarations or symbols and exits
# non-zero, and the targets after it do not run. Each gate builds only what it reads (the index gates need the index,
# not a rebuild). `make panic-allow` regenerates panic-allow.txt from the index; read the diff before committing it.
SHELL        := /bin/bash
# one shell per recipe, so the timing trap below covers the whole gate; -e stops at the first failing command
.ONESHELL:
.SHELLFLAGS  := -eu -o pipefail -c
.NOTPARALLEL:
export LC_ALL := C
export CARGO_TARGET_DIR ?= /data/tmp/relk/target/$(notdir $(CURDIR))

CAP     := /home/dh/repo/freyd/scripts/cap
LR      := /home/dh/repo/lean-refactor/scripts/lean-refactor
MEM     := 20000
LAKE    := lake -d $(CURDIR)
# lib `Rel` lists its modules by reading `Rel/` at configure time (`restRoots`) and lake caches that list in .lake/config,
# so a module added, renamed or deleted under Rel/ needs `lake -R` (2 s a call); `CONF` reconfigures once when the
# set of module files differs from the one the last reconfigure saw, instead of on every lake call
MODHASH := $(CURDIR)/.lake/rel-modules.hash
CONF     = h=$$(find $(CURDIR)/Rel -name '*.lean' | sort | sha256sum | cut -c1-64); if [ ! -f $(MODHASH) ] || [ "$$h" != "$$(cat $(MODHASH))" ]; then lake -R -d $(CURDIR) query RelCore:modules > /dev/null; echo "$$h" > $(MODHASH); fi
DB      := $(CURDIR)/.lake/build/refactor-index.db
T       := /data/tmp/rel-gates/$(notdir $(CURDIR))
GATES   := $(CURDIR)/.lake/build/bin/gates
RELC    := $(CURDIR)/.lake/build/bin/relc
RELKA   := $(CURDIR)/.lake/build/lib/librelk.a
QRT     := $(CURDIR)/.lake/build/native/cargo/qrt.o
SQL     := sqlite3 -readonly $(DB)
# prints the gate's wall time when it ends, pass or fail
GATE     = SECONDS=0; trap 'echo "[$@] $$SECONDS s, exit $$?"' EXIT; mkdir -p $(T); $(CONF)
# $(call UNCHANGED,gate,inputs): exit the recipe (as passed) when the hash of the command `inputs` prints equals the one
# the gate's last pass recorded; PASSED records it, so a failed run leaves no record and runs again
UNCHANGED = h=$$( { $(2); } | sha256sum | cut -c1-64); if [ -f $(T)/$(1).pass ] && [ "$$h" = "$$(cat $(T)/$(1).pass)" ]; then echo "$(1): inputs unchanged since its last pass ($$h)"; exit 0; fi
PASSED    = echo "$$h" > $(T)/$(1).pass

# cheapest first: compile-diff takes minutes, so a gate that fails in seconds is reported before it starts
GATES_LIST := build pc9-time allcov crate-test syms tags native ldd index-complete axioms noreduce panic bang pointfree decode listban kernel-tested externs compile-diff
.PHONY: check main-only nogmp bench indexpanic-allow bang-allow pointfree-allow decode-allow listban-allow kernel-tested-allow $(GATES_LIST)
check: main-only $(GATES_LIST)
	$(GATE)
	echo "make check: every gate passed"

# A target that builds the whole package runs once, in the main checkout before the merge; a linked worktree builds
# only the modules it edited, because every Rel.Kernel module has most of the package downstream of it.
COMMON  = $$(git -C $(CURDIR) rev-parse --path-format=absolute --git-common-dir)
# WORKTREE_CHECK=1 lets a worktree whose .lake was seeded from main's run the gates (e.g. to time `make check`)
main-only:
	if [ -z "$(WORKTREE_CHECK)" ] && [ "$$(git -C $(CURDIR) rev-parse --absolute-git-dir)" != "$(COMMON)" ]; then
	  echo "make $(MAKECMDGOALS): $(CURDIR) is a linked worktree; the main thread runs this in $$(dirname $(COMMON)) before the merge. Here build only the modules you edited and their tests: cap lake build <Mod> <ModTest> ..." >&2
	  exit 1
	fi

# the compile: every #guard and decide pair, 0 error, 0 sorryAx
build: main-only
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build RelCore RelKernel RelRun Rel rel-native

# Rel/Lang/AllPrograms.lean imports every module of Rel/ that defines a rel_program. It reads the oleans of the modules
# that list does not import, so it runs after `build`, never as a library module (lake does not know those reads).
allcov: build
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) lean $(CURDIR)/test/AllCovered.lean

# sudokupc9 (test/Pc9Time.lean) runs within PC9_MS: it went 3 s → 35 s → 12 s through two silent expansions, each
# found only by an investigation. It reads the library `build` made; a `rel: warning: … expanded` line names an expansion.
PC9_MS  := 6000
pc9-time: build
	$(GATE)
	t0=$$(date +%s%N)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) lean $(CURDIR)/test/Pc9Time.lean
	ms=$$(( ($$(date +%s%N) - t0) / 1000000 ))
	echo "pc9-time: sudokupc9 took $$ms ms (budget $(PC9_MS) ms)"
	if [ $$ms -gt $(PC9_MS) ]; then echo "sudokupc9 took $$((ms / 1000)).$$((ms % 1000 / 100)) s > $$(($(PC9_MS) / 1000)) s budget; profile with perf record -g -- $(LAKE) lean $(CURDIR)/test/Pc9Time.lean" >&2; exit 1; fi

# The differential test: each closed definition of every registered program, as the constant rel_program generated
# computes it (`expanded`), is compared with `Tm.code` run on the re-read `Tm` (which `Tm.gen_sound` is about); a
# definition with no code is listed with the nodes that have none. There is no stored baseline.
# A module of lib `RelGate`: its inputs are its source and its imports, all in lake's trace, so lake elaborates it again
# when one of them changed and otherwise replays its log; a failing run writes no trace, so it runs again next time.
compile-diff: main-only
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build RelGate

# size and throughput, outside every gate: lib `RelBench` (Bench/) holds the programs over what a program may cost the
# gate (`gateMs` in test/TestCompile.lean, which fails naming each); building it runs them
bench:
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build RelBench

# inputs: every file of crate/ (sources, testdata, Cargo.lock, rust-toolchain.toml) and the toolchain it selects
crate-test:
	$(GATE)
	$(call UNCHANGED,crate-test,find $(CURDIR)/crate -type f | sort | xargs sha256sum; (cd $(CURDIR)/crate && cargo -V && rustc -vV))
	CAP_MEM_MB=$(MEM) $(CAP) cargo test --manifest-path $(CURDIR)/crate/Cargo.toml --features std
	$(call PASSED,crate-test)

# cargo builds crate/ alone: its defined qlean_* equal crate/RELK.txt (kernels) + crate/RELIO.txt (IO)
syms:
	$(GATE)
	sh $(CURDIR)/crate/build.sh syms

# crate/src/tag.rs, Rust's `Enc` tags, is what `gates tags` generates from Lean's `ctorIdx`
tags:
	$(GATE)
	$(LAKE) build Rel.Kernel.Value gates
	$(LAKE) env $(GATES) tags Rel.Kernel.Value > $(T)/tag.rs
	cmp $(T)/tag.rs $(CURDIR)/crate/src/tag.rs || { echo "tags: crate/src/tag.rs differs from Lean's Enc; regenerate: $(LAKE) env $(GATES) tags Rel.Kernel.Value > crate/src/tag.rs" >&2; diff $(T)/tag.rs $(CURDIR)/crate/src/tag.rs >&2; exit 1; }

# Each program of test/native/progs.txt (`NATIVES`, default all; `make native NATIVES=rel-native` leaves out the rest):
# its out/ from the native executable equals the out/ `relc plan` writes from Lean (`Plan.exec`, the same plan) and the
# out/ `relc run` writes from the program's Lean meaning: the same entries, and each file byte for byte. The obligations
# are the Lean sides' files, so a file the native run left out fails.
NAT     := $(T)/native
PROGS   := $(CURDIR)/test/native/progs.txt
NATIVES ?= $(shell grep -v '^\#' $(PROGS) | awk '{ print $$1 }')
native:
	$(GATE)
	$(LAKE) build relc
	REL_NATIVE='$(NATIVES)' $(LAKE) build rel-native
	rm -rf $(NAT); mkdir -p $(NAT)
	grep -v '^#' $(PROGS) > $(NAT)/progs
	while read -r name mod plan run inp out; do
	  case " $(NATIVES) " in *" $$name "*) ;; *) continue ;; esac
	  d=$(NAT)/$$name; mkdir -p $$d/lean $$d/native $$d/run
	  # the inputs, read relative to each run's directory: a program's own writer, or the files of test/native/in
	  for s in lean native run; do
	    if [ "$$inp" = - ]; then cp -r $(CURDIR)/test/native/in $$d/$$s/; else (cd $$d/$$s; $(LAKE) env $(RELC) run $$mod $$inp); fi
	  done
	  if [ "$$plan" = - ]; then pargs=; else pargs="$$mod $$plan"; fi
	  # `lake env`, not `lake exe`: relc is built above, and `planIO` imports the modules from the LEAN_PATH it sets
	  $(LAKE) env $(RELC) plan $$d/lean $$pargs
	  (cd $$d/native; $(CURDIR)/.lake/build/native/$$name)
	  # the Lean meaning of the program (`run`, not the plan), whose out/ the native one must hold byte for byte
	  (cd $$d/run; $(LAKE) env $(RELC) run $$mod $$run)
	  find $$d/run/$$out -mindepth 1 -printf '%y %P\n' | sort > $$d/run.entries
	  test -s $$d/run.entries || { echo "native $$name: relc run wrote nothing under $$d/run/$$out; it is written by: $(LAKE) env $(RELC) run $$mod $$run, run in $$d/run" >&2; exit 1; }
	  test -d $$d/lean/$$out || { echo "native $$name: no $$d/lean/$$out; it is written by: $(LAKE) env $(RELC) plan $$d/lean $$pargs" >&2; exit 1; }
	  test -d $$d/native/$$out || { echo "native $$name: no $$d/native/$$out; it is written by: $(CURDIR)/.lake/build/native/$$name, run in $$d/native" >&2; exit 1; }
	  find $$d/lean/$$out -mindepth 1 -printf '%y %P\n' | sort > $$d/lean.entries
	  find $$d/native/$$out -mindepth 1 -printf '%y %P\n' | sort > $$d/native.entries
	  test -s $$d/lean.entries || { echo "native $$name: relc plan wrote nothing under $$d/lean/$$out" >&2; exit 1; }
	  cmp $$d/lean.entries $$d/native.entries || { echo "native $$name: the entries of out/ differ (< lean, > native):" >&2; comm -3 $$d/lean.entries $$d/native.entries >&2; exit 1; }
	  find $$d/lean/$$out -type f -printf '%P\n' | sort | xargs -I{} cmp $$d/lean/$$out/{} $$d/native/$$out/{}
	  comm -23 $$d/run.entries $$d/native.entries > $$d/run.missing
	  if [ -s $$d/run.missing ]; then echo "native $$name: entries relc run wrote and the native run did not:" >&2; cat $$d/run.missing >&2; exit 1; fi
	  find $$d/run/$$out -type f -printf '%P\n' | sort | xargs -I{} cmp $$d/run/$$out/{} $$d/native/$$out/{}
	  # the gate plan's own Lean value of each term it outputs (`relc lean`, `writeRel`), not the plan: comparing the plan
	  # only with itself let a converse that skipped `canon` pass; each file the Lean value writes, the native run writes alike
	  if [ "$$plan" = - ]; then
	    mkdir -p $$d/sem/out
	    $(LAKE) env $(RELC) lean $$d/sem
	    find $$d/sem/out -type f -printf '%P\n' | sort > $$d/sem.files
	    test -s $$d/sem.files || { echo "native $$name: relc lean wrote nothing under $$d/sem/out" >&2; exit 1; }
	    xargs -I{} cmp $$d/sem/out/{} $$d/native/$$out/{} < $$d/sem.files
	  fi
	done < $(NAT)/progs

# every native executable needs libc, libm and libpthread only (plus the loader and the vdso)
ldd: native
	$(GATE)
	grep -v '^#' $(PROGS) | awk '{ print $$1 }' | grep -xF -f <(printf '%s\n' $(NATIVES)) | while read -r name; do
	  ldd $(CURDIR)/.lake/build/native/$$name | awk '$$1 !~ /^(linux-vdso\.so|\/lib64\/ld-linux|libc\.so|libm\.so|libpthread\.so)/ { print "ldd '$$name': unexpected " $$0; bad = 1 } END { exit bad }'
	done

# the index is read from built modules and refuses a stale one, so it needs exactly the library targets built
index:
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build RelCore RelKernel RelRun Rel
	CAP_MEM_MB=$(MEM) $(LR) index

# the index gates read `dep`: a module missing from the index would pass them without being read
index-complete: index
	$(GATE)
	find Rel -name '*.lean' | sort > $(T)/src.txt
	$(SQL) "select source from module where source like 'Rel/%'" | sort > $(T)/indexed.txt
	comm -23 $(T)/src.txt $(T)/indexed.txt > $(T)/unindexed.txt
	cat $(T)/unindexed.txt
	test ! -s $(T)/unindexed.txt

# every declaration of Rel.Core.* depends on {propext, Quot.sound} at most
axioms:
	$(GATE)
	$(LAKE) build RelCore gates
	$(LAKE) query RelCore:modules | xargs $(LAKE) env $(GATES) axioms

# `dep` records a use of a constant by the declaration that mentions it, so a missing sorry or reduceBool is an absent row
noreduce: index
	$(GATE)
	$(SQL) "select distinct src || '  (' || module || ') uses ' || dst from dep where dst in ('sorryAx', 'Lean.ofReduceBool') order by 1" > $(T)/noreduce.txt
	cat $(T)/noreduce.txt
	test ! -s $(T)/noreduce.txt

# panic-allow.txt is exactly the set of declarations that mention panicWithPosWithDecl themselves (a caller of one is not
# a panic site); internal=0 leaves out the equation lemmas and matchers derived from a listed declaration
PANICS = select distinct d.src from dep d join decl_info i on i.name = d.src and i.module = d.module where d.dst = 'panicWithPosWithDecl' and i.internal = 0 order by 1
panic: index
	$(GATE)
	$(SQL) "$(PANICS)" > $(T)/panics.txt
	sort -u panic-allow.txt > $(T)/allow.txt
	comm -13 $(T)/allow.txt $(T)/panics.txt | sed 's/^/new panic, not in panic-allow.txt: /' > $(T)/panic-diff.txt
	comm -23 $(T)/allow.txt $(T)/panics.txt | sed 's/^/stale, no longer panics (delete from panic-allow.txt): /' >> $(T)/panic-diff.txt
	cat $(T)/panic-diff.txt
	test ! -s $(T)/panic-diff.txt

panic-allow: index
	$(GATE)
	$(SQL) "$(PANICS)" > panic-allow.txt

# $(T)/$(1).txt, the declarations violating gate $(1) today, against $(1)-allow.txt, each printed with its source line
# from the index: a new one fails, and so does a listed one that no longer violates, so the list only shrinks
define ALLOWED
$(SQL) "select i.name, coalesce(m.source || ':' || (r.sl1 + 1), m.source) from decl_info i join module m on m.name = i.module left join decl_range r on r.name = i.name and r.module = i.module" | sort -t'|' -k1,1 > $(T)/loc.txt
sort -u $(1)-allow.txt > $(T)/$(1).allow
comm -13 $(T)/$(1).allow $(T)/$(1).txt | join -t'|' -a1 - $(T)/loc.txt | sed 's/^/$(1): new, not in $(1)-allow.txt: /' > $(T)/$(1).diff
comm -23 $(T)/$(1).allow $(T)/$(1).txt | join -t'|' -a1 - $(T)/loc.txt | sed 's/^/$(1): stale, no longer violates (delete from $(1)-allow.txt): /' >> $(T)/$(1).diff
cat $(T)/$(1).diff
if [ -s $(T)/$(1).diff ]; then echo "$(1): fix the new ones; after a fix, regenerate the list with: make -C $(CURDIR) $(1)-allow"; exit 1; fi
endef

# every package module, for the gates that read the whole package's environment
MODS = $(LAKE) query RelCore:modules RelKernel:modules RelRun:modules Rel:modules
# no `!` indexing: a written def or opaque whose code (its value and the auxiliaries it owns) reaches a constant named
# `…!` declared outside the package, Lean's convention for the variant that panics (gates/Gates.lean `panicking`)
define bang_NOW
$(LAKE) build gates
$(MODS) | xargs $(LAKE) env $(GATES) bang | sort -u > $(T)/bang.txt
endef
# no points in the body of a relation: a written def whose result type, unfolding reducible abbreviations only, is headed by
# a relation type (gates/Gates.lean `relTypes`) or built from one, and whose body is written over points (a `fun` returning a
# proposition or a `∀`/`→` proposition: gates/Gates.lean `pointwise`, so `∃`, `∀`, `¬`, `∧` of points); theorems are exempt
define pointfree_NOW
$(LAKE) build gates
$(MODS) | xargs $(LAKE) env $(GATES) pointfree | sort -u > $(T)/pointfree.txt
endef
# no element decode in Lean on the run path: a compiled declaration of RelRun whose code, followed through the IR (an
# @[extern] a call, an @[implemented_by] its implementation), reaches a per-element reader (gates/Gates.lean `decoders`);
# the chain from each to the reader is in $(T)/decode.chains. A name of decode-allow.txt is a leaf of the walk, so only
# a path through no listed name flags a declaration; a listed one that no longer reaches a reader itself is stale
define decode_NOW
$(LAKE) build RelRun gates
$(LAKE) query RelRun:modules | xargs $(LAKE) env $(GATES) decode 2> $(T)/decode.chains | sort -u > $(T)/decode.txt
endef
# every export, an @[extern] declaration whose symbol crate/RELK.txt or crate/RELIO.txt lists, is mentioned (index `use_site`: a
# declaration, `#guard` or `example`) in a module whose name matches *Test*; loops over the kernels, not the tests
define kernel-tested_NOW
$(LAKE) build gates
$(LAKE) query RelKernel:modules | xargs $(LAKE) env $(GATES) externs | sort -t$$'\t' -k1,1 > $(T)/kt-extern.tsv
sort -u crate/RELK.txt crate/RELIO.txt | join -t$$'\t' -o 1.2 $(T)/kt-extern.tsv - | sort -u > $(T)/kernels.txt
$(SQL) "select distinct name from use_site where use_module glob '*Test*'" | sort -u > $(T)/tested.txt
comm -23 $(T)/kernels.txt $(T)/tested.txt > $(T)/kernel-tested.txt
echo "kernel-tested: $$(wc -l < $(T)/kernel-tested.txt) of $$(wc -l < $(T)/kernels.txt) kernels have no use in a *Test* module"
endef

# no List on the run path: a compiled declaration of Rel.Run.*, Rel.Kernel.* (not *Test*) or Rel.Lang.GenK* whose code, followed
# through the IR as `decode` does, reaches a reader turning an array into a List or `List.range` (gates/Gates.lean `listBan`);
# an @[extern] declaration's Lean body is a specification, never compiled, so it is not walked
define listban_NOW
$(LAKE) build gates
$(LAKE) query RelKernel:modules RelRun:modules Rel:modules | tr ' ' '\n' | grep -E '^Rel\.(Run|Kernel|Lang\.GenK)' | grep -v 'Test\|Rel.Run.Lang.EmitC' | xargs $(LAKE) env $(GATES) listban 2> $(T)/listban.chains | sort -u > $(T)/listban.txt
endef

bang: index
	$(GATE)
	$(bang_NOW)
	$(call ALLOWED,bang)

listban: index
	$(GATE)
	$(listban_NOW)
	$(call ALLOWED,listban)

pointfree: index
	$(GATE)
	$(pointfree_NOW)
	$(call ALLOWED,pointfree)

decode: index
	$(GATE)
	$(decode_NOW)
	$(call ALLOWED,decode)

kernel-tested: index
	$(GATE)
	$(kernel-tested_NOW)
	$(call ALLOWED,kernel-tested)

# regenerate an allowlist from what violates today; read the diff before committing it
bang-allow pointfree-allow decode-allow listban-allow kernel-tested-allow: %-allow: index
	$(GATE)
	$($*_NOW)
	cp $(T)/$*.txt $*-allow.txt

# no GMP from this package's code: every *Test* module under Rel/ is elaborated with test/nogmp/nogmp.c preloaded,
# which aborts on a GMP allocation whose stack holds a frame of a shared library under .lake/build/lib (a precompiled
# module), except in a module initializer (a closed term computed once at load, listed); Lean's own GMP use (elaborator,
# kernel, interpreter) is only counted. Every test module elaborates the package, so this runs in the main checkout.
# The native program links no GMP at all (crate/rt aborts in lean_big_usize_to_nat), so its run is `native`
NOGMP   := $(CURDIR)/.lake/build/nogmp/libnogmp.so
# `make nogmp NOGMP_MODE=log` lists every site with its count instead of stopping at the first
NOGMP_MODE ?= abort
$(NOGMP): $(CURDIR)/test/nogmp/nogmp.c
	mkdir -p $(dir $@)
	cc -O2 -Wall -Werror -shared -fPIC -o $@ $< -ldl -lpthread
nogmp: main-only $(NOGMP) native
	$(GATE)
	grep -v "^#" $(PROGS) | awk "{ print \$$1 }" | grep -xF -f <(printf "%s\n" $(NATIVES)) | sed "s,^,$(CURDIR)/.lake/build/native/," | xargs nm > $(T)/nogmp.nm
	if grep ' __gmp' $(T)/nogmp.nm >&2; then echo "nogmp: a native executable links GMP (above)" >&2; exit 1; fi
	find $(CURDIR)/Rel -path "*Test*" -name "*.lean" | sort > $(T)/nogmp.tests
	test -s $(T)/nogmp.tests || { echo "nogmp: no *Test* module under $(CURDIR)/Rel" >&2; exit 1; }
	xargs -I{} env REL_NOGMP=$(NOGMP_MODE) REL_NOGMP_OURS=$(CURDIR)/.lake/build/lib LD_PRELOAD=$(NOGMP) \
	  CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) lean {} < $(T)/nogmp.tests

# every @[extern] name declared in RelKernel is defined in what a native program links: librelk.a (the kernels) or
# qrt.o (the Lean runtime symbols crate/rt provides, e.g. lean_array_push)
externs:
	$(GATE)
	$(LAKE) build RelKernel gates rel-native
	$(LAKE) query RelKernel:modules | xargs $(LAKE) env $(GATES) externs > $(T)/extern.tsv
	cut -f1 $(T)/extern.tsv | sort -u > $(T)/extern.names
	nm -g --defined-only --format=just-symbols $(RELKA) $(QRT) | sort -u > $(T)/relk.defined
	comm -23 $(T)/extern.names $(T)/relk.defined > $(T)/extern.missing
	if [ -s $(T)/extern.missing ]; then echo "extern names with no definition in $(RELKA) or $(QRT):"; grep -F -f $(T)/extern.missing $(T)/extern.tsv; exit 1; fi
