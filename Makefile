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
# -R: lib `Rel` lists its modules by reading `Rel/` at configure time and lake caches that list in .lake/config,
# so a renamed or deleted module stays listed until reconfigure (about 1 s)
LAKE    := lake -R -d $(CURDIR)
DB      := $(CURDIR)/.lake/build/refactor-index.db
T       := /data/tmp/rel-gates/$(notdir $(CURDIR))
GATES   := $(CURDIR)/.lake/build/bin/gates
NATIVE  := $(CURDIR)/.lake/build/native/rel-native
RELKA   := $(CURDIR)/.lake/build/lib/librelk.a
QRT     := $(CURDIR)/.lake/build/native/cargo/qrt.o
SQL     := sqlite3 -readonly $(DB)
# prints the gate's wall time when it ends, pass or fail
GATE     = SECONDS=0; trap 'echo "[$@] $$SECONDS s, exit $$?"' EXIT; mkdir -p $(T)

# cheapest first: compile-diff takes minutes, so a gate that fails in seconds is reported before it starts
GATES_LIST := build crate-test syms native ldd index-complete axioms noreduce panic bang pointfree kernel-tested externs compile-diff
.PHONY: check main-only index compile-diff-write panic-allow bang-allow pointfree-allow kernel-tested-allow $(GATES_LIST)
check: main-only $(GATES_LIST)
	$(GATE)
	echo "make check: every gate passed"

# A target that builds the whole package runs once, in the main checkout before the merge; a linked worktree builds
# only the modules it edited, because every Rel.Kernel module has most of the package downstream of it.
COMMON  = $$(git -C $(CURDIR) rev-parse --path-format=absolute --git-common-dir)
main-only:
	if [ "$$(git -C $(CURDIR) rev-parse --absolute-git-dir)" != "$(COMMON)" ]; then
	  echo "make $(MAKECMDGOALS): $(CURDIR) is a linked worktree; the main thread runs this in $$(dirname $(COMMON)) before the merge. Here build only the modules you edited and their tests: cap lake build <Mod> <ModTest> ..." >&2
	  exit 1
	fi

# the compile: every #guard and decide pair, 0 error, 0 sorryAx
build: main-only
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build RelCore RelKernel RelRun Rel rel-native

# A regression pin, not a correctness check: each closed definition of every registered program, as the constant
# rel_program generated computes it (`expanded`), has the status and set of rows test/compile-diff.json pins, by name.
# The pin is an earlier run's output, so red means changed, green not right. The same run is the differential test:
# each definition with no `Tm.gap` node also run as `Tm.code` (which `Tm.gen_sound` is about), and must agree.
# `lake lean` builds the imports only and elaborates the gate every time: an olean would survive a new pin.
compile-diff: main-only
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) lean $(CURDIR)/test/TestCompile.lean

# re-pins test/compile-diff.json to the current run; read the diff before committing it, since nothing else checks it
compile-diff-write: main-only
	$(GATE)
	REL_COMPILE_DIFF_WRITE=1 CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) lean $(CURDIR)/test/TestCompile.lean

crate-test:
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) cargo test --manifest-path $(CURDIR)/crate/Cargo.toml --features std

# cargo builds crate/ alone: its defined qlean_* equal crate/RELK.txt
syms:
	$(GATE)
	sh $(CURDIR)/crate/build.sh syms

# out/key and out/val of the native executable equal what `relc plan` writes from Lean
native:
	$(GATE)
	$(LAKE) build relc rel-native
	rm -rf $(T)/nat; mkdir -p $(T)/nat/lean $(T)/nat/native
	$(LAKE) exe relc plan $(T)/nat/lean
	cd $(T)/nat/native; $(NATIVE)
	diff -r $(T)/nat/lean/out $(T)/nat/native/out

# the native executable needs libc, libm and libpthread only (plus the loader and the vdso)
ldd: native
	$(GATE)
	ldd $(NATIVE) | awk '$$1 !~ /^(linux-vdso\.so|\/lib64\/ld-linux|libc\.so|libm\.so|libpthread\.so)/ { print "ldd: unexpected " $$0; bad = 1 } END { exit bad }'

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
# no ∃ in the body of a relation: a written def whose result type, unfolding reducible abbreviations only, is headed by
# a relation type (gates/Gates.lean `relTypes`) or built from one, and whose code mentions `Exists`; theorems are exempt
define pointfree_NOW
$(LAKE) build gates
$(MODS) | xargs $(LAKE) env $(GATES) pointfree | sort -u > $(T)/pointfree.txt
endef
# every kernel, an @[extern] declaration whose symbol crate/RELK.txt lists, is mentioned (index `use_site`: a
# declaration, `#guard` or `example`) in a module whose name matches *Test*; loops over the kernels, not the tests
define kernel-tested_NOW
$(LAKE) build gates
$(LAKE) query RelKernel:modules | xargs $(LAKE) env $(GATES) externs | sort -t$$'\t' -k1,1 > $(T)/kt-extern.tsv
sort -u crate/RELK.txt | join -t$$'\t' -o 1.2 $(T)/kt-extern.tsv - | sort -u > $(T)/kernels.txt
$(SQL) "select distinct name from use_site where use_module glob '*Test*'" | sort -u > $(T)/tested.txt
comm -23 $(T)/kernels.txt $(T)/tested.txt > $(T)/kernel-tested.txt
echo "kernel-tested: $$(wc -l < $(T)/kernel-tested.txt) of $$(wc -l < $(T)/kernels.txt) kernels have no use in a *Test* module"
endef

bang: index
	$(GATE)
	$(bang_NOW)
	$(call ALLOWED,bang)

pointfree: index
	$(GATE)
	$(pointfree_NOW)
	$(call ALLOWED,pointfree)

kernel-tested: index
	$(GATE)
	$(kernel-tested_NOW)
	$(call ALLOWED,kernel-tested)

# regenerate an allowlist from what violates today; read the diff before committing it
bang-allow pointfree-allow kernel-tested-allow: %-allow: index
	$(GATE)
	$($*_NOW)
	cp $(T)/$*.txt $*-allow.txt

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
