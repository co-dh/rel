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
SQL     := sqlite3 -readonly $(DB)
# prints the gate's wall time when it ends, pass or fail
GATE     = SECONDS=0; trap 'echo "[$@] $$SECONDS s, exit $$?"' EXIT; mkdir -p $(T)

# cheapest first: compile-diff takes minutes, so a gate that fails in seconds is reported before it starts
GATES_LIST := build crate-test syms native ldd index-complete axioms noreduce panic externs compile-diff
.PHONY: check main-only index panic-allow $(GATES_LIST)
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

# compile agrees with the code rel_program generated, on every closed definition of every registered program
compile-diff: main-only
	$(GATE)
	CAP_MEM_MB=$(MEM) $(CAP) $(LAKE) build TestCompile

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
	rm -rf $(T)/nat; mkdir -p $(T)/nat/lean/out $(T)/nat/native/out
	$(LAKE) exe relc plan $(T)/nat/lean
	cd $(T)/nat/native; $(NATIVE)
	for f in key val; do cmp $(T)/nat/lean/out/$$f $(T)/nat/native/out/$$f; done

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

# every @[extern] name declared in RelKernel is defined in librelk.a
externs:
	$(GATE)
	$(LAKE) build RelKernel gates
	$(LAKE) query RelKernel:modules | xargs $(LAKE) env $(GATES) externs > $(T)/extern.tsv
	cut -f1 $(T)/extern.tsv | sort -u > $(T)/extern.names
	nm -g --defined-only --format=just-symbols $(RELKA) | sort -u > $(T)/relk.defined
	comm -23 $(T)/extern.names $(T)/relk.defined > $(T)/extern.missing
	if [ -s $(T)/extern.missing ]; then echo "extern names with no definition in $(RELKA):"; grep -F -f $(T)/extern.missing $(T)/extern.tsv; exit 1; fi
