This repository is the Rel language: a relation-algebra programming language, its Lean model and proofs, and the Rust
kernels its programs run on. It was split out of freyd's `leetq/` and qlean's `QLean/RelPart` + `rust/relk`
(`doc/` holds the design history; freyd keeps `doc/rel-repo-split-design.md`).

## Layout
- `Rel/Core/` — the concrete allegory core: `Rel α β` a predicate on pairs, its operators, `mu`/`nu`. Toolchain only.
- `Rel/Kernel/` — each kernel as one `@[extern "qlean_…"] def` whose Lean body is its specification; `Column`,
  `QAtom` (`Value`). `Rel/KernelSpec/` — the lemmas about them that the rest cites.
- `Rel/Run/` — what `rel_program` runs at elaboration time: the expander, the code it emits, their imports.
- `Rel/` (everything else) — `CRel*`/`Rep*` laws, `KernelWF`, `Lang` (denotation, plan, C emitter, tests),
  `Programs` (the `.rel` programs), tests.
- `crate/` — the Rust crate `relk`: the kernels the externs name (`RELK.txt` lists its exports). `crate/rt/` — the
  Lean runtime a native Rel program links instead of `libleanshared` (a package of its own).
- Lake libraries (`lakefile.lean`): `RelCore`, `RelKernel` (precompiled; `Rel.Kernel.*` + `Rel.KernelSpec.*`),
  `RelRun` (precompiled), `Rel` (the rest, read from the directory). `extern_lib relk` builds `crate/` with
  `crate/build.sh`. `lean_exe relc` prints a plan as C; `target rel-native` links it with `librelk.a` and `qrt.o`.
- No `require`. Lean namespaces say nothing about qlean or freyd: qlean `require`s this package and names `Rel.*`;
  freyd's bridge (`relaop/`) ties `Rel.Core` to freyd's `RelSet` by `rfl`.

## What RelRep is
- The core: a relation is a pair of typed arrays of one length, `Rel k v = {n, key : Arr k n, val : Arr v n}`.
  An `Arr` is a `Column` of one `QAtomicType`, `general` (q's type 0, each element boxed) included. The key
  is a plain `Arr`, as in q.
- `Arr` is the implementation and Lean's `List` is for proofs only: every compiled op builds and reads arrays,
  and a `List` appears only in a statement or a `#guard` (`toList`, `El`), because Lean has the lemmas for `List`
  and not for arrays. `Obj.arr` is the side whose cell is an array (`lo`, `hi` into one flat payload); it is not
  Lean's `List`.
- The algebra on it: composition `≫`, converse `°`, `∩`, `∪`, `⊑`, `𝟘`, `⊤`, `𝟙`, left/right/symmetric
  division, `Λ` and `∋`, pair `⟨R,S⟩` and product, sum `[R,S]`, fold `⦇e,f⦈`, hylo, functors `F(R)`, natural
  and lax natural transformations (`∋`, `est`, `thin`), maps on positions, and `where` (q's `where`: a set of positions
  numbered in position order, the one place row order enters; not `Enc.enum`, the symbol dictionary encoding).

## Goal
Rel is a programming language of its own, not an implementation of k or q:
- A program is written in the algebra above — a composition of a few executable Rel primitives — and runs as
  written. kdb/q semantics that no Rel program uses are removed, not kept or re-implemented.
- Only the primitives are kernels (`crate/`): `scan` and `scatter`, with `gather`, `asc` and `seen` as
  optimisations. A fused kernel for a pattern of primitives is an optimisation, tied to the pattern by a theorem.
- Execution is compute-on-compression (encoded columns), so it is also efficient: memory IO is the speed limit.
- No serialization: the in-memory structure is the on-disk structure, so loading an array is an mmap.

## Rules
- **Documents in `doc/` are written in Chinese** — a design note is a `.zh.typ` styled after
  `doc/rel-architecture.zh.typ`, compiled to PDF, because he reads them in Chinese; code, identifiers, comments,
  commit messages and technical terms stay English.
- **`doc/rel-architecture.zh.typ` is THE design; read it before any design question, dispatch or new operator** —
  §0 the runtime types (`Rel = tab | lazy`, `Known`), §1 the `Tm` constructor groups, §4 the table
  "allegory 运算 → kernel" (each operation's composition of the five kernels), §7 what becomes a prelude definition.
  Where code and that document differ, say so and ask; never propose a second design beside it, because a
  design invented without reading it has been rejected each time.
- **Notation follows freyd's.** Composition in diagram order by juxtaposition or `≫` (`R ≫ S`: first `R`, then `S`);
  applying an operator takes parentheses (`F(R)`, `thin(Q)`, `f(a)`); a converse with a name of its own is written by
  that name (`≥`, not `≤°`; `∈`, not `∋°`).
- **A spec is a composition of relations first** — before writing or shortening a program, say which relations it
  composes; definition bodies are point-free (no `∃` in a body), because a pointwise body hides the composition the
  laws are about.
- **Constructive in `Rel.Core` only** — its axioms stay within `{propext, Quot.sound}`, so the core holds in every
  allegory freyd's bridge maps it to. The rest uses `Classical` freely (`Column.atoms`, `Classical.propDecidable`).
- **No `sorry`, `native_decide`, `!` indexing, raised `maxHeartbeats`, and no new `panic!`** — a `panic!` already in
  the tree is on the allowlist until removed, and the gate refuses any other.
- **A kernel computes on the encoded column, never on a decoded copy** — it reads the foR blocks (frame, width,
  patches) and their per-block metadata directly and writes encoded output, because decoding to full words and
  encoding back costs more than the operation itself and throws away the speed the encoding exists to buy. A
  kernel that decodes needs his approval first: ask him, stating why the answer cannot be computed per block, and
  record the approval in its doc comment.
- **A kernel is one declaration**: the `@[extern]` def and its Lean model are the same `def`, and its `decide`
  beside `#guard` pair is the only check that the Rust agrees with the body. Never restate a body by cases.
- **Find a declaration with the index**, never by grepping `*.lean`: `./scripts`-less here, so run
  `/home/dh/repo/lean-refactor/scripts/lean-refactor index` in this checkout and query `.lake/build/refactor-index.db`
  (`decl_info`, `module`, `decl_range`; keep `internal = 0`).
- **Renames go through `lean-refactor`** (`rename`, `move`); after each, query the index for a doubled namespace
  (`Rel.Rel.` other than the structure `Rel.Rel` and its fields, `Rel.LeetQ.`, `Rel.QLean.`).
- **Search before creating a type** — a `Rel k v`, `RelRep`, `FinRel` or `Column` twin is the duplicate this
  repository was split to avoid; extend the one that exists.
- **DRY**: one authoritative definition per fact; a stronger theorem with the weaker by specialisation.
- Build under the memory cap: `CAP_MEM_MB=20000 /home/dh/repo/freyd/scripts/cap lake build RelCore RelKernel RelRun Rel`.
  Name the targets; a worktree builds only the modules it edited. Temporary files go under `/data/tmp`.

## Gates
- `lake build RelCore RelKernel RelRun Rel` green: every `#guard` and `decide` pair, 0 `error`, 0 `sorryAx`.
- `sh crate/build.sh syms`: `cargo build` of `crate/` alone defines exactly the `qlean_*` of `crate/RELK.txt`.
- `lake build rel-native`, then run `.lake/build/native/rel-native` in a directory holding an empty `out/`: `out/key` and `out/val`
  equal to what `lake exe relc plan DIR` writes from Lean.
