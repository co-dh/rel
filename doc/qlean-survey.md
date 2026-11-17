# qlean survey for freyd's finite-relation library

Read-only survey, 2026-10-11, of qlean at commit `a12c600` (2026-10-09, "Merge amend as gather, whole-column map
and scatter …"), with 6 uncommitted files in the working tree. Written so a freyd agent deciding whether qlean's
compressed arrays can back `AOP/A6_FinRel.lean`'s `SortedRel` does not have to re-read qlean. Line numbers come
from `.lake/build/refactor-index.db` at that commit or from the file itself; the index runs about 60 lines behind
`QLean/Value.lean`, so treat a line as a pointer and the declaration name as the anchor.

## 1. What qlean is

A Lean 4 type checker, evaluator and column store for kdb+/q (`README.md`, `AGENTS.md`, `PLAN.md`). The part that
matters for freyd is the column store: `QLean/Value.lean` (`Column`), `QLean/Kernel/*.lean` (one Lean module per
C kernel family) and `c/*.c` (the kernels). `CLAUDE.md` records the standing decisions: compression is the only
representation, never box a whole column, every whole-column operation is one C call.

## 2. The `Column` type (`QLean/Value.lean`, `inductive Column`, index line 195)

The payload is UNTYPED. The element type is a runtime tag `QAtomicType` carried by `QValue.vector t c`; every
read takes that tag. K and V can only be q's atomic types (`long` = Int64, `int`, `short`, `float`, `symbol`, …),
never a Lean type parameter.

| ctor                                  | layout                                                                  |
|---------------------------------------|-------------------------------------------------------------------------|
| `bytes : ByteArray`                   | dense little-endian fixed width, byte-identical to q's wire and splayed  |
| `bits : (count : Nat) → ByteArray`    | booleans, one bit each, LSB first                                        |
| `syms : (blob : ByteArray) → (offs : Array Nat)` | NUL-joined UTF-8 symbols plus n+1 start offsets              |
| `foR : (count : Nat) → (metadata pack : ByteArray)` | Frame of Reference: 1024-element blocks, 33 B metadata per block (base, max, offset, block sum, width) + 16 B trailer (null, count), residuals bit-packed at the block's width |
| `alp : …`                             | floats as decimal integers per block over `foR`'s parts, exceptions raw  |

Readers, all pure Lean, no FFI: `Column.atoms t c : Array QAtom` (boxes every element — banned on hot paths by
`CLAUDE.md`), `Column.get t c i : Option QAtom` (O(1), on `foR` through `Column.foRBits`), `Column.count`,
`Column.bitsAt`/`pushBits` (the one byte reader/writer), `Column.blockStarts`/`resAt`/`baseAt`/`widthAt` (the
`foR` denotation). Writers: `Column.ofAtoms t as : Option Column` (dense), `Column.symsOf`, `Column.packBits`.
There is NO `toList`/`toArray` abstraction with operation lemmas; `atoms` is the only denotation.

## 3. Kernels: where each operation lives

Every family is one Lean module whose `@[extern]` defs name a C file; the C file's `LEAN_EXPORT` line is given.

| family     | Lean module (lines)                   | declarations                                              | C entry (`c/`)                                                          |
|------------|---------------------------------------|-----------------------------------------------------------|--------------------------------------------------------------------------|
| encode     | `QLean/Kernel/Coc.lean` (633)         | `Coc.encode` (`qlean_coc_encode`, ~l.108), `blockOf`, `packRes`, `foRMeta`, decode | `coc.c:538` encode, `:553` decode, `:600` over, `:620` count_lt, `:671` mask_cmp; kernels in `coc.h` |
| search     | `QLean/Kernel/Search.lean` (1232)     | `binStep` l.218 (spec of q `bin`/`binr`), `binBytes` l.231, `findScalar` l.85, `findVec` l.94, `memberVec` l.104, `findBit` l.121, `whereBits` l.148, `findColumn` l.263, `binColumn` l.310, `memberColumn` l.334, `whereColumn` l.370 | `search.c:1427` bin, `:1472` coc_bin, `:1571` find_sorted, `:1600` coc_find_sorted, `:1613` coc_member_sorted, `:266` find_scalar, `:584` find_vec, `:606` member_vec, `:877` where_bits |
| sort/group | `QLean/Kernel/Sort.lean` (1056)       | `Order.ascending` l.142 (is-sorted), `Order.grade` l.157, `Order.distinct` l.180, `Order.group` l.191, `gradeColumn` l.284, `sortedColumn` l.297, `distinctColumn` l.317, `groupColumn` l.342 | `sort.c:784` ascending, `:867` ascending_foR, `:912` grade, `:935` grade_foR, `:1952` distinct, `:2006` group, `:2042` group_ids, `:2117` distinct_foR, `:2133` group_foR |
| scan       | `QLean/Kernel/Scan.lean` (822)        | q `sums`/`prds`/`mins`/`maxs`/`fills`, `ema`, moving windows | `scan.c:483` scan, `:563` scan_foR, `:594` scan_alp, `:1136` mwin                    |
| gather     | `QLean/Kernel/Structural.lean` (1273) | gather/scatter/reverse/concat/shift/til, amend              | `structural.c:663` gather, `:741` gather_foR, `:1475` concat, `:1642` til, `:2096` scatter, `:2206` scatter_for |
| reduce     | `QLean/Kernel/Reduce.lean` (663)      | `overBytes` (q `+/ */ &/ |/`), `overGroups`                  | `reduce.c:262` over_bytes, `:427` over_groups, `:717` over_f64                        |
| elementwise| `QLean/Kernel/Elementwise.lean` (2085)| dyadic/monadic maps, compare masks, casts                   | `elementwise.c:517` ew_val, `:595` coc_ew_val, `:840` ew_cmp                          |

Table-level joins exist at `QLean/Dep/EquiJoin.lean` (`EquiJoin.ej`), `QLean/Dep/InnerJoin.lean` (`InnerJoin.ij`),
`QLean/Dep/KeyedJoin.lean`, `QLean/Dep/AsofJoin.lean` — over schema-indexed `QValue` tables, not typed K/V.
Binary search on the compressed form exists in C (`qlean_coc_bin`, `qlean_coc_find_sorted`); its Lean spec decl
was not located in the index.

Complexity: one C call per whole-column operator (`PLAN.ckernel.md` §3.1: per-element FFI is forbidden); `bin`
is O(log n) per key; `min`/`max`/`sum` on `foR` read block metadata only; `ascending` is one early-exit pass.

## 4. How a kernel is specified, and where the trust is (`PLAN.ckernel.md` §3.2)

```lean
@[extern "qlean_search_bin"]
def binBytes (w : USize) (float signed right : Bool) (hay : @& ByteArray) (keys : @& ByteArray) : ByteArray :=
  … binStep … -- the Lean body IS the specification; the C function is the implementation
```

- The kernel (`decide`, `rfl`, every proof in `QLean/Verify/`) unfolds the Lean body. The interpreter and the
  compiled binary call the C. So `#print axioms` CANNOT see a Lean/C disagreement: the plan demonstrates a C
  `3*n` against a Lean `2*n` with `'double_spec' does not depend on any axioms`.
- The checks on that hole: `QLean/Kernel/Test.lean` pairs `example : … := by decide` (kernel → Lean body) with
  `#guard …` (interpreter → C) on the same sample; this needs `precompileModules := true`. The far-side check is the
  differential corpus `./.lake/build/bin/qlean-test` against a live q 4.1, which needs an on-demand `kc.lic` and
  therefore network access to the KX licence daemon at every start.
- `opaque` was rejected deliberately: it would make the trust visible but erase the body `Verify/` reads.

## 5. Proved versus open

| proved                                                                                   | where                                   |
|------------------------------------------------------------------------------------------|-----------------------------------------|
| `atoms_ofAtoms` (write dense/bits/syms/guid atoms, read back the same), per-ctor variants | `Value.lean` ~l.798, 1022, 1144, 1421, 1446 |
| `atoms_type : ∀ a ∈ atoms t c, a.type = t` with NO hypothesis; `count_atoms`; `atoms_dense` | `Value.lean` ~l.1461, 1481, 1493        |
| `bitsAt_pushBits8`, `blockStarts_fold`, `blockStarts_get` — the byte level of the encoding  | `QLean/Verify/Encoding.lean` (97 lines)  |
| shape of kernel answers only: `findColumn_vec : ∃ c', v = .vector .long c'`, `gradeColumn_type`, `groupColumn_type`, `memberColumn_type`, `whereColumn_type` | `Kernel/Search.lean` l.380–407, `Kernel/Sort.lean` l.366–391 |
| evaluator typing soundness (`find_sound`, take/drop, join/dict/cast, monadic, store)        | `QLean/Verify/*.lean` (~300 theorems)   |

Open: the `foR` round trip `Column.atoms t (Column.encode t c) = Column.atoms t c` — `Verify/Encoding.lean`'s
header names it as the obligation and lists what is still missing (`blockStarts`, `resAt`, `foRBits` against
`packRes`/`blockOf`). No theorem says `binBytes` answers the least index with `k ≤ hay[i]`, that `grade` is a
sorting permutation, that `ascending = true` means sorted, or that `group` groups. `Column.encode`'s doc states the
round trip; `Kernel/Test.lean` checks it by `#guard` on one sample.

## 6. Axioms

`QLean/Verify/Find.lean` guards `find_sound` at `[propext, Classical.choice, Quot.sound]`. `Classical.choice`
enters through `Column.atoms`'s symbol branch: core's `String.fromUTF8?` uses the nonconstructive
`String.validateUTF8`. Any statement that unfolds `Column.atoms`, even at `.long`, inherits it.

## 7. Toolchain and build

| fact                 | value                                                                                          |
|----------------------|------------------------------------------------------------------------------------------------|
| toolchain            | `leanprover/lean4:v4.28.0` (same as freyd); no `require`s (`lake-manifest.json` is empty)         |
| lakefile             | `lakefile.lean` (not TOML: TOML cannot declare an `extern_lib`); `lean_lib QLean` globbed, `precompileModules := true` |
| C                    | `extern_lib qleankernel` from 13 objects, `-O3 -march=native -fPIC -fno-trapping-math` (`scan.c` without the last, with `-ffp-contract=off`); every `c/*.h` is a traced input of every object |
| sizes                | ~82 k lines Lean (`QLean/`), ~37 k lines C/H (`c/`); `Kernel/*Test.lean` and `#guard`s run at `lake build` |
| artefacts            | `.lake/build/lib/libqleankernel.{a,so}`, `libqlean_QLean.so`, `bin/qlean-test`, `bin/bench-*` (built at this commit) |
| module system        | legacy files (no `module` keyword); a `module` file may import them                              |
| index                | `.lake/build/refactor-index.db`, same schema as freyd's (`decl_info`, `decl_range`, `module`)    |
| ownership            | `AGENTS.md` rule 3: `QLean/Value.lean`, `Wire/Tags.lean`, `QLean.lean`, `Test.lean`, lakefile are shared — edit only when assigned |

## 8. Integration design for freyd (`AOP/A6_FinRel.lean`)

freyd's abstraction is `rel (l : List (K×V)) : ⟨K⟩ ⟶ ⟨V⟩ := fun k v => (k,v) ∈ l`, with `SortedRel K V` = two
Lean `Array`s, `rep s = rel (keys.toList.zip vals.toList)`, `lookup_rep : graph(lookup s) ≫ ∋ = rep s`, and the
hash join `join(F,G)(xs) ≜ ix(xs) F G° ix(xs)° ∩ (<)`.

- A qlean instance is Int64-only: `structure QSortedRel := (keys vals : Column) (hk : Order.ascending .i64 false
  false n keys = true)`; `rep s = rel (((atoms .long keys).zip (atoms .long vals)).map unbox)` with
  `unbox (.long n) = n`, total by `atoms_type`; `lookup s k = binBytes 8 false true false keys (pushBits ∅ k 8)`
  read back, then `Column.get .long vals i`. Indices become Int64.
- To be proved in freyd against the Lean bodies (qlean has none of it): `lookup_rep` from `binStep` (fuel
  recursion over `ordKey`-biased UInt64 keys and `Column.bitsAt`) and `ascending`'s `List.all`; `rep_ofList` from
  `atoms_ofAtoms_bytes` (dense). Trusted or left to qlean: C = Lean body for `bin`, `ascending`, `encode`; and for
  a `foR` column the open `atoms_encode`.
- Headline `#print axioms` becomes `{propext, Quot.sound, Classical.choice}` (choice via `Column.atoms`), one more
  than the aop skill's `{propext, Quot.sound}`; freyd's `leet/L1.lean` already admits choice through `Std.HashMap`.
  The headline then states that the Lean SPEC of the program is correct and nothing about the binary.
- Build: do not `require qlean` from `/home/dh/repo/freyd/lakefile.toml` — a `require` is package-wide, every
  `lake` call would elaborate qlean's `lakefile.lean`, and the first `lake build leet` would build all of `QLean`.
  Instead a separate lake package directory, e.g. `/home/dh/repo/freyd/leetq/`, with its own lakefile,
  `require freyd from ".."` and `require qlean from "../../qlean"`: path dependencies build in their own dirs, so
  freyd's `.lake/build` is reused, freyd's lakefile and default `lake build` never see qlean, and `Freyd/`/`AOP/`
  stay dependency-free. `lean-refactor index` would need pointing at the new package.
- No typeclass in `A6_FinRel` now: the second instance is not generic in K,V, its `lookup` is `Option` through
  `Column.get`, its sortedness is a `Bool` — a class drawn from `Array K` would be reshaped anyway. What makes the
  swap free: every consumer (`join`, two-sum, the build-then-probe program) is stated over `rep s` and uses only
  `rep_ofList : rep (ofList l) = rel l` and `lookup_rep`, never the `keys`/`vals` fields. Those two laws are the
  whole future interface; turning them into a class when the instance exists is a mechanical lean-refactor.

Preconditions before integrating, all on the qlean side: (a) `atoms_encode` proved; (b) a behavioural lemma for
`binBytes` (least index with `k ≤ hay[i]`) and for `Order.ascending` (sortedness); (c) the Lean spec decl for
`qlean_coc_bin` located or written, if the column is to stay `foR` during lookup. Until then freyd's `Array`
representation with the rep-only discipline above is the right one.
