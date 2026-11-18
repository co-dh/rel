# Rel: migration plan from master 059f46c to `rel-architecture.zh.typ`

Source of the target: `doc/rel-architecture.zh.typ`. Source of the current state: the refactor index of
`/home/dh/repo/rel` at 059f46c and the files it points to. All line numbers below are 1-based and valid at 059f46c
only; every step starts by re-reading its anchor with the index query in section 0.

Owner decisions on section 5 (taken as the recommended defaults; the owner may override):
- R1/Q4: `rep` is a predicate `Reps`, `tab none` represents every relation (partial correctness); diagnostics
  come from the failing node, never from a truncated table.
- R4: "kernel" (5) differs from "runtime export": `stop`, `Coc.encode`/`decode` stay as runtime exports;
  `own_write` and the group-id kernels are rewritten with `EmitC`.
- R5: atoms are `u1 char i8 i16 i32 i64 f32 f64 sym` (nine). Truth values are `u1` (width 1), no `bool`;
  the tag is `Arr .u1`
  (from `.boolean`); `char` is 8-bit and strings are `arr char`; boxed `general` and the temporal atoms
  are deleted.
- R7: floats are canonicalised (one NaN, `-0 ↦ +0`) before the order-preserving bit map; equality = bit equality
  after canonicalisation.
- R8: 1.1 writes only the equations that are not a restatement of one `Core.Rel` law (`mu_unfold`, `nu_unfold`);
  the other ten are used directly as the `Core.Rel` laws.
- Q1 delete `RelAop/Syn.lean`; Q2 surface `refold` becomes `hylo` too; Q3 `tab` holds `Option (Tab A B)`, the structure
  `{n, key, val}` (owner: M);
  Q7 `Den` inlined by hand; Q9 `hylo` keeps `k what ch body`; Q11 `call` means the callee's term inlined;
  Q12 `compile` moves out of `RelRun` into the library that holds the proofs.
- Non-log outputs (baseline, row analysis) go into this file or `doc/`, not `/data/tmp`.

## 0. Conventions every step obeys

- Repo `/home/dh/repo/rel`. Never grep `*.lean`; locate a declaration with

  ```
  sqlite3 -readonly /home/dh/repo/rel/.lake/build/refactor-index.db "select i.user_name, i.module, r.sl1+1, r.el1+1
    from decl_info i join decl_range r on r.name=i.name and r.module=i.module
    where i.internal=0 and i.user_name like '<PATTERN>'"
  ```

  and users with `select use_module, group_concat(l1+1) from use_site where name='<FULL NAME>' group by 1`.
- `LR` = `/home/dh/repo/lean-refactor/scripts/lean-refactor`. Run without `--apply` first (preview), then with it.
  After each `LR` run: `LR index`, then the doubled-namespace query
  `select name from decl_info where name like 'Rel.Rel.Rel.%' or name like 'Rel.LeetQ.%' or name like 'Rel.QLean.%'`
  must return nothing.
- `B <targets>` = `CAP_MEM_MB=20000 /home/dh/repo/freyd/scripts/cap lake build <targets>`, output to
  `/data/tmp/<step>.log`, read the tail. A worktree builds only the modules it edited.
- Phase gate (run once in main before a phase is merged): `make check` (build, compile-diff, crate-test, syms,
  native, ldd, index-complete, axioms, noreduce, panic, externs), then
  `lake -d /home/dh/repo/freyd/relaop build RelAop -R -K rel=/home/dh/repo/rel`.
- Forbidden in every step: `sorry`, `native_decide`, `!` indexing, raised `maxHeartbeats`, a new `panic!`, a
  pointwise (`∃`) definition body, `Classical` inside `Rel/Core/`, a second copy of `Rel`/`Column`/`FinRel`.
- Model labels: **opus** = the step contains Lean proving or an algorithm to design; **sonnet** = typing, renames,
  deletions, builds. A sonnet step whose build fails on a proof stops and reports; it does not prove.
- Generated code: every `rel_program` constant in `Rel/Programs/*` and `Rel/Lang/Test*` is emitted by
  `Expand.node` (`Rel/Run/Lang/Expand.lean` 676-746) through `mkConst ``Gen.…`. A step that renames or removes a
  `Gen.*` constant edits the matching line of `Expand.node` in the same step and rebuilds `Rel.Programs.Prelude`.

## 1. Diff table

Size: S = one step under 20 tool calls, M = one to three steps, L = more than three steps or a proof campaign.

| #  | Design item                | Current code (module : line)          | Gap                                 | Size |
|----|----------------------------|---------------------------------------|-------------------------------------|------|
| 1  | `Rel` = `tab` or `lazy`    | `Rel.Rel`, `Run/Core.lean:485`        | no `lazy`, `Known`; 2420 dependents | L    |
| 2  | `Known = {dom, ran}`       | `Gen.Dem`, `Gen.lean:25`, dom only    | `ran` side has no counterpart       | M    |
| 3  | CRel deleted, ok → Option  | `CRel`, `Run/CRelDef.lean:8`          | 2297 decls; `.rel` read at ok=false | L    |
| 4  | `Fn`, `Dem` deleted        | `Gen.lean:48`, `:25`; `Pl` `:51`      | 224 + 182 decls in 7 modules        | L    |
| 5  | `Den` inlined              | `abbrev Den`, `Lang/Den.lean:20`      | 274 decls; no `LR` inline command   | M    |
| 6  | `Tm` without `Bool` index  | `Tm`, `Run/Lang/Tm.lean:15`           | `Res`, Elab, Expand, Bits, Plan     | L    |
| 7  | `compile` returns subtype  | `compile`, `Compile.lean:235`         | all gaps closed first; R2           | L    |
| 8  | Syn, Le, Eqv, Hom.den gone | `Lang/Syn.lean`, 347 lines            | leaf in rel; freyd imports it       | S    |
| 9  | `Tm.Ax` as equations       | `Syn.lean:21-42`, `:131-148`          | 12 constructors, 12 equations       | S    |
| 10 | refold renamed hylo        | `Tm.lean:91`, `Gen.lean:267`          | 120 names contain "refold"          | S    |
| 11 | foldI a definition         | `Tm.lean:68`, `Den.lean:98`           | typechecks only after item 6; R3    | M    |
| 12 | flat a definition          | `Tm.lean:72`, `Den.lean:103`          | same; `flat_sound` goes             | M    |
| 13 | inl, inr constructors      | prim rows 3, 4, `Syntax.lean:150`     | rows exist, constructors do not; R9 | S    |
| 14 | junc definition, no juncD  | `Tm.lean:35`, `:38`; `Gen.lean:247`   | `Core.Rel.junc` already the union   | M    |
| 15 | symmetric division ctor    | `Alg.symDiv`, `Run/Alg.lean:293`      | no `Tm` ctor, no `Den`              | M    |
| 16 | non-positive μ/ν refused   | `Tm.pol`, `Tm.lean:254`               | Elab `.fix` (1655-1670): no check   | S    |
| 17 | gap: open share            | `Rows.lean:125`, `Expand.lean:530`    | producer not located; R6            | M    |
| 18 | gap: setify, asc           | `rowGaps`, `Rows.lean:107`            | row soundness; float order; R7      | M    |
| 19 | gap: hylo                  | `rep_refold`, `RefoldSpec.lean:124`   | `den_local` does not exist          | M    |
| 20 | gap: lam, E, thin          | `lamDen` `Den.lean:111`; `Canon`      | three soundness lemmas missing      | L    |
| 21 | gap: call                  | `Tm.lean:79`; den `𝟘`, `none'`        | stage 5 not specified in code       | L    |
| 22 | prim rows as fold/hylo     | 28 rows, `Compile.lean:77-112`        | not checked per row                 | M    |
| 23 | scan, scatter primitives   | drivers, `Kernel/Driver.lean:25-38`   | `Op`, `Op.eval`, two laws           | L    |
| 24 | gather, asc, distinct      | `gatherPacked`, `Order.grade`, `nubC` | externs, laws, "= composition"      | L    |
| 25 | one encoding `packed`      | `Ext.Enc`, 7 ctors, `Value.lean`      | 460 decls depend on `Enc`           | L    |
| 26 | nine atoms                 | `QAtomicType`, 18 ctors, `Value:13`   | 1718 decls; boolean, general; R5    | L    |
| 27 | RELK.txt 99 → 5            | `crate/RELK.txt`, `crate/src/ffi/`    | native gate needs more; R4          | L    |
| 28 | q-only kernels leave       | 99 externs (`extern.tsv`)             | qlean pinned to e024297: no work    | S    |

## 2. Phases

Order: P0 → P1 → P2 → P3 → P4 → P5 → P7, and P6 (kernels) independent of P2-P5 at the Lean level except for
the float order (5.2 waits for 6.9). P1 and the steps of P2 can run while P6 runs.

### P0 Baseline (1 step)

**0.1 sonnet.** `make -C /home/dh/repo/rel index` then `make -C /home/dh/repo/rel check > /data/tmp/p0.log 2>&1`.
Record from the log the compile-diff line ("compile agrees … on N definitions; not ok on …") into
section "Baseline" at the end of this file with `git -C /home/dh/repo/rel rev-parse HEAD`.
Done: exit 0 and the file exists.
Every later phase gate compares its compile-diff line with this one.

### P1 Syn removal (3 steps; 1.1 then 1.2; 1.3 in the same merge as 1.2)

**1.1 sonnet — `Tm.Ax` as equations.** File `Rel/Lang/Den.lean`, append after `den_anti` (line 585-592).
For each of the 12 constructors of `Tm.Ax` (`Rel/Lang/Syn.lean` 21-42: `id_comp comp_id assoc conv_conv conv_comp
meet_join comp_join join_comp comp_zero zero_comp mu_unfold nu_unfold`) add one theorem

```
theorem Tm.den_<ctor> <the constructor's binders, copied> (ρ : Val) : (<lhs>).den ρ = (<rhs>).den ρ := <term>
```

where `<lhs>`, `<rhs>` are the two indices of the constructor's result type `Tm.Ax lhs rhs`, any hypothesis of
the constructor becomes a hypothesis of the theorem, and `<term>` is the right-hand side of the matching case of
`Tm.Ax.sound` (`Syn.lean` 131-148; they use `Core.Rel.id_comp comp_id comp_assoc recip_recip recip_comp
inter_union comp_union union_comp comp_zero zero_comp mu_fix nu_fix`, `Tm.den_subst`, `Tm.den_mono`). Build
`B Rel.Lang.Den`. Done: 12 new theorems, build green. If a copied term does not check, stop and report (opus).

**1.2 sonnet — delete `Rel/Lang/Syn.lean`.** Before deleting, `LR uses Rel.Lang.foldDen_le` and
`LR uses Rel.Lang.foldIDen_le`: expected users are in `Rel.Lang.Syn` only; if another module uses one,
`LR move-decl Rel.Lang.Den <name> --apply` first. The `rfl` lemmas `Tm.den_comp … Tm.den_own` (315-328),
`den_mu`, `den_nu`, `den_refold` (333-341) have no user in the index and are deleted with the file. Then
`git rm Rel/Lang/Syn.lean`; no rel module imports it. Build `B Rel`. Done: `select count(*) from decl_info where
module='Rel.Lang.Syn'` is 0 after `LR index`.

**1.3 sonnet — freyd side.** Only `/home/dh/repo/freyd/relaop/RelAop/Syn.lean` (39 lines: `instance : Cat Syn`,
`def den : Functor Syn RelSet`, `den_outl`, `den_outr`) imports `Rel.Lang.Syn`; no relaop file imports
`RelAop.Syn`. Variant A (default): `git -C /home/dh/repo/freyd rm relaop/RelAop/Syn.lean`. Variant B (if the
owner answers Q1 with "keep the functor"): before 1.2, copy `Rel/Lang/Syn.lean` lines 44-303 (`Tm.Le` … 
`Syn.assoc`) to the top of `RelAop/Syn.lean`, replace its `import Rel.Lang.Syn` with `import Rel.Lang.Den`,
skip the `Tm.Ax` cases (replace `Tm.Le.ax` uses with the 1.1 equations: opus). Done: the relaop gate of section 0.

### P2 Work that does not depend on the `Rel` type (6 steps; all parallel in worktrees except 2.2 before 2.3)

**2.1 sonnet — refold → hylo.** Name list: run
`select name from decl_info where internal=0 and lower(name) like '%refold%' and module not like 'Rel.Programs.%'
and module not like 'Rel.Lang.Test%' and name not like 'Rel.Lang.Pre.%' and name not like 'Rel.Lang.Expr.%'`.
For each name N pass the pair `N N'` where N' replaces `refold` by `hylo` and `Refold` by `Hylo` (must include
`Rel.Lang.Tm.refold`, `Rel.Lang.Gen.refold`, `Rel.Lang.Gen.refoldRounds`, `Gen.rep_refold`, `refoldRounds_ok`,
the `Refold.*` names of `Rel/RefoldSpec.lean`): `LR rename N N' … --apply`; then the module:
`LR rename Rel.RefoldSpec Rel.HyloSpec --apply`. The surface constructor `Pre.refold` (Elab 160, 304, 915, 1636)
keeps its name (Q2). Check by hand the three places a rename tool can miss: `Expand.lean:735`
(`mkConst ``Gen.refold`), `Rows.lean:114` (gap string), `Elab.lean:1640`. Build `B RelRun Rel`. Done: the query
above returns only names in generated modules; build green.

**2.2 opus — `flatDen` is a composition.** File `Rel/Lang/Den.lean`, after `flatDen` (line 103). Add

```
theorem flatDen_eq (T : Den I (.prod A B)) :
    flatDen T = ((graph Prod.fst ≫ T) ∩ (graph Prod.snd ≫ (graph Prod.fst)°)) ≫ graph Prod.snd
```

with the three projections spelled exactly as the right-hand sides of the `.outl`, `.outr` cases of `Tm.den`
(`Den.lean` 191-234), so that step 4.2 closes by `rfl` after rewriting with it. Pointwise reading: `(i,a)` to
`(a',b)` with `T i (a',b)` and `a' = a`, then to `b`. Build `B Rel.Lang.Den`.

**2.3 opus — `foldIDen` is a `foldDen`.** Same file, after `foldIDen` (line 98). Add

```
theorem foldIDen_eq (Te : Den I (.prod V V)) (TS : Den (.prod E (.prod I V)) (.prod I V)) :
    foldIDen Te TS =
      ((π₁ ≫ π₁°) ∩ (π₂ ≫ foldDen (ranD ⟨𝟙, Te ≫ π₂⟩) (TS ∩ (π₂ ≫ π₁ ≫ π₁°)))) ≫ π₂
```

where `π₁`, `π₂`, `ranD`, `⟨_,_⟩`, `𝟙` are the Core operators `Tm.den` assigns to `.outl`, `.outr`, `.ran`,
`.pair`, `.id`. The carrier is `I × V`; the meet `TS ∩ (π₂ ≫ π₁ ≫ π₁°)` keeps the index constant, which
`foldIDen` does by writing `p.1` on both sides of `TS`. Without that meet the equation is false. Reuse
`foldDen_le`-style unfolding of `foldDen` (`Den.lean:89`). Build `B Rel.Lang.Den`.

**2.4 sonnet — positivity error at elaboration.** File `Rel/Run/Lang/Elab.lean`, `.fix` case, lines 1655-1670.
After the line `let body ← closed? …` insert a check that calls `Tm.pol` (`Rel/Run/Lang/Tm.lean:254`) with
exactly the arguments the μ and ν cases of `Tm.gap` pass (`Rel/Lang/Rows.lean` 116-119) and, when it fails,
`throw ⟨p, s!"{if least then "μ" else "ν"} at {p}: its body does not use {k} positively"⟩`. Do not touch
`Tm.gap` (see R2). Build `B RelRun Rel`. Done: build green (no program in the tree is non-positive today: the
compile-diff line equals baseline); add one `#guard_msgs` test of the new error to `Rel/Lang/Test.lean`.

**2.5 opus — meaning of symmetric division.** File `Rel/Lang/Den.lean`, after `rdivDen` (lines 49-70). Add
`def symDivDen (UA : Den A A) (UB : Den B B) (R : Den A C) (S : Den B C) : Den A B`, point-free, built from
`ldivDen`/`rdivDen` and converse the way those two take their universes, and in `Rel/CRelRel.lean` after
`rep_symDiv` (line 306) the theorem that the right-hand side of `rep_symDiv`
(`(∀ c, R x c ↔ S y c) ∧ ((∃ c, R x c) ∨ (x ∈ Ua ∧ y ∈ Ub))`) is `symDivDen (corefl Ua) (corefl Ub) R S x y`.
Build `B Rel.Lang.Den Rel.CRelRel`.

**2.6 opus (analysis, no edit) — prim rows as fold/hylo.** For each of the 28 rows of `Compile.lean` 77-112
(`tau cons mem inl inr map filter takewhile thinL merge loop uncons length sum inits tails prefix suffix concat
cat uncat zip snoc unsnoc setify distinct asc tic`) write to `doc/rel-rows.md` one line: the `Tm` it equals
(using only constructors of the target `Tm`), or "primitive" with the reason. `Syntax.lean` 150-192 already marks
`filter takewhile tails prefix suffix concat` with a `prelude :=` definition. Output feeds Q5; no code changes.
Done (`doc/rel-rows.md`). Owner decisions: arrays are built only by `snoc`, never by `cons` (appending uses the
array's spare capacity), so the default `fold` eliminates `[nil, snoc]` (step 4.5) and `cons`, `uncons` are
definitions used only as reads (`cons° = uncons`); arrays are read left to right where the meaning allows, so the
right fold stays only for `sum` and `thinL`, whose meanings are right-to-left (kept); Q5 answered L (every row with
slice code stays a fused kernel, its definition the specification, `⟦row⟧ = ⟦def⟧`).

### P3 The `Rel` type (13 steps; serial on one branch `rel-lazy`, except where marked)

Staging rule: names stay, types change first, indices are removed last. Master is not touched until the phase
gate passes on the branch.

**3.1 sonnet — the structure `Rel.Rel` becomes `Rel.Tab`.** Pairs from the index:
`select name || ' Rel.Tab' || substr(name, 8) from decl_info where internal=0 and (name='Rel.Rel' or name like
'Rel.Rel.%')` (structure, fields `n key val`, `mk`, `Holds`, `toList`, `Canon`, …). `LR rename <pairs> --apply`.
Build `B RelCore RelKernel RelRun Rel`. Done: no declaration named `Rel.Rel` or `Rel.Rel.*` remains. (Q3: the
design names `Tab` too, the structure with the three fields, because 2128 declarations project `.n .key .val`.)

**3.2 opus — `CRel` is `Option (Tab A B)`.** File `Rel/Run/CRelDef.lean` lines 8-64. Replace the structure by

```
abbrev CRel (k v : Obj) := Option (Tab k v)
def CRel.ok (c : CRel k v) : Bool := c.isSome            -- temporary, removed in 3.12
def CRel.rel (c : CRel k v) : Tab k v := c.getD default   -- temporary, removed in 3.12
def CRel.mk (r : Tab k v) (ok : Bool) : CRel k v := if ok then some r else none   -- temporary
```

delete `instance : Inhabited (CRel A B)` (line 46; `Option` has one, value `none`), restate `CRel.guard` (50),
`comp` (53), `inter` (57), `union` (60), `CRel.ofC` (43) through `CRel.mk`. Then repair, module by module in
import order, the 16 modules that use `CRel.mk` (92 declarations) and every `{ c with … }`/anonymous-constructor
use: query `select use_module, group_concat(l1+1) from use_site where name='Rel.CRel.mk' group by 1`. Statements
of the form `(X).ok = true → … (X).rel …` keep their text. Split by library if over budget: 3.2a `RelRun`
(`Run/CRel*Def.lean`, `Gen.lean`, `Expand.lean`), 3.2b `Rel/CRel*.lean`, 3.2c `Rel/Lang/*`. Build
`B RelRun Rel`. Done: build green; compile-diff line; list every `#guard` whose expected value changed (R1).

**3.3 opus — `Known`, `Rel`, `Reps`.** New file `Rel/Run/Lang/Lazy.lean` (imports `Rel.Run.CRelDef`), add it to
the imports of `Rel/Run/Lang/Gen.lean`:

```
structure Known (A B : Obj) where
  dom : Option ((n : USize) × Vals A n) := none
  ran : Option ((n : USize) × Vals B n) := none
inductive Rel (A B : Obj) where
  | tab (t : Option (Tab A B))
  | lazy (f : Known A B → Rel A B)
def Rel.run : Rel A B → Known A B → Option (Tab A B)      -- tab t ↦ t;  lazy f ↦ (f K).run K
```

and in `Rel/Rep.lean` after `Rep.rep` (line 17):

```
def Known.den (K : Known A B) : Core.Rel A.El A.El × Core.Rel B.El B.El     -- none ↦ 𝟙, some c ↦ corefl (∈ c)
def Rel.Reps : Rel A B → Core.Rel A.El B.El → Prop
  | .tab none, _ => True
  | .tab (some t), R => Rep.rep t = R
  | .lazy f, R => ∀ K, (f K).Reps (K.den.1 ≫ R ≫ K.den.2)
```

This is the reading of the design's `rep (lazy f) = R ⇔ ∀ K L, rep (f ⟨K,L⟩) = K ≫ R ≫ L` as a predicate; R1
states why it is not a function. Prove `Reps.tab_some`, `Reps.lazy_iff` only if a later step cites them. Build
`B Rel.Run.Lang.Lazy Rel.Rep`.

**3.4 opus — bridge from the old function type.** File `Rel/Lang/GenSpec.lean`, after `Gen.Sound` (line 37):

```
def Gen.Fn.toRel : {d : Bool} → Gen.Fn d A B → Rel A B     -- false: tab (f ()); true: lazy fun K => dom-keyed call
theorem Gen.Sound.reps {f : Gen.Fn d A B} {T} (h : Gen.Sound f T) : (Gen.Fn.toRel f).Reps T
```

(`toRel` itself goes in `Gen.lean` after line 48). For `d = true` and `K.dom = none` the result is `tab none`.
Reuse `keys`, `Cor` (`GenSpec.lean` 26, 31), `Sound.eq` (41). This step proves that the predicate of 3.3 is
implied by today's soundness; if it cannot be proved, stop: 3.3's definition is wrong and Q4 is open.
Build `B Rel.Lang.GenSpec`.

**3.5 opus — `Gen.Fn d A B := Rel A B` (phantom `d`), leaves.** `Rel/Run/Lang/Gen.lean`: change line 48 to
`abbrev Gen.Fn (_d : Bool) (A B : Obj) := Rel A B`; rewrite the leaves (lines 66-89) so a `d = false` leaf
returns `.tab …` and a `d = true` leaf returns `.lazy fun K => …` reading `K.dom` (and `K.ran` for `leq`, `lt`,
`top`: `tab (K ≫ leq ≫ L)`, `K × L`) where it read `Dem`. Keep `Dem` (line 25) until 3.12 for the plan path.
Restate `Gen.Sound` (`GenSpec.lean:37`) as `def Gen.Sound (f : Rel A B) (T) : Prop := f.Reps T` and re-prove the
leaf lemmas `const_sound … mem_sound` (`GenSpec.lean` 89-145). Build `B Rel.Run.Lang.Gen`; `GenSpec` may be red
below line 145 until 3.7.

**3.6 opus — binary and unary combinators.** `Gen.lean` 93-190 (`comp conv meet join diff dom ran pair prod junc
ldiv rdiv` and the `…B` bit-matrix forms): each becomes a function on `Rel` by cases `tab`/`lazy`. Rule: the
body the old code ran at `d = false` is the `tab, tab` case; the body it ran at `d = true` is under
`.lazy fun K =>` with `Dem.of`/`Dem.l`/`Dem.r` (29-40) replaced by `K.dom`; `tab r ≫ lazy g` calls
`g ⟨some r.val-column, K.ran⟩`. `comp` must not read `r.n` of a `none` (line 109 does today). Lemmas
`comp_sound` (348) … `rdiv_sound` (555), `compB_sound … ldivB_sound` (649-661). Build `B Rel.Run.Lang.Gen`.

**3.7 opus — folds and fixed points.** `Gen.lean` 191-270 (`fold foldI flat nu nuAC mu onNodes juncD
refoldRounds refold`) and `GenSpec.lean` 495-548, `CompileSpec.lean` 29-125 (`mu_sound nu_sound flat_sound
onNodes_sound juncD_sound`), `Rel/HyloSpec.lean`. `mu` returns `tab none` when the cap is hit (today: the
truncated chain with `ok = false`). Build `B RelRun Rel.Lang.GenSpec Rel.Lang.CompileSpec`.

**3.8 opus — `Compile`, `Expand`, tests on the new `Fn`.** `Rel/Run/Lang/Compile.lean`: `CodeEnv` (13), `bind`
(17), `Out` (155), `Out.memo` (162), `Tm.gen` (169-232) drop the `()`/`Dem` application. `Expand.lean`:
`printText` (100) and `checkErr` (104) take `Rel A B` and read `Rel.run r {}`; `share` (621), `body` (670),
`node` (676-746) emit `Rel A B` where they emitted `CRel A B`. `Rel/Lang/Test.lean` `get`, `test/TestCompile.lean`
`differs` compare `Option (Tab A B)`. `Rel/Lang/CompileSpec.lean` 212-355 restated on `Reps`;
`Rel/Lang/RelRep.lean` `prf pprf prfNode` (31-67) follow. Build `B RelCore RelKernel RelRun Rel TestCompile`.
Done: phase-style check `make check`; compile-diff line equals baseline except entries explained by R1.

**3.9 sonnet — remove the index from `Tm`.** `Rel/Run/Lang/Tm.lean`: line 15 becomes
`inductive Tm : Obj → Obj → Type`; delete the `Bool` index from every constructor (15-91), from `Res` (94:
`(A) × (B) × Tm A B`), `Tm.mapM parts fv Sub lift Sub.get fresh subst pol` (100-278); `Tm.call` loses its first
argument `d` and `cv : Option (Lean.Name × Bool)` becomes `Option Lean.Name`. Then `Gen.Fn` loses its parameter:
`LR remove-arg Rel.Lang.Gen.Fn 0 --apply` (check the argument index in the preview). Users by constructor are in
the anchor list of section 4. Build `B Rel.Run.Lang.Tm Rel.Run.Lang.Bits Rel.Run.Lang.Plan Rel.Run.Lang.Gen
Rel.Run.Lang.Compile`.

**3.10 opus — Elab without demand bits.** `Rel/Run/Lang/Elab.lean`: `swapTm pairTest Proj Proj.pre Proj.meet
convTm convProj onPairs divTest` (1247-1385), `at?` (1401), `closed?` (1405, becomes `at?`), `uniPart uniTm numU`
(1412-1433), `corAt` (1489), `closeRes` (1493: today it prefixes the universe when `d = true`; without `d` the
prefix is applied where `Tm.fv`/shape requires it — Q6), `build` (1507-1670), `callArgs` (1675). Build `B RelRun`.

**3.11 opus — Expand without demand bits.** `Expand.lean`: `closed` (526, `!d && t.fv.isEmpty`), `number`
(530-534), `free` (538), `varComp` (541), `arcs` (548), `code` (607-618), `plan?` (629), `planOr` (657), `spine`
(663), `node`. The bit-matrix path (`Bits.runC`, `Bits.lean:249`) was chosen on `d = false`; choose it on
"both operands are `tab`" inside `Gen.comp`/`meet`/`diff`/`ldiv` (3.6 already has the case split) and delete
`compB meetB diffB ldivB` as separate names if they have no caller left. Build `B RelCore RelKernel RelRun Rel
TestCompile`.

**3.12 sonnet — delete the temporaries.** `LR unused` must list `Gen.Dem`, `Dem.of`, `Dem.l`, `Dem.r`,
`Gen.Fn.toRel`, `Gen.Sound.reps`, `CRel.mk`; `LR remove <each> --apply`. For `CRel.ok`, `CRel.rel` (454 + 479
declarations, most generated): rewrite hand-written statements `(X).ok = true → P (X).rel` to
`∀ r, X = some r → P r` module by module (opus if a proof breaks); then `LR remove`. `LR fold-abbrev` is not the
inverse needed for `CRel`: replace `CRel A B` by `Option (Tab A B)` with `LR retype Rel.CRel …` after reading its
`--help` (the manual decides the exact form). Build all four libraries.

**3.13 sonnet — inline `Den`.** `Den A B` (`Den.lean:20`) is used by 274 declarations in `Den GenSpec Rows
ConvSpec CompileSpec BitsSpecRun BitsSpec`. `LR` has no "unfold abbrev" command (Q7). Until one exists: the step
is blocked; do not do it with a regex.

### P4 Constructor changes of `Tm` (5 steps; serial, they share the same match arms)

For each removed constructor delete its arm in: `Tm.lean` (`mapM fv subst pol`), `Den.lean` (`den`, `den_congr`,
`den_subst`, `den_pol`), `Rows.lean` (`gap`), `Compile.lean` (`gen`), `CompileSpec.lean`, `ConvSpec.lean`,
`BitsSpec.lean`, `BitsSpecRun.lean`, `Elab.lean` (`convTm`, `build`), `Expand.lean` (`node`). Anchors: section 4.

**4.1 opus — `inl`, `inr` constructors; `junc` a definition; `juncD` deleted.** `Tm.lean`: add
`| inl : Tm A (.sum A B)` and `| inr : Tm B (.sum A B)`; replace constructor `junc` (35) by

```
def Tm.junc (R : Tm A C) (S : Tm B C) : Tm (.sum A B) C := .join (.comp (.conv .inl) R) (.comp (.conv .inr) S)
```

delete `juncD` (38). `den` of `.inl`/`.inr` is `Core.Rel.inl`/`Core.Rel.inr`, so `(Tm.junc R S).den ρ =
Core.Rel.junc (R.den ρ) (S.den ρ)` by `rfl` (`Core/Rel.lean:70`). `gen` of `.inl`/`.inr` is `CRel.inl`/`CRel.inr`
lifted; soundness from `inl_sound` (120), `inr_sound` (125). Delete prim rows 3, 4 (`inlRow`, `inrRow`,
`Syntax.lean` 150-151; `Compile.lean` rows; `Rows.lean` rows) so one definition remains (R9). Delete `Gen.junc`,
`Gen.juncD` (247), `junc_sound` (438), `juncD_sound` (`CompileSpec:125`), `Expand.node` lines 701, 737; Elab 1292,
1422, 1578-1587 build `Tm.junc`. Build all four libraries + `TestCompile`. Done: `Quicksort`, `TestRefold`, `Test`
(the users of `Gen.juncD`) keep their `#guard` results; timing of `Rel.Programs.Quicksort` reported (R3).

**4.2 opus — `flat` a definition.** Replace constructor `flat` (`Tm.lean:72`) by
`def Tm.flat (R : Tm I (.prod A B)) : Tm (.prod I A) B := .comp (.meet (.comp .outl R) (.comp .outr (.conv .outl)))
.outr`; `den` equals `flatDen` by 2.2. Delete `Gen.flat` (209-212), `flat_sound` (`CompileSpec:75`),
`Expand.node:717`. Users of `Gen.flat` in generated code: `Test` 20, `Chess` 9, `TestWumpus` 7, `Blocks` 3,
`Edit` 2, `Wumpus`, `Knapsack`, `ModuleTest`. Done as 4.1, timings of `Rel.Programs.Chess` reported.

**4.3 opus — `foldI` a definition.** Replace constructor `foldI` (`Tm.lean:68`) by the `Tm` whose `den` is the
right-hand side of `foldIDen_eq` (2.3). Delete `Gen.foldI` (196-206), `foldIDen_le`, the `foldI` gap arm
(`Rows.lean:121`), `Expand.node:715`. Users: `Edit`, `Knapsack`, `Test`, `TestKnapsack`, `TestEdit`. The gap
"foldI: no foldI_sound" disappears with the arm. Done as 4.1.

**4.4 opus — `symDiv` constructor.** `Tm.lean` after `rdiv`: `| symDiv (UA : Tm A A) (UB : Tm B B) (R : Tm A C)
(S : Tm B C) : Tm A B` (mirrors `ldiv`'s universe arguments; Q8). `den := symDivDen` (2.5); `gen` through
`CRel.symDiv` (`Run/CRelRelDef.lean:52`); soundness from `CRel.rep_symDiv` (`CRelRel.lean:306`) and 2.5. Add arms
to every function listed at the head of P4. Surface syntax in `Grammar`/`Elab` is a separate decision (Q8).

**4.5 opus — the left fold over `[nil, snoc]` as default; build by `snoc` only.** Today `fold` is only a right
fold over `[nil, cons]`: `foldDen` (`Den.lean:107-113`) seeds `ys[n]`, sets `ys[t] = S(xs[t], ys[t+1])` and returns
`ys[0]`; the kernel round `k` reads element `k` from the end (`Alg.foldRound`, `Run/Alg.lean:686-700`). Rule
(`doc/rel-rows.md` head): read left to right where the meaning allows, right to left only where it needs it; build
arrays only by appending. No row meaning changes, so no `rowDens` entry and no `#guard` result changes.
- Add the left fold, step `S : V×E ⟶ V` reading `(acc, x)`, index 0 first (the order `scan` runs), as `Tm.fold`;
  today's constructor stays as `Tm.foldr`, meaning unchanged. Meaning: `foldDen` becomes `foldrDen`, a left
  `foldDen` beside it (seed `ys[0]`, `ys[t+1] = S(ys[t], xs[t])`, result `ys[n]`); `foldIDen`, `foldIDen_eq`
  (115-157) move to the left fold (the meet becomes `π₁ ≫ π₁ ≫ π₁°`); `fold_le`, `foldI_le` (550-558) for both;
  both constructors' arms in every function listed at the head of P4.
- Code: `foldRound` takes the reading order (element `k` from the start, or from the end as today);
  `demandStepC` (733-736) pairs `(pend, el)` for the left fold, `(el, pend)` for the right; `foldOnC` (743-748),
  `CRel.foldOn` (`Run/CRelFoldDef.lean:16`), `Gen.fold` (`Gen.lean:191-192`) with `Gen.foldr` beside it,
  `Gen.foldI` if 4.3 has not removed it, `Expand.node:713`.
- Right fold kept only where the meaning is right-to-left: `Arr.sumC` (`Alg.lean:1546`; `sum`'s side condition
  bounds suffix sums) and the first pass of `thinLOnC` (1393; `thinLDen` is the chain from the end). Every other
  `foldOnC` caller moves to the left fold.
- Prepend → append: every output path built by `consC` (`Alg.lean:656`) builds by `snocC`: `thinBodyC` (1377)
  becomes the two passes `thinA`/`thinK` of `doc/rel-rows.md` (actions appended right to left, then the kept
  elements appended left to right; `thinLDen`, `rep_thinLOnC` (`CRelFold.lean:469`) and their `#guard`s keep their
  statements), `mapFoldC` (771), `alphaC` (896), `permC` (1242), `subseqC` (1347), `ticC` (1531). `consC` and
  `CRel.cons` (`Run/CRelListDef.lean:44`) remain only as the `cons` row's code until 2.6 deletes the row;
  `mergeRound` (1408) already appends.
- Lemmas: `rep_foldOnC` (`CRelFold.lean:133-181`), `CRel.rep_foldOn` (533-557), `foldRows_iter`,
  `foldRows_rep_keep` (`RepFold.lean:328-347`, `575-669`), `Gen.fold_sound` (`GenSpec.lean:493-518`), each for both
  reading orders; the `rep_*C` lemmas of the kernels above.
- Programs: every left fold's step flips its pair, and a step that conses becomes one that snocs, so outputs keep
  their order; each prelude definition takes its form in `doc/rel-rows.md` §2: `prefix`, `subseq`, `tails`,
  `filter`, `takewhile`, `perm` (its `add`), `sort` (`Rel/Programs/Prelude.lean`); the programs whose generated code
  calls `Gen.fold` (`Selsort Mss Detab Blocks Edit Party Knapsack Quicksort`) and the tests (`Test TestHylo
  TestSelsort TestKnapsack TestEdit TestMss`). A fold whose meaning is right-to-left becomes `foldr`.

Build all four libraries + `TestCompile`. Done: compile-diff unchanged (241 / 25), every `#guard` result unchanged.

### P5 Close the gaps, in the decided order (8 steps; 5.4a-c parallel, the rest serial)

**5.1 opus — share.** `Tm.gap` arm `Rows.lean:125`, `compile_sound` arm `CompileSpec.lean:305`, den
`Den.lean:225` (`R.den Val.empty`), `Expand.number` 530-534 (wraps only `closed` sub-terms), `convTm` share arm
`Elab.lean:1325`, `convProj` `:1361`. First find by `#eval` over `relRegistry` (as `test/TestCompile.lean` does)
which registered terms contain a `.share k R` with `R.fv ≠ []`; report the list. Then fix the producer so none is
emitted. The gap arm stays as a well-formedness condition (R2).

**5.2 opus — setify, asc rows.** `Rows.lean`: add `Row` entries at indices 24 (`setify`) and 26 (`asc`) from
`CRel.rep_setify` (`CRelPower.lean:283`) and `CRel.rep_asc` (`CRelArith.lean:221`, one direction, hypothesis
`B.Ordered`); the converse direction of `rep_asc` needs `Obj.KeyInj` (`CRel.lean:124`), false at float atoms
today (R7). Remove both names from `rowGaps` (107) and the `prim` arm from `Tm.gap`. Waits for 6.9 if the float
key changes.

**5.3 opus — hylo.** New in `Rel/Lang/Den.lean`:
`theorem Tm.den_local (b : Tm A B) (k) (ch : Core.Rel …) (h : <b has the shape c ≫ G(X) ≫ S>) : (∀ y, ch x y →
X y = X' y) → b.den (ρ.bind k X) x = b.den (ρ.bind k X') x` as written in `doc/rel-denotation-design.md` §7.2;
then `hylo_sound` in `CompileSpec.lean` from `Gen.rep_hylo` (`HyloSpec.lean:124`, hypotheses `Monotonic Φ` from
`Tm.den_mono`, `Local` from `den_local`). Remove the hylo arm of `Tm.gap` (`Rows.lean:114`). Q9: `Tm.den` of
hylo ignores `ch`; the premise tying `ch` to the body is not in the design.

**5.4a / 5.4b / 5.4c opus — `lam_sound`, `E_sound`, `thin_sound`.** `GenSpec.lean`, one theorem each, against
`lamDen` (`Den.lean:111`), `EDen`, `thinDen`; reuse `Rel.Tab.Canon`, `canon_ofC` (`CRel.lean:310`), `canon_comp`
(330), `canon_inter` (335), `canon_union` (341), `canon_diff` (`CRelFold:627`), `canon_antiJoin` (`CRelRel:329`),
`Obj.lt_*` (`ObjOrder.lean` 41-49, 145). Each needs `Ordered` and `KeyInj` of the element object as hypotheses;
where they come from in `compile_sound` is Q10. Then the three arms of `compile_sound` and of `Tm.gap`.

**5.5 opus — call (stage 5).** `Tm.call` (`Tm.lean:79`), den `𝟘` (`Den.lean:229`), `none'` (`Compile.lean:221`),
Elab 1335, 1652, 1702, Expand 637, 666, 746. The design names the stage and not the mechanism (Q11); this step
starts with a written proposal, not code.

**5.6 sonnet — delete `Tm.gap`.** When every arm of `Tm.gap` (`Rows.lean` 111-134) returns `none` except the
well-formedness arms of R2: rename what remains (`LR rename Rel.Lang.Tm.gap Rel.Lang.Tm.illFormed --apply`),
delete `rowGaps`, `gap_or` (`CompileSpec:233`), the last line of `compile_sound` (355). Build all + `TestCompile`.
Done: compile-diff reports 0 "not ok".

### P6 Kernels (survey + 12 steps; Rust and Lean halves of one kernel serial, different kernels parallel)

**6.0 opus (analysis, no edit) — replacement table.** For each of the 99 rows of
`/data/tmp/rel-gates/rel/extern.tsv` (namespaces: `Rel.Kernel` 51, `Ew` 17, `Order` 18, `Coc` 10, `Scan` 1,
`Column` 1, `Db` 1): the Lean users (`use_site`), and one of {`scan op`, `scatter`, `gather`, `asc`, `distinct`,
"q-only: delete", "no target: R4"}. Output `/data/tmp/rel-kernels.md`. Steps 6.8-6.11 are cut from this table;
they cannot be cut before it exists.

**6.1 sonnet — `Op`.** New `Rel/Kernel/Op.lean` in `RelKernel`:
`inductive Rel.Kernel.Op | add | sub | mul | min | max | eq | lt | and | or | not | first | fadd | fmul | fdiv |
flt` (complete the list from §4 of the design), `def Op.readsAcc : Op → Bool`, `def Op.assoc : Op → Bool`,
`def Op.eval : Op → UInt64 → UInt64 → UInt64` on raw words. The name `Rel.Lang.Op` (`Syntax.lean`) already
exists: keep the kernel one in `Rel.Kernel`. Existing op codes to map: `Ew.add … Ew.acos` (`Elementwise.lean`
22-65), `Scan.Verb` (`Scan.lean:11`).

**6.2 opus — `packed`.** `Rel/Kernel/Value.lean`: add to `Ext.Enc` the constructor
`| packed (lg : UInt8) (bases widths payload : ByteArray)` and its case of `Ext.Enc.raw` (line 705); `bits` is
base 0 width 1, `enum` width `⌈log2 card⌉`, `const` width 0. Reuse `Coc.encodeAt` (`Coc.lean:85`). The other six
constructors stay until 6.11.

**6.3 opus — `crate/src/pack.rs`.** Block encode/decode for `packed`, on `pod::Elt` (`pod.rs:22`), `by_width!`
(`ids.rs:12`), `Producer::block_into` (`enc.rs:284`), `pool`. `cargo test` in `crate/`.

**6.4 / 6.5 opus — `scan`, `scatter` (parallel).** Lean (`Rel/Kernel/Scan.lean`, new `Rel/Kernel/Scatter.lean`):

```
@[extern "qlean_k_scan"]    def Kernel.kscan (op : Op) (seg : @& Enc) (es : @& List Enc) : Enc := <model on raw>
@[extern "qlean_k_scatter"] def Kernel.kscatter (ix e : @& Enc) (n : USize) (fill : UInt64) : Enc := <model>
theorem raw_scan …    theorem raw_scatter …       -- Rel/KernelSpec/, statements from §4 of the design
```

each with its `decide`-beside-`#guard` pair; Rust `crate/src/scan.rs` (exists, extend), `scatter.rs` (new),
`ffi/scan.rs`, `ffi/structural.rs`; add the two symbols to `crate/RELK.txt`. Temporary `k` names because
`qlean_scan` (`Scan.scan`, `Scan.lean:179`) and `Kernel.scan` (`Driver.lean:33`) exist; renamed in 6.11. The
models are stated with `Op.eval`, never with a Lean closure. Gates: `B RelKernel`, `sh crate/build.sh syms`,
`make externs`.

**6.6 / 6.7 / 6.8 opus — `gather`, `asc`, `distinct` (parallel, after 6.4 and 6.5).**

```
@[extern "qlean_k_gather"]   def Kernel.kgather (ix e : @& Enc) (fill : UInt64) : Enc
@[extern "qlean_k_asc"]      def Kernel.kasc (es : @& List Enc) : Enc × Enc          -- values, permutation
@[extern "qlean_k_distinct"] def Kernel.kdistinct (es : @& List Enc) : Enc
```

laws `raw_permute`, `asc_sorted` + `asc_perm`, `distinct_first` + `distinct_cover`, and one theorem each "= the
composition of `kscan` and `kscatter`" from the design's composition table (distinct = scan → scatter; asc =
radix scan → scatter, MSD for `arr` byte; gather = concat → asc → scan fill → scatter). The Lean body IS the
composition; the Rust is the fused form. Existing material: `gatherPacked` (`Structural.lean:34`), `scatterPacked`
(240), `Order.grade` (`Sort.lean:69`), `gradeLane` (96), `runStarts` (`Search.lean:233`), `Alg.nubC` (`Alg:202`).

**6.9 opus — atoms and order-preserving codes.** `QAtomicType` (`Value.lean:13`) renames by `LR rename`:
`boolean→u1 long→i64 int→i32 short→i16 byte→i8 real→f32 float→f64 symbol→sym` (`char` keeps its name);
then `Obj.key` (`ObjOrder.lean:19`) at float
atoms becomes the order-preserving bit map. Removing `general` and the temporal atoms: per R5, the `.sum` tag
becomes `Arr .u1`; `Obj.general` goes and `Obj.Ordered` loses its `t ≠ .general` premise.

**6.10 opus, many — migrate users.** One step per group of 6.0's table: each `Alg`/`Code`/`CRel*Def` definition
that calls an old extern is restated on the five, with its `KernelSpec`/`KernelWF` lemma re-proved from the new
law. `Rel/KernelSpec/*` (about 5700 lines) and `Rel/KernelWF/*` (about 16000 lines) are stated on today's
kernels; the number of steps is known only after 6.0.

**6.11 sonnet — delete the old.** Remove the six old `Ext.Enc` constructors, the old externs, drivers
`Kernel.map fold scan permute` (`Driver.lean`; 5, 2, 2, 2 users), the Rust files without a caller; `LR rename`
the `k` names to `Kernel.scan gather scatter asc distinct` and the symbols to `qlean_scan …`; `crate/RELK.txt`;
`panic-allow.txt`. Gates: `syms`, `externs`, `panic`, `crate-test`.

**6.12 opus — native gate.** `Rel/Lang/EmitC.lean:16` `abi` lists `Db.ownWrite`, `Order.groupIds`, `idGroups`,
`Ew.val cmp bit`, `whereBits`, `gatherBytes`; `relc`/`rel-native` write columns with `qlean_own_write`. Restate
`abi` on the five kernels plus whatever R4 keeps; `lake build rel-native` and the `out/key`, `out/val` comparison.

### P7 Plan A (4 steps; serial)

**7.1 opus — library boundary.** `compile` lives in `RelRun` (precompiled); `Tm.den` (`Rel/Lang/Den.lean`,
noncomputable, `Classical`) and every `*_sound` live in `Rel`. Either `Den.lean`, `GenSpec.lean`,
`CompileSpec.lean`, `Rows.lean` and their imports (`CRel*`, `KernelWF`) move under `Rel/Run/`, or `compile` moves
to `Rel/Lang/` and `rel_program` (which runs it at elaboration time) imports `Rel`. Q12 decides; this step is
blocked on it.

**7.2 opus — the subtype.**
`def compile (η : CodeEnv) (ρ : Val) (hη : η.Sound ρ) (t : Tm A B) (hw : t.illFormed = none) :
{r : Rel A B // r.Reps (t.den ρ)}` built by the recursion of `Tm.gen` (`Compile.lean` 169-232) with each arm's
proof the matching arm of `compile_sound` (`CompileSpec.lean` 238-355). Delete `compile_sound`, `Out.Sound`,
`Code.Sound`.

**7.3 opus — `rel_program` emits `compile t` (design doc §5.1 stage 4).** Delete from `Expand.lean`: `code node
plan? planOr spine body share primE fitConst primWrappers`; from `Rel/Lang/RelRep.lean`: `prf pprf prfNode lem
lemO rep`; `Rel/Lang/TestRep.lean`. `test/TestCompile.lean` and the `compile-diff` gate lose their subject
(nothing second to compare with): replace the gate by the `#guard`s of the programs.

**7.4 sonnet — cleanup.** `LR unused`, `LR unused-simp`, `LR remove-import` over `Rel/Lang/*` and `Rel/Run/Lang/*`;
update `CLAUDE.md` Layout/Gates text and `Makefile` (`compile-diff`).

## 3. Parallel and serial, per phase

| Phase | Steps | Parallel worktrees (no shared section)     | Serial                                         |
|-------|-------|--------------------------------------------|------------------------------------------------|
| P0    | 1     | —                                          | 0.1                                            |
| P1    | 3     | 1.3 (freyd repo) beside 1.1                | 1.1 → 1.2; 1.2 and 1.3 land together           |
| P2    | 6     | 2.1, 2.2, 2.4, 2.5, 2.6                    | 2.2 → 2.3 (same section of `Den.lean`)         |
| P3    | 13    | 3.3 beside 3.2                             | 3.1 → 3.2 → 3.4 → 3.5 → … → 3.13, one branch   |
| P4    | 5     | none: every step edits the same match arms | 4.1 → 4.2 → 4.3 → 4.4 → 4.5                    |
| P5    | 8     | 5.4a, 5.4b, 5.4c; 5.2 beside 5.3           | 5.1 first; 5.5 → 5.6 last                      |
| P6    | 13+   | 6.1, 6.3; 6.4, 6.5; 6.6-6.8; 6.10 groups   | 6.0 first; 6.2 → 6.4; 6.9 → 6.10 → 6.11 → 6.12 |
| P7    | 4     | —                                          | 7.1 → 7.2 → 7.3 → 7.4                          |

Total: 8 phases, 53 steps (6.10 counted once; it expands after 6.0). Opus 39, sonnet 14.

## 4. Anchors: use sites of the constructors that change (line numbers at 059f46c)

| Ctor   | Tm.lean            | Den.lean        | Compile | CSpec  | Rows | Elab                | Expand      |
|--------|--------------------|-----------------|---------|--------|------|---------------------|-------------|
| foldI  | 68 126 166 230 275 | 226 255 395 577 | 217     | 355    | 121  | 1351 1623           | 715         |
| flat   | 72 127 167 231 276 | 227 269         | 219     | 260    | 128  | 1352 1627           | 717         |
| juncD  | 38 115 155 219 269 | 211 255 537     | 202     | 352    | 130  | 1348 1584           | 737         |
| junc   | 35 114 154 218 268 | 210             | 201     | 289    | 130  | 1292 1422 1578 1587 | 701         |
| refold | 91 131 171 237 273 | 234 285 380 565 | 228     | 355    | 114  | 1347 1640           | 521 735     |
| share  | 65 174 248 278     | 225 242 294     | 216     | 305    | 125  | 1325 1361           | see below   |
| call   | 79                 | 229             | 221     | 355    | 115  | 1335 1652 1702      | 637 666 746 |
| mu, nu | 87, 84             | —               | —       | 29, 43 | 116  | 1283 1284 1664 1668 | 520 722 734 |

`CSpec` is `Rel/Lang/CompileSpec.lean`. Also:

- `share` in `Expand.lean`: 531 534 543 550 608 642 664 714; in `Plan.lean:336`; in `RelRep.lean` 39, 57, 106.
- `ConvSpec.lean`: foldI 48, 134; flat 134; juncD 135; junc 132; refold 135; share 46, 93, 194.
- `foldI` in `BitsSpec.lean:76`, `BitsSpecRun.lean:31, 480`; `junc` in `RelRep.lean:95`.

## 5. Risks and open questions (stated, not resolved)

- **R1 `rep` is not a function on the new `Rel`; a failed table carries no rows.** The design gives
  `rep (lazy f) = R ⇔ ∀ K L, rep (f ⟨K,L⟩) = K ≫ R ≫ L`, a predicate; decision 2 writes `rep r = ⟦t⟧ρ`. `succ`
  with no `dom` has no table, and `tab none` has no relation. Step 3.3 uses `Reps` with `tab none ↦ True`
  (partial correctness, as `ok = true →` today) — Q4. Also: code reads `.rel` when `ok = false` today
  (`Gen.comp` line 109, `Expand.printText` 100, `checkErr` 104, `Gen.mu`'s truncated chain, `failures` 112);
  with `Option` those rows are gone and the diagnostics change.
- **R2 Plan A needs `compile` total on `Tm`, and three conditions are not expressible in `Tm`.** Positive μ/ν
  bodies, closed `share` parts and resolved `call`s are properties computed by recursion on `Tm` (`Tm.pol`,
  `Tm.fv`); they cannot be constructor fields without induction-recursion. "Rejected at elaboration" does not
  remove the hypothesis from the theorem. Steps 5.6/7.2 keep a decidable `t.illFormed = none`; whether that
  counts as "all gaps closed" is the owner's call. Second half: `compile` is in precompiled `RelRun`, `Tm.den` and
  all proofs in `Rel` (Q12).
- **R3 foldI and flat as definitions contradict the gap order and may be slower.** Both definitions need `conv`
  or `ran` on on-demand terms, which the `Bool` index forbids, so they typecheck only after P3, while decision 6
  lists foldI first. `foldI` equals a `fold` only with the index-preserving meet (2.3). `Gen.foldI`, `Gen.flat`,
  `Gen.juncD` are direct kernels today; the derived terms run `outl° `, a meet and a composition per call
  (Chess, Edit, Knapsack, Quicksort use them). No measurement exists.
- **R4 "RELK.txt has 5 lines" contradicts the gates.** `rel-native` and `relc` call `qlean_own_write` and the
  group-id kernels (`EmitC.lean:16`); `qlean_stop` (`Kernel.stop`) is the capacity abort; `Coc.encode`/`decode`,
  `Column.blockStart` are externs with no place among the five. `externs`, `syms` and `panic` gates read the list.
- **R5 (decided above) Nine atoms remove types the core uses.** `Vals (.sum A B)` keeps its tag in
  `Arr .boolean`; `Obj.general`
  and `Obj.Ordered (t ≠ .general)` name `.general`; `Arr .long` holds `lo`/`hi` of `Obj.arr`. The design does not
  say what the tag column becomes (i8, or packed width 1) or whether boxed columns remain. 1718 declarations
  depend on `QAtomicType`; `KernelSpec` + `KernelWF` (about 21700 lines) are stated on today's kernels and
  encodings: P6's proof cost is unknown until 6.0.
- **R6 Open shares: producer not located.** `Expand.number` wraps only closed terms, yet `Tm.gap` has the arm;
  `convTm` (1325) and `convProj` (1361) rebuild shares. `closed` is defined with `!d`, so its meaning changes in
  3.11.
- **R7 Float order.** `rank64` sends every NaN to one key, so `¬ lt` is not antisymmetric and `KeyInj` fails;
  the design's order-preserving bit map makes distinct NaN payloads distinct and `-0 ≠ +0`. That changes
  equality on floats in every relation, not only in `asc`.
- **R8 `Tm.Ax` as equations are one-line restatements of `Core.Rel` laws** (10 of 12), which the repository's
  "no one-liner theorems" rule deletes on sight unless they are deliverables. Decision 3 asks for them; step 1.1
  writes all 12.
- **R9 `inl`/`inr` exist as prim rows 3, 4** with `inl_sound`, `inr_sound`. Adding constructors without deleting
  the rows is a duplicate; 4.1 deletes the rows, which changes `prims` indices (`rows` are indexed 0-27 in
  `Rows.lean`) and `Calc.toTerm`'s reading in freyd relaop (`RelAop/Calc.lean`).
- **R10 `nuAC`.** `Expand.node:732` emits `Gen.nuAC` for AC-3-shaped bodies; `compile` uses `Gen.nu`. They agree
  by the compile-diff test only; `nuAC` has no soundness lemma (design doc §7.2 says it needs its own). After 7.3
  either `compile` chooses `nuAC` (needs the lemma) or AC-3 programs slow down.
- **R11 `Tm.pol` after 4.2/4.3.** It treats `foldI`, `flat` as "must not mention k"; as definitions their
  polarity is derived from `comp`/`meet`/`conv`, so the set of accepted programs changes.
- **R12 Staging uses temporaries** (`CRel.ok`, `CRel.rel`, `CRel.mk`, `Fn.toRel`, phantom `d`, `k`-named
  kernels, `packed` beside six encodings). Each is a second form of one fact for the length of a phase, against
  the DRY rule; each has a named deleting step (3.12, 3.9, 6.11).

Questions for the owner:

| Q   | Question                                                                                                  |
|-----|-----------------------------------------------------------------------------------------------------------|
| Q1  | freyd: delete `RelAop/Syn.lean`, or keep `Functor Syn RelSet` by moving the quotient into relaop?         |
| Q2  | Does the surface keyword / `Pre.refold` also become hylo?                                                 |
| Q3  | Answered M: `tab` holds `Option (Tab A B)`, `Tab` the structure `{n, key, val}` (3.1's rename)            |
| Q4  | Is `Reps` (predicate, `tab none ↦ True`) the intended `rep`? If not, what is `rep (tab none)`?            |
| Q5  | Answered L: `snoc`, `asc` primitive; every `+ slice` row of 2.6 a fused kernel tied by `⟦row⟧ = ⟦def⟧`    |
| Q6  | Without `d`, where does Elab insert the universe prefix that `closeRes` inserts today?                    |
| Q7  | `Den` inline: add an unfold-abbrev command to lean-refactor, or keep `Den` as a notation?                 |
| Q8  | `Tm.symDiv` signature (universe arguments as `ldiv`?) and its surface syntax.                             |
| Q9  | Signature of `Tm.hylo` (`k what ch body` kept?) and the premise that ties `ch` to `body`.                 |
| Q10 | Where do `Ordered`/`KeyInj` hypotheses of lam/E/thin come from in `compile`'s type?                       |
| Q11 | Meaning of `call` in `Tm.den` (stage 5): inline the callee's term, or an environment of definitions?      |
| Q12 | Library boundary for plan A: proofs into `RelRun`, or `compile` out of it?                                |

## Baseline

At `e78e922`, `make check` exit 0. compile-diff: "compile agrees with the generated code on 241 definitions; not ok
on 25" (`sudokuac.s`, `Test.given.q{R,M,F,h}`, `Test.orders.Of`, `Test.muGrow.g`, `TestWumpus.given.f0`-`f16`,
`TestRefold.refoldCycle.bad`). Every phase gate must reproduce 241 / 25 or explain the difference.
