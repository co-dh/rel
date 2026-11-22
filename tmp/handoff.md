# Tm28 B3 handoff

Base de81c61. Spec: `doc/tm-minimal-design.zh.typ` row B3 (line ~360), §"`dom` 行需要的 dem" (line ~125).

## Done (this branch)

- `Prim.dem : PrimDem` (`keys | whole | arg`, default `keys`) replaces `Prim.whole : Bool` (`Rel/Run/Lang/Syntax.lean`,
  `PrimDem` just above `structure Prim`, with a hand-written `ToExpr`). `asc`, `sums` are `dem := .whole`.
- `Tm.whole` (`Rel/Run/Lang/Tm.lean:113`) is now `r.dem != .keys`, so `Tm.dem`'s `arg` clause is unchanged and every
  proof that unfolds it is untouched. `TmGen` `ToExpr Prim` and `Expand` row equality read `dem`.

## Blocker found: `Prim.objs` cannot type a `dom`/`ran` row

`Prim.objs r A B` (`Tm.lean:107`) reads the object variables off the row's TYPE `r.sig.2` only, then looks up every
`r.vars` (which include the PARAMETERS' variables). `dom : (R : A ⟶ B) ⟶ (A ⟶ A)`: `B` is in no position of `A ⟶ A`,
so `domRow.objs A A = none`, hence `Prim.den = 𝟘`, `primGen` = error table, `primHasCode = false`. Same for `ran`
(`A` absent from `B ⟶ B`). No existing row has a parameter variable absent from its type (`flat`, `foldI`, `asc`,
`sums`, `loop` all mention theirs), so this never surfaced. `nil : A ⟶ [B]` is fine.

General fix (needed before the rows exist): `Prim.objs r A B (ps : List (Obj × Obj))` also unifies each parameter
pattern `r.sig.1[i]` (its pair-test form `X×Y ⟶ X×Y` where `some true`) with the i-th argument's objects. The
arguments' objects are in hand at every reader: `Prim.den r A B ss` (`ss : List Sem`, `Den.lean:419`), `primGen r A B xs`
(`xs : Codes`, `TmGen.lean`), `primHasCode r A B xs` (`xs : List (Obj × Obj)`), `rowGens`' `σ` (`TmGen.lean:40-100`,
already per-σ). Proof sites to follow: `Prim.den_iff` and `objs_simp` (`ConvSpec.lean:40-85`), `rowOK_args`
(`GenSound.lean:304`), `Prim.den_map_congr` (`Den.lean:1014`), `Prim.den_mono` (`Den.lean:829`).

## Left (the B3 table row), in order

1. `Prim.objs` over the arguments (above).
2. Rows in `prims` (`Syntax.lean`): `domRow` sig `([((A,B), some false)], A, A)`, `dem := .arg`, `conv := "dom"`;
   `ranRow` `([((A,B), some false)], B, B)`, `dem := .arg`, `conv := "ran"`; `nilRow` `([], A, [B])`. `written := false`.
3. `Tm.dom R := .arg (.prim domRow) R`, `Tm.ran`, `Tm.nil := .prim nilRow` as defs in `Tm.lean` (as `Tm.prod`), so
   every construction site `.dom R` / `.ran R` / `.nil` in Elab/Schema keeps compiling; delete the three constructors.
4. Code: `kernRows` (`GenK.lean:368`) gets `("dom", ``GenK.dom)`, `("ran", ``GenK.ran)`, `("nil", ``GenK.nil)` — the
   last-resort fit in `Expand.primE` (a constant that is itself a code, as `foldI`). `GenK.dom`/`ran` bodies unchanged.
5. Meaning: `RowCode.dom/ran/nil` and `rowDens` entries (`Den.lean:321-420`): `Sem.one fun T => 𝟙 _ ∩ T ≫ T°`,
   `Sem.one fun T => 𝟙 _ ∩ T° ≫ T°°`, `nilDen`. New `Tm.dom_den`, `Tm.ran_den`, `Tm.nil_den` (as `Tm.prod_den`).
6. Soundness: `rowOK_dom/ran/nil` (pattern `rowOK_flat`, `GenSound.lean:930`) from the existing `case dom/ran/nil`
   arms of `Tm.gen_sound` (`GenK.dom_wf`, `GenK.ran_wf` at `GenSound.lean:1160-1161`, nil at 1146) and add to
   `rowsProved`/`rowsProved_ok`.
7. Converse: `Prim.den_conv` (`ConvSpec.lean:58`) enumerates rows with `conv`; `dom`, `ran` are their own converse
   only because their meaning is coreflexive — add a `first` alternative proving it by `a = b` from `𝟙 ∩`.
8. `Tm.kids` (`Tm.lean:382`) `.dom R => R.kids` becomes an `.arg (.prim r) x` branch with `r.sym == domRow.sym`;
   `Tm.den_local` (`Den.lean:1039`) and `Tm.size_kids`, `Tm.genHyp_kids` follow.
9. Remove the deleted constructors' arms. `use_site` (index, stale line numbers) lists them: `Tm.lean` dem 124/135/138,
   size 155/163, mapMSz 179-180, fv 227-228/247, subst 280-281/308, pol 332-333/347, kids 382; `TmGen.lean` gen 158-159/167,
   hasCode 232-234, tmE 298-299/310; `Elab.lean` instObj 274-275/283, convTm 1960/1967/2016 (`.ran`/`.dom`/`.nil`
   arms; with rows the `.arg` arm + `conv` field does it); `Den.lean` den 453-454/462, den_congr 533/559, den_subst 653,
   den_pol_spine 881-884/965, den_local 1103-1133; `GenSound.lean` GenHyp 189/199, monoOK 205/213, pol_of_fv 1374,
   number_spine 1637, gen_wf/gen_sound cases 1146/1160-1161; `ConvSpec.lean` convTm_den 134-161,
   convTm_instObj_den 524-560; `EmitC.lean` Plan.tabB 1273-1274/1314 (emits C for dom/ran/nil: must match the row).
10. `pairTest`, `divTest`, `test` (Elab 1922, 2056, 2542-2562), `uniPart` (2166-2168), `DfnCut.flat`/`foldI`
    (2082-2085), `zeroTm` (2069), `build` (2323-2352), `Schema.join` (Schema.lean:146) build `.dom`/`.ran`/`.nil`:
    unchanged text once step 3's defs exist, but `DfnCut` is an inductive indexed by the term, and `Tm.flat_den`
    (`Den.lean:487`), `Tm.prodUni_den` (`Den.lean:506`), `DfnLaw.lean:278` unfold `Tm.den` of `.dom`/`.ran`: rewrite
    them with `Tm.dom_den`/`Tm.ran_den`.

Note on dem: with `arg`, `Tm.dem (ran R) = R.dem` (today `ran` is always `false`); `dom` keeps `R.dem`, `nil` keeps
`true`. Check `GenSoundTest` and the compile pins for a `ran` of an on-demand `R`.
