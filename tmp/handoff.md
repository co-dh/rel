# Tm28 B3 handoff (after B3b)

Spec: `doc/tm-minimal-design.zh.typ` row B3 (line ~360), §"`dom` 行需要的 dem" (line ~125). B3 is NOT yet marked done
in that table: the constructors still exist.

Branch `worktree-agent-a10c07c339edfdd1b`, on base 035657b + 4392c7b (`PrimDem`, `Prim.dem`). The worktree index
(`<worktree>/.lake/build/refactor-index.db`) was built after step 1; re-run
`/home/dh/repo/lean-refactor/scripts/lean-refactor index` in the worktree for current line numbers.

## Done

1. `Prim.objs r A B ps` (`Rel/Run/Lang/Tm.lean:106`): a variable the type names is read off the type; a variable only
   a parameter names (`dom`'s `B`, `ran`'s `A`) off that argument's objects `ps` (pair test `some true` at `X×Y ⟶ X×Y`,
   as `rowObjs`). Callers: `Prim.den` (`ss.map (s.1, s.2.1)`), `primGen` (`xs.map (x.1, x.2.1)`), `primHasCode` (`xs`).
   New lemmas `Sems.le.objs` (Den.lean, after `Sems.le`), `CodesRep.objs` (GenSound.lean, after `CodesRep`). Proofs
   that follow: `Prim.den_iff`, `objs_simp` (+`Option.orElse`), `Prim.den_mono`, `Prim.den_map_congr`, `rowOK_args`,
   DfnLaw `ho` facts (now `∀ ps`), `Prim.starRow_keyLifts` (`simp only [ho]`: the RHS's objs is under `fun i`).
   Full build green, GenSoundTest 1660/1660, 0 sorryAx (commit "B3b step 1").
2. Rows `domRow` (`dem := .arg`), `ranRow` (`dem := .arg`), `nilRow` (Syntax.lean, after `starRow`), at the end of
   `prims`; `written := false`; NO `conv` yet (see step 7).
4. `kernRows` (GenK.lean:368): `("dom", ``GenK.dom)`, `("ran", ``GenK.ran)`, `("nil", ``GenK.nil)`.
5. `RowCode.dom/ran/nil` and `rowDens` entries (Den.lean ~350, ~412); `rowDens_mono` got an `all_goals` arm for
   dom/ran.
6. `rowOK_dom`, `rowOK_ran`, `rowOK_nil` (GenSound.lean, after `rowOK_star`), in `rowsProved` and `rowsProved_ok`.
   ConvSpec `Prim.den_conv`'s simp lists name `domRow, ranRow, nilRow`.

## Left, in order

3. `Tm.dom R := .arg (.prim domRow) R`, `Tm.ran R := .arg (.prim ranRow) R`, `Tm.nil := .prim nilRow` as defs in
   Tm.lean (as `Tm.prod`, line ~147); delete constructors `dom` (Tm.lean:30), `ran` (:31), `nil` (:42). Add
   `Tm.dom_den`/`Tm.ran_den`/`Tm.nil_den` (as `Tm.prod_den`, Den.lean ~499) via `Prim.den_iff`/unfolding `Prim.den`
   with `domRow.objs A A [(A, B)] = some [A, B]`.
7. Converse: give `domRow`/`ranRow` `conv := "dom"`/`"ran"`. `Prim.den_conv` (ConvSpec.lean:59) then has a goal per
   row whose meaning is coreflexive: change the intro pattern `⟨σ, -, ⟨rfl, rfl⟩, h⟩` to keep `hσ`, and add a `first`
   alternative: from `h : Sem.one (fun T => 𝟙 ∩ T ≫ T°) ss b a` get `b = a` (Sem.one is `𝟘` or the dite), `subst`,
   `exact ⟨σ, hσ, ⟨rfl, rfl⟩, h⟩`.
8. `Tm.kids` (Tm.lean:376) `.dom R => R.kids` → inside the `.arg (.prim r) x` branch, `r.sym == domRow.sym` →
   `x.kids k A`; `Tm.den_local` (Den.lean ~1050), `Tm.size_kids`, `Tm.genHyp_kids` follow.
9. Remove the deleted constructors' match arms. `use_site` from the index lists them (line numbers stale): `Tm.lean`
   dem/size/mapMSz/fv/subst/pol/kids; `TmGen.lean` gen (166-167, 174), hasCode (242-245), tmE; `Elab.lean` instObj,
   convTm (`.ran`/`.dom`/`.nil` arms: with rows the `.arg` arm + `conv` field does it); `Den.lean` den (443-444, 451),
   den_congr, den_subst, den_pol_spine, den_local; `GenSound.lean` GenHyp, monoOK, pol_of_fv, number_spine,
   gen_wf/gen_sound `case dom/ran/nil` (1157, 1171-1172, 1276-1277, 1295 before B3b's +55 lines); `ConvSpec.lean`
   convTm_den, convTm_instObj_den; `EmitC.lean` Plan.tabB (emits C for dom/ran/nil: must match the row).
10. `pairTest`, `divTest`, `test`, `uniPart`, `DfnCut.flat`/`foldI`, `zeroTm`, `build`, `Schema.join` build
    `.dom`/`.ran`/`.nil`: unchanged text once step 3's defs exist. `Tm.flat_den` (Den.lean ~495), `Tm.prodUni_den`
    (~514), `DfnLaw.lean:278` unfold `Tm.den` of `.dom`/`.ran`: rewrite with `Tm.dom_den`/`Tm.ran_den`.

## Behaviour change to check with step 3

`Tm.dem (.arg (.prim ranRow) R)`: `Tm.whole` is true (`dem != .keys`), the head is a `.prim`, so `Tm.dem = R.dem`.
Today `Tm.dem (.ran R) = false` always (ran is memoised whole by `Tm.code`). After step 3 a `ran` of an on-demand `R`
is no longer memoised: `GenK.ran` runs under the caller's keys (sound by `GenK.ran_sound` at every `K`). Look in
GenSoundTest output and the programs (`Tm.prodUni` is `ran(⟨u, ⊤(v)⟩)`: `⊤` and a universe are closed, so it stays
closed) for a `ran` of an on-demand `R`, and report the count of definitions whose plan changes. `dom` keeps `R.dem`,
`nil` keeps `true` (`.keys` row with no argument).
