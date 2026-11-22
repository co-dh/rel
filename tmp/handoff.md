# B4 handoff (checkpoint at 40 tool calls)

## Done (WIP commit, does not build yet)
- lean-refactor rename thin -> front: Tab.front, frontDen, Tab.front_den, Tab.front_wf, GenK.front_sound, frontSp,
  Op.front, Tm.front, Pre.front, GenK.front, GenK.front_wf, Test.frontDiag (18 files).
- Tm.lean: constructors `est`/`front` and all their match arms deleted; `Tm.est Q := .arg (.prim estRow) Q`,
  `Tm.front Q := .arg (.prim frontRow) Q` after `Tm.nil`.
- Syntax.lean: `estRow` (mono), `frontRow` (mono := false), both `written := false`, `some true` pair-test param, added
  to `prims`; Op.table entry "front". Op constructors `est`/`front` kept (map precedent: freyd Calc reads them).
- Elab.lean: `Op.row` maps `.est`/`.front` to the rows (so `applied` -> `appliedRow`); `Pre.est`/`Pre.front` and every
  arm deleted (instObj, mo map, convTm throws, build, applied arm).

## Left
- Elab `dfns`/`DfnCut`: constructors `est`, `front`. NOTE `build` hands dfns `build x` of the order Q : B -> B (not
  tau(Q)); fused must be `Tm.est (pairTest Q)` (pairTest Elab.lean:1954). ldiv universes may be `.id` (ldivDen's
  universe disjunct is harmless under `∋ ∩`).
- TmGen.lean 170-171, 242-243, 312-313: delete arms. GenK.lean: kernRows add ("est", ``Tab.est), ("front",
  ``Tab.front); delete GenK.est / GenK.front defs.
- Den.lean: Tm.den arms 409-410, den_mono 537-538; RowCode.est/front; rowDens entries (Sem.one, estDen/frontDen on T).
- GenKEst: restate est_sound/front_sound on `GenK.testVals B (.arr B) _ Q fun q X => Tab.est q X`.
- GenSound: GenHyp/monoOK arms (189-190, 207), est_wf/front_wf (544-548) and cases 1238-1239, 1366-1367 delete;
  rowsProved += "est","front"; rowOK_est/rowOK_front like rowOK_thinL (:921); by_cases lines in rowsProved_ok.
- ConvSpec 161, 557: drop `est _ _ | front _ _`.
- EmitC 1367-1380: move est/front emission into `rowB` (c == ``Tab.est / ``Tab.front).
- DfnLaw: Prim.den_estRow / den_frontRow (form of den_foldIRow :232), Tm.est_den, Tm.front_den, dfnCut_den cases.
- .rel texts: thin( -> front( in Test/Lists, Folds, Orders, TestNative, Kern45, RoundTrip.
- doc/rel-architecture.zh.typ rename + typst compile.
