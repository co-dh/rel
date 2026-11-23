# B9bc handoff (WIP, nothing built yet)

Design as in the task: `Tm.own` and `Tm.callCv` deleted, `Tm.call ks c (cv : Option Name) os b`.

## Done (edited, NOT yet compiled)
- `Rel/Run/Lang/Tm.lean`: ctor, dem, size, mapMSz, inner, fv, subst, pol, linIn, kids.
- `Rel/Run/Lang/TmGen.lean`: gen, argGen, hasCode, argHasCode, #guards, tmE (`toExpr cv`), numberKey, number, twoCalls.
- `Rel/Run/Lang/Elab.lean`: instObj, `Pre.own` + traverse arm + build arm deleted, `Pre.call.cv : Option Name`, convTm
  (own arm deleted; call arm = self theorem branch with `by obtain ⟨-, rfl⟩ := h; exact pure …`, derived branch
  `convTm b`), callTm (`return .call ks c cv os (← inst t)`), callNode.
- `Rel/Run/Lang/Expand.lean`: `useDef` perm arm deleted; `convOf o : Option Name` = guard then `some (o.const ++ `conv)`;
  `callDef` has new param `cs : List (String × String)` before `d`; `cv := own <|> convOf o` where `own` = `some k`
  iff `cs.lookup n = some n` (self theorem); `walk` passes `convs prog` at both callDef sites; `fieldsEq` compares `cv.map key`.
  Choice: table taken from the walked program (`convs prog`, in `walk`) not threaded through `read`.
  A theorem `c° = c'` with c' ≠ c falls to the derived converse (the name c' has no body here).

## Left (anchors are use_site rows of the index, lines of f10a505)
1. `Rel/Lang/ConvSpec.lean`: ConvOK `:115-128` (own, callCv clauses -> the `call … (some c')` clause of the task),
   `convTm_den` (own :185, call :203, callCv :208), `convTm_instObj_den` (:573, :596, :601), `callTm_convOK` (:903; delete if unused),
   it may need `ρ` after the colon.
2. `Rel/Lang/Den.lean`: den :490/497, argDen :509/512, den_congr :682/716, den_pol_spine :954/1027, den_linIn :1099/1100,
   den_local :1233/1261/1263.
3. `Rel/Lang/GenSound.lean`: GenHyp :199-200, monoOK :214-216, pol_of_fv :1499, numGeneric :1716, number_spine :1762, number_spec :1785.
4. `Rel/Lang/EmitC.lean`: nodeB :1491/1515, argB :1541.  `Rel/Lang/GenSoundTest.lean` :113-143 (`call` has the new `cv` arg).
5. `Rel/Programs/Prelude.lean:43-44` comment mentioning `Tm.own`; `Registry.call?` (`Expand.lean` ~1020) check that a name does not determine the body.
6. Tests: `#guard` with a program using `perm°`; a program `(f° g)°` with a user definition `f` (derived converse).
7. Docs: PLAN.md B9b/B9c -> one merged line; `doc/rel-architecture.zh.typ` ~187, ~189; `doc/tm-minimal-design.zh.typ` ~282-284; `typst compile` both.
8. Build: `CAP_MEM_MB=20000 /home/dh/repo/freyd/scripts/cap lake build` of the edited modules, then `RelRun Rel`.
