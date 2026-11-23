# 8.2d handoff

Design: `ValsB (o : Bool) : Obj → USize → Type` (o a PARAMETER, matched only through `ColB o t n`, so sum/prod/one reduce
at a variable o), `Vals := ValsB false`, `ColB false = Arr`, `ColB true = Opt`. Summand columns of a dense sum are
`ValsB true`. Generic functions were renamed `Vals.* -> ValsB.*` (row view ofOpt ofGen gather concat cols cellsOk
rowsImpl) so that field notation on `x : Vals A n` still finds them by unfolding `Vals`; `Vals.enc`/`Vals.get`
(Core.lean) keep `x.enc`/`x.get i` working on atom sides.

## Done (committed, built green)
Rel.Run.Core, Gather, Cols, Canon, Struct (Opt.fill, Vals.lift/unlift/zeros/none; Arr.dflts deleted), Arith, Cast, Div,
Lang.Gen (sumV takes ValsB true summands), doc/rel-architecture.zh.typ line 74 (typst compile NOT yet run).

## Left, first errors
- `Rel/Run/List.lean:50:67` `Vals.pack` on a sum's `.gen` summands: `ValsB.ofGen h tag (← Vals.pack x) ...` gets
  `ValsB true`; `Vals.pack`/`cells`/`tau`/`cat`/`zip` must become ValsB-generic (arr lo/hi are `ColB o .i64`).
- `Rel/Run/Lang/Plan.lean:550:102` `cols a x ...` on a `ValsB true` summand.
- Not yet reached: RepCanon (Vals.WF -> `ValsB.WFOn x P`: Opt leaf `isNul i = true <-> ¬P i`; gen sum
  `(∀ i, ¬P i → tag.get i = false) ∧ WFOn x (P ∧ ¬tag) ∧ WFOn y (P ∧ tag)`; `Vals.WF x := x.WFOn (fun _ => True)`),
  RepCols, RepStruct (`Vals.zeros_ok`, `Vals.ofGen_wf`, `inl/inr` laws; `Opt.nuls_get` is kept; add an `Opt.fill`
  lemma, `Opt.fill t n = Opt.nuls t n` for t ≠ general), RepTabDiv, RepWF (`pack_wf` filler clauses).
- Test in Core.lean: `tsum` summands now `Opt.ofArr`.
- Later agent (as scoped): readVals/encVals/cellsOk ownership mask, GenKBits/GenSound, EmitC, tests, and
  `ColB`-generic `Vals.gather` for `Opt` null rows needs no change (kgather moves flags).
