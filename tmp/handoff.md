# tm28b6a handoff (n-arg rows, then B6 foldI)

Done (WIP, not yet built green):
- Rel/Run/Lang/Tm.lean: `Tm.pol` + new `Tm.spinePol` in one `mutual` block; `.arg f x` case is
  `f.spinePol s k && x.pol s k || !t.fv.contains k`.
- Rel/Lang/Den.lean: `Sems.le`, `Sems.sle`, `Sems.sle.nil/cons`; `Sem.one_mono`, `rowDens_mono`, `Prim.den_mono`
  over `Sems.le ss ss'` (any length); `Tm.den_pol_spine` (conjunction motive: den half + argDen-of-spine half),
  `Tm.den_pol` derived from it.
- Rel/Run/Lang/Expand.lean `primE`: after the wrappers, a constant that is itself an `Fn` combinator of its
  relations (any number, `GenK.foldI`) is fitted directly; tried last so no existing row's fit changes.

Left:
- build `Rel.Lang.Den Rel.Run.Lang.TmGen`, then GenSound/DfnLaw/GenSoundTest; fix fallout.
- B6: foldIRow in Syntax `prims`, `RowCode.foldI` + `Sem.two` rowDens entry, kernRows ("foldI", GenK.foldI),
  `DfnCut.foldI`, `dfns` entry, `Tm.dfnCut_den` case via `foldIDen_eq.symm`, `Prim.dfn_read`, `lFold`
  (Elab ~:984) emits `Pre.prim foldIRow [e, S']`, delete `Pre.foldI`, `Tm.foldI` and every match arm (Tm.lean
  68/137/147/183/233/289/336, Den 462/510/922, TmGen 180/239/324, Elab 293/385/595/2001/2399, ConvSpec 136/526,
  GenSound 114/130/972, GenSoundTest 102), `rowOK_foldI` from `GenK.foldI_sound`, rowsProved entry.
