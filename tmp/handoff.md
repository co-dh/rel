# tm28b6b handoff (Tm28 B6: Tm.foldI -> fused prim row foldI)

Branch tm28b6b, from 5d7704e (tm28b6a). WIP commit made at the 40-call checkpoint, not yet built.

Done (edits, unbuilt):
- Deleted `Tm.foldI`, `Pre.foldI` and every arm (Tm, TmGen, Elab, ConvSpec, Den, GenSound, GenSoundTest).
- Syntax: `foldIRow` (sig [e : I ⟶ V×V, S : (I×V)×E ⟶ I×V], I×[E] ⟶ V), last in the main `prims` list after `$`.
- Den: `RowCode.foldI`, `Sem.two`, `Sem.two_mono`, rowDens entry (Sem.two ... foldIDen), rowDens_mono case.
- GenK: `kernRows` moved after `end GenK` (end of file) so ``GenK.foldI`` resolves; entry ("foldI", ``GenK.foldI).
- Elab: `lFold` emits `.prim foldIRow [e, S'] (.prod I (.arr x)) v`; `DfnCut.foldI` + uni/fused/cut; `dfns` "foldI".
- DfnLaw: `Prim.den_foldIRow`, `Tm.dfnCut_den` foldI case via `foldIDen_eq.symm`, `Prim.dfn_read`.
- GenSound: `rowOK_foldI`, rowsProved entry, rowsProved_ok case h33.

Left:
- Build `Rel.Lang.GenSoundTest Rel.Lang.DfnLaw Rel.Lang.ConvSpec`, fix fallout (rowOK_foldI's split shapes are a guess).
- `#guard` in GenSoundTest: a lifted fold whose e/S mention the mu variable is still `monoOK`.
- Gates: full build, make decode-allow panic-allow bang-allow pointfree, compile-diff, PLAN line.
