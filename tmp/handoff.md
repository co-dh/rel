# 8.2b handoff (agent a7284d04)

Base: merged 8b3487e (8.2 wip) clean. Edited: Rel/Run/Struct.lean, Rel/RepStruct.lean. NOT yet built green.

## Key finding
`Vals.zeros` rows were word 0, but `Obj.dflt (.atom t)` is `Carrier.null t` (q null; i64: -2^63), so "zeros rows = dflt"
was false for atoms. Fixed in Struct.lean: `Arr.dflts t n` (post chain `[(.and,0),(.or, word t null)]`), `Vals.zeros .atom`
uses it; `tagCol` moved before `Vals.zeros`, the sum filler tag is `tagCol n false`. Filler-on-read (task item 3) must
therefore compare against the null word `QAtomicType.word t default`, not 0.

## RepStruct.lean state (new, first block before `namespace Tab`)
`Opt.nuls_get` (moved up), `tagCol_get`, `Arr.dflts_get`, `Vals.zeros_ok` (WF and rows = dflt, induction on A),
`Vals.ofGen_wf`, `Vals.none_wf` (= zeros_ok at 0). `injCols_ok` deleted. inl/inr_wf, inl/inr_holds use zeros_ok.
Helpers in Tab block: `Vals.gather_tag_valid`, `selConv_holds` (whereCol-selected rows), used by the gen cases of
`inlConv_holds` / `inrConv_holds` (mask via colMap_raw for `.not`, `Arr.get_u1` for the tag words).

## Errors seen in the last build (Rel.RepStruct), to fix
- `Arr.dflts_get`: `ht : t ≠ .general` proof leaves `foR` goal (add `QAtomicType.width` to the simp set); `storeFmt?.isSome`
  is FALSE for `.u1`, `.sym` so `Tab.of_atomOfBits` (also in RepTabArith, not imported) cannot be used: prove
  `∀ a, (Dep.Carrier.of? t (.atom (Column.atomOfBits t a ht))).getD default = QAtomicType.ofBits t a` and
  `ofBits t (word t default) = default` by `cases t <;> first | exact absurd rfl ht | rfl/decide`; then for u1 the word is `c % 2`.
- `Vals.zeros_ok` `.arr` case: `split at h` names shifted (`hhi : Except.ok lo = Except.ok hi`); use
  `cases hlo : Arr.zeros .i64 n` (both lo, hi are the same term) then `cases hf : Vals.zeros b 0`.
- `Vals.ofGen_wf` statement: `none` resolves to `Vals.none` inside `theorem Vals.…`; write `Option.none`.
- `inl_wf`/`inr_wf`: `Vals.ofGen_wf`'s implicit `h` not synthesised; use `refine canon_wf h ⟨hX, ?_⟩; exact Vals.ofGen_wf …`.
- `Vals.gather_tag_valid`: `Arr.valid_of_gather` is in Rel.Lang.GenKBits (not imported by RepStruct); `Tab.gather_valid` is in
  RepCast. Prove from `kgather` success (`kgather_valid`, find its module) or move.
- inl_holds/inr_holds gen branch: `simp only [Vals.row, Vals.view_ofGen, tagCol_get htg k, …]` leaves goals; add `rfl`/`Obj.dflt` as needed.

## Not started
Task items 2 (port RepWF, RepTabDiv, GenKBits, GenSound, tests TestTable/TestIO/TestNullband), 3 (filler on read: readVals /
encVals / cellsOk in Rel/Run/Table.lean; per-block check `foR` frame = null word, width 0, no patch), 4 (dead code deletion once
the index shows no callers), 5 (PLAN.md 8.2 line).
