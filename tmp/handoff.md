merge ROW-DFN handoff, round 2 (branch worktree-agent-afaae7ffa52641af7; 7beb52f merged in, no conflict).

DONE (in tmp/MergeDef.lean, a scratch file importing PreludeMerge/PreludeLoop/PreludeOrd; check it with
`env LEAN_PATH=<wt>/.lake/build/lib/lean lean <wt>/tmp/MergeDef.lean`, ~1 min):
- `Tm.mergeDef` (with `local notation "𝕊"` for the state `((B*×B*)×B*)`): the `obtain rfl : Tm.mergeDef (.var 1) = t' :=
  Except.ok.inj ht` example COMPILES, so the shape is confirmed against `prelude.merge.body`.
- In `Tm.mergeDef_row`: `hτ`, `hnil` (`nilDen x l ↔ l = []` by `simp [nilDen, Core.Rel.graph]`), the main
  `simp only [...]` and `refine outer _ _ fun s e w => ?_` work (T is unified).
- `outer` (any T with hT ⇒ `((⟨⟨𝟙,nilDen⟩,cat⟩ ≫ loopDen T) ≫ π₂) p ys ↔ ys = merge`): `generalize loopDen T = L`
  BEFORE simp (`loopDen` unfolds to `foldDen` under any simp). After the simp the goal is
    (∃ a b a1 b1 b2 b3, (((x = a1 ∧ y = b1) ∧ b2 = []) ∧ b3 = x ++ y) ∧ L (((a1,b1),b2),b3) ((a,b),ys)) ↔ ys = merge x y le
  the `rintro` in the file has one binder count wrong (error: Unknown identifier `h`, line 63) — fix the pattern to the
  goal above (6 existentials then the conjunction; the right-to-left witness is ⟨[], [], x, y, [], x ++ y, …⟩ with
  a,b the final lists `[]`, `[]`: currently it passes `[]`,`[]` first, which is right; check the nesting).

LEFT:
1. `hT` in `Tm.mergeDef_row` (the `sorry` at the end). With `Tm.den` + `Tm.dom_den` + `Val.bind` lookup in one
   `simp only` and then `rcases xs; rcases zs; simp [mstep]` the whole theorem hits the 200000 heartbeat limit.
   Plan: do not unfold `Tm.den` again; prove first, by `rfl`/`simp` per lemma, the meaning of the three environment
   terms that appear in T: `den ρ' (.var 2)` = `(π₁π₁) ≫ den ρ headAt`, `.var 3` likewise with π₁π₂, and
   `den ρ' L_DEF` (the `l` call) = `dom(⟨a,b⟩ cor Q) ∪ (dom a − dom b)` read pointwise as
   `s ↦ (s.1.1 ≠ [] ∧ s.1.2 ≠ [] ∧ Q (head xs) (head ys)) ∨ (s.1.1 ≠ [] ∧ s.1.2 = [])`; rewrite with those, then case on xs, zs.
   (`Tm.dom_den'` pointwise is in Rel.RepSymRank, not imported; `Tm.dom_den` (Den) is the relation form.)
2. Move `Tm.mergeDef`, `Tm.mergeDef_row`, and `Tm.mergeDef_den` (copy `Tm.estDef_den`, PreludeDfn.lean:63) into
   Rel/Lang/PreludeMerge.lean; add `public import Rel.Lang.PreludeLoop` and `Rel.Lang.PreludeOrd` there.
3. DRY in PreludeMerge.lean: delete `Prim.den_loop` (verbatim copy of `Prim.den_loopRow`, PreludeLoop.lean); inline
   `Tm.zeroLit` into `Tm.headAt` and replace the `hz` proof in `Tm.headAt_den` by `Tm.zeroLit_den` (PreludeOrd.lean:37)
   after `Gen.atom_zero` (as `Tm.ltDef_den` does: `have hz := Tm.zeroLit_den ρ; simp only [Tm.den] at hz`).
4. PreludeDen.lean:31 `unproved := []`. Delete tmp/handoff.md, tmp/MergeDef.lean, tmp/PrintMerge.lean from git.
5. Build `cap lake build Rel.Lang.PreludeMerge Rel.Lang.PreludeDen Rel.Lang.AllPrograms`; `make pointfree decode listban axioms`.
