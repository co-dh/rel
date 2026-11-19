import Rel.Run.SetOps
import Rel.RepCanon
import Rel.Run.CRelFoldDef

/-! The laws of `Tab.union`, `Tab.inter`, `Tab.diff` and `Tab.le` (`Rel/Run/SetOps.lean`), from the five kernels' laws
and `Tab.canon`'s (`Rel/RepCanon.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-! ## Checks on `foR` tables -/

section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
private def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

private def T₁ : List (Int64 × Int64) := [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)]
private def T₂ : List (Int64 × Int64) := [(-2, 9), (-2, 9), (1, 2), (7, -3), (-5, -5), (3, 1)]
private def T₃ : List (Int64 × Int64) := [(0, 0), (9, 9)]

#guard ((tab T₁).union (tab T₂)).toOption.map Tab.toList ==
  some [(-5, -5), (-2, 9), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1), (7, -3)]
#guard ((tab T₁).inter (tab T₂)).toOption.map Tab.toList == some [(-5, -5), (1, 2), (3, 1)]
#guard ((tab T₁).diff (tab T₂)).toOption.map Tab.toList == some [(-1, 2), (0, 0), (2, 7)]
#guard ((tab T₂).diff (tab T₁)).toOption.map Tab.toList == some [(-2, 9), (7, -3)]
#guard ((tab []).inter (tab T₁)).toOption.map Tab.toList == some []
#guard ((tab T₁).diff (tab [])).toOption.map Tab.toList == some [(-5, -5), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1)]
#guard ((tab T₁).le (tab T₁)).toOption == some true
#guard ((tab T₁).le (tab T₂)).toOption == some false
#guard ((tab []).le (tab [])).toOption == some true
-- the five-kernel operators against the old `CRel.union`, `CRel.inter`, `CRel.diff`, `Alg.leC` on the same tables,
-- both orders; the old `∩`/`−` keep `R`'s order, so their answer is compared after `Alg.canonC`
#guard [T₁, T₂, T₃, []].all fun ps => [T₁, T₂, T₃, []].all fun qs =>
  let R := tab ps; let S := tab qs
  let old (c : CRel .long .long) := c.bind fun t => let c := Alg.canonC t; if c.2 then some c.1.toList else none
  ((R.union S).toOption.map Tab.toList) == old (CRel.union (some R) (some S)) &&
  ((R.inter S).toOption.map Tab.toList) == old (CRel.inter (some R) (some S)) &&
  ((R.diff S).toOption.map Tab.toList) == old (CRel.diff (some R) (some S)) &&
  (R.le S).toOption == (let c := Alg.leC R S; if c.2 then some c.1 else none)

end Checks

end Rel
