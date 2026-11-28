import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA10_3_Tardy

/-! # Laws of freyd §10.3 (`AOP/A10_3_Tardy.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA10_3_Tardy where
    -- the step `pick (X×𝟙) arm₂ α` of `schedule`, with `pick ⊑ H`, `H = Λ(arm₂ β°) est(Q')`, `Y = (X×𝟙) arm₂ α`
    theorem pickBranchLe(P : β ⟶ γ×δ, H : β ⟶ γ×δ, Y : γ×δ ⟶ ε) if P ⊑ H : P Y ⊑ H Y by Rel.Lang.Tm.pickBranchLe_den  -- Freyd.Alg.RelSet.Tardy.pick_branch_le, 10-greedy.typ:478
    theorem gInl(Z : α ⟶ γ, P : β ⟶ γ) : inl [Z, P] = Z by Rel.Lang.Tm.gInl_den  -- Freyd.Alg.RelSet.Tardy.gFn_inl (g ≜ [zero, penalty]), 10-greedy.typ:339

-- not ported: R_eq (Freyd.Alg.RelSet.Tardy.R_eq, 10-greedy.typ:321): `R` is defined here as `cost ≤ cost°`, so the statement is a syntactic identity; and `cost` needs the arithmetic below
-- not ported: bagify_cata (…bagify_cata, 10-greedy.typ:309): `Bag Job` is a quotient of lists by permutation, an object rel has no type for (no quotient object, no `Bag` row)
-- not ported: penalty_eq_bagPenalty (…, 10-greedy.typ:361): the same `Bag Job` quotient, and `penalty` needs integer subtraction and multiplication
-- not ported: cost_alg_bmax (…, 10-greedy.typ:394), cost_alg_k (…, 352), k_mono (…, 367), tardy_mono (…, 379), tardy_tail (…, 41): they state laws of `cost`, `g`, `m`, `k`, `bmax`, which need subtraction, multiplication and binary maximum on signed integers; the prelude has only `plus`, `succ` and the order rows, and a negative penalty has no value in an unsigned `obj`. They also use `F.map` of a relator (`Fobj Unit Job`) and `Bag Job`
-- not ported: tardy_branch (…, 10-greedy.typ:476): `est_arm₂_le` at `[nil,snag]` over the relator `F Unit Job` with `Bag Job`; its premise `nil_snag_disjoint` is `nil_ne_snag` on the bag quotient
-- not ported: run_cands, run_chosen, run_sched, run_cost (…, 10-greedy.typ:492, 500, 504, 508): the run is on `jobs3`, whose penalties `(ctsum + ct − dt) × wt` are negative for job 0 (`2 − 3`), so no unsigned `obj` holds them, and `chosen`/`sched` need `cost`, `bagPenalty` and the `Bag Job` quotient

end Rel.Programs
