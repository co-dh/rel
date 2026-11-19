import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-- `plan`'s moves in the order of their step. -/
def moves (gs : List (String × Gen.Gv)) : Option (List (Int64 × Int64)) :=
  (get gs "plan" .long XX).map fun R => (R.nub.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

open Rel.Programs.prelude Programs.blocks in
rel_program given where
    qR : [X×X] ⟶ X×X ≜ QR(∋)
    qM : [X×X] ⟶ X×X ≜ QM(∋)
    qF : [X×X] ⟶ X×X ≜ Qc⇝
    qh : [X×X] ⟶ [X×X] ≜ Qh(∋)

-- the program with the start state and the goal replaced
rel_program table from Programs.blocks where
    S₀ : X ⟶ X ≜ {(A,A),(B,B),(C,C)}
    G : X ⟶ X ≜ {(A,B),(B,C)}
rel_program cycle from Programs.blocks where
    S₀ : X ⟶ X ≜ {(A,A),(B,B),(C,C)}
    G : X ⟶ X ≜ {(A,B),(B,A)}

open Rel.Programs.prelude Programs.blocks in
rel_program printPlan where
    print plan

#guard given.ok && table.ok && cycle.ok
-- the file's own `check plan = …` holds and it prints nothing; `plan` printed here is the move list below
#guard Programs.blocks.ok && Programs.blocks.prints == [] && given.prints == []
#guard printPlan.prints == ["plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}"]
#guard moves Programs.blocks.expanded == some [(2, 2), (1, 2), (0, 1)]
#guard moves table.expanded == some [(1, 2), (0, 1)]
#guard moves cycle.expanded == some []

/-! The elaborated definitions, as sets, on the reachable states. -/

/-- The definition `n` of `given` or of the program it extends at `St ⟶ B` holds the rows `xs`, whatever their
    order and multiplicity. -/
def rowsAre {B : Obj} [BEq B.El] (n : String) (xs : List (St.El × B.El)) : Bool :=
  match get (given.expanded ++ Programs.blocks.expanded) n St B with
  | some R => R.toList.all xs.contains && xs.all R.toList.contains
  | none => false

/-- The 13 states reachable from `S₀`. -/
def reach : List St.El := [[(0, 0), (1, 1), (2, 0)], [(0, 0), (1, 2), (2, 0)], [(0, 0), (1, 1), (2, 1)],
  [(0, 0), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 1)], [(0, 1), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 2)],
  [(0, 0), (1, 0), (2, 2)], [(0, 0), (1, 2), (2, 2)], [(0, 1), (1, 1), (2, 0)], [(0, 2), (1, 0), (2, 2)],
  [(0, 0), (1, 0), (2, 1)], [(0, 1), (1, 2), (2, 2)]]

#guard rowsAre (B := St) "Q" (reach.map fun s => (s, s))
#guard rowsAre (B := XX) "qR" [([(0, 0), (1, 1), (2, 0)], 2, 0), ([(0, 0), (1, 2), (2, 0)], 1, 2),
  ([(0, 0), (1, 2), (2, 0)], 2, 0), ([(0, 0), (1, 1), (2, 1)], 2, 1), ([(0, 2), (1, 1), (2, 1)], 0, 2),
  ([(0, 2), (1, 1), (2, 1)], 2, 1), ([(0, 1), (1, 1), (2, 2)], 0, 1), ([(0, 2), (1, 1), (2, 2)], 0, 2),
  ([(0, 0), (1, 0), (2, 2)], 1, 0), ([(0, 0), (1, 2), (2, 2)], 1, 2), ([(0, 1), (1, 1), (2, 0)], 0, 1),
  ([(0, 1), (1, 1), (2, 0)], 2, 0), ([(0, 2), (1, 0), (2, 2)], 0, 2), ([(0, 2), (1, 0), (2, 2)], 1, 0),
  ([(0, 0), (1, 0), (2, 1)], 1, 0), ([(0, 0), (1, 0), (2, 1)], 2, 1), ([(0, 1), (1, 2), (2, 2)], 0, 1),
  ([(0, 1), (1, 2), (2, 2)], 1, 2)]
#guard rowsAre (B := St) "qh" [([(0, 1), (1, 2), (2, 2)], [(0, 1), (1, 2), (2, 2)])]

/-! The parser on each line of `Programs.blocks`: every composite and infix term in parentheses, as the note reads the
    formula (§c), not as the parser happens to print it. -/

#guard Programs.blocks.filterMap reading == [
    ("S₀", "{(C, A), (A, A), (B, B)}"),
    ("G", "{(A, B), (B, C)}"),
    ("R", "(S ∩ ∼𝟙)"),
    ("M", "∼((R(S)° ⊤) ∪ (⊤ R(S)))"),
    ("S'", "((S ∩ ∼(p ⊤)) ∪ p)"),
    ("h", "G ⊑ S"),
    ("c", "⟨𝟙, M(∋)⟩"),
    ("⇝", "S'((π₁ ∋), π₂)"),
    ("t", "(c Λ(⇝))"),
    ("s₀", "ran(Λ((⊤(X, X) ⟨𝟙, S₀⟩)))"),
    ("r", "(dom(s₀) Λ(⊤))"),
    ("L", "ran((r ⦇[⟨D, ((D ⊤) {(0, 0)})⟩, (π₁ ∪ (π₁ ⟨(π₁ B), (π₂ succ)⟩))]⦈))"),
    ("Q", "ran((L(s₀, t) π₁))"),
    ("H", "(Q h(∋))"),
    ("C", "L(H, (Q t)°)"),
    ("W", "((C π₁)° (C π₂))"),
    ("δ", "(Λ(W) est(≤))"),
    ("K", "((Q c) dom((((Λ(⇝) δ) succ) ∩ (π₁ δ))))"),
    ("≼", "(((π₁ <) π₁°) ∪ ((π₁ π₁°) ∩ ((π₂ ≤) π₂°)))"),
    ("σ", "(Λ((K π₂)) est(≼))"),
    ("nx", "(⟨dom(σ), σ⟩ Λ(⇝))"),
    ("Z", "L(s₀, nx)"),
    ("ζ", "((Z π₂)° (Z π₁))"),
    ("plan", "(ζ σ)"),
    ("check", "plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}")]


end Rel.Lang.Test
