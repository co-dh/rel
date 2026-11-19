import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- arc consistency on `y = x²` with both arcs, `x → y` by `sq` and `y → x` by `sq°`
open Rel.Programs.prelude in
rel_program square where
    obj V = {x,y}
    obj D = 0…9
    A : V ⟶ V ≜ {(x,y)}
    Ac : V ⟶ V ≜ A°
    sq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}
    sqc : D ⟶ D ≜ sq°
    uV : V ⟶ V ≜ 𝟙(V)
    uD : D ⟶ D ≜ 𝟙(D)
    s : V ⟶ D ≜ ⊤(V,D)
    z : V ⟶ D ≜ νZ : s ∩ (A\(Z sq)) ∩ (A°\(Z sq°))
    check z = {(x,0),(x,1),(x,2),(x,3),(y,0),(y,1),(y,4),(y,9)}
#guard square.ok

/-! `ν` of an AC-3 body runs by delta rounds (`Alg.acFix`): its result against the naive rounds (`Alg.fixOn` on
    `Alg.acRound`, called directly), and each path's work per round. -/

/-- An AC-3 body read from the definitions `gs`: the bound `s`, the arcs `(A, C)` by name, the universes `uv`,
    `ud`. -/
def acOf (gs : List (String × Gen.Gv)) (s uv ud : String) (arcs : List (String × String)) :
    Option ((V : Obj) × (D : Obj) × Tab V D × Tab V V × List (Revise V D)) := do
  let (_, ⟨V, D, sR⟩) ← gs.find? (·.1 == s)
  let UV ← get gs uv V V; let UD ← get gs ud D D
  let as ← arcs.mapM fun (a, c) => return (⟨← get gs a V V, ← get gs c D D, UV, UD⟩ : Revise V D)
  pure ⟨V, D, sR.rel, UV, as⟩

/-- The language's `z`, the delta rounds and the naive rounds give one relation. -/
def acAgree (gs : List (String × Gen.Gv)) (z s uv ud : String) (arcs : List (String × String)) : Bool :=
  match acOf gs s uv ud arcs with
  | some ⟨V, D, s, U, as⟩ =>
    let d := (acFix s as U).1; let n := (fixOn (s.n.toNat + 1) (acRound s as) s).1
    d == n && (get gs z V D).any (· == d)
  | none => false

/-- One round's work: the cells divided over `Σₖ |ran(Δ Aₖ)|`, and the rows the divisions join `Σₖ |(Δ Aₖ)° (Δ X Cₖ)|`. -/
def acWork {V D : Obj} (as : List (Revise V D)) (X : Tab V D) (Δ : Tab V V) : Nat × Nat :=
  as.foldl (fun (c, j) a => let R := (Δ ≫ a.A).nub
    (c + (Alg.ran R).n.toNat, j + (R° ≫ (Δ ≫ X ≫ a.C).nub).n.toNat)) (0, 0)

/-- The delta rounds' work, until `Δ = 𝟘`. -/
def deltaTrace {V D : Obj} (as : List (Revise V D)) : Nat → Tab V D → Tab V V → List (Nat × Nat × Nat)
  | 0, _, _ => []
  | f + 1, X, Δ => if Δ.n == 0 then [] else
    let (X', Δ') := acDelta as (X, Δ); let w := acWork as X Δ
    (w.1, w.2, X'.n.toNat) :: deltaTrace as f X' Δ'

/-- The naive rounds' work, until a round leaves the row count. -/
def naiveTrace {V D : Obj} (s : Tab V D) (as : List (Revise V D)) (U : Tab V V) :
    Nat → Tab V D → List (Nat × Nat × Nat)
  | 0, _ => []
  | f + 1, X => let X' := (acRound s as X).nub; let w := acWork as X U
    (w.1, w.2, X'.n.toNat) :: if X'.n == X.n then [] else naiveTrace s as U f X'

/-- Both traces: per round (cells divided over, rows joined, rows of `X` after). -/
def acTraces (gs : List (String × Gen.Gv)) (s uv ud : String) (arcs : List (String × String)) :
    List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  match acOf gs s uv ud arcs with
  | some ⟨_, _, s, U, as⟩ => (deltaTrace as (s.n.toNat + 1) s.nub U, naiveTrace s as U (s.n.toNat + 1) s.nub)
  | none => ([], [])

open Rel.Programs.prelude Programs.csp Programs.sudokuac in
rel_program sudokuEx where
    uV : Cell ⟶ Cell ≜ 𝟙(Cell)
    uD : D ⟶ D ≜ 𝟙(D)
    ne : D ⟶ D ≜ ≠

/-- `sudokuac`'s definitions and the universes and order `sudokuEx` adds. -/
def sudokuGs : List (String × Gen.Gv) := sudokuEx.expanded ++ Programs.sudokuac.expanded

#guard acAgree sudokuGs "s" "s₀" "uV" "uD" [("peer", "ne")]
#guard acAgree square.expanded "z" "s" "uV" "uD" [("A", "sq"), ("Ac", "sqc")]
-- SudokuAC, both 11 rounds, 489 → 81 rows: the delta rounds join 39780 rows in all, the naive ones 148200
#guard acTraces sudokuGs "s₀" "uV" "uD" [("peer", "ne")] ==
  ([(81, 13980, 183), (81, 9100, 163), (81, 3140, 142), (80, 3640, 122), (80, 3120, 113), (68, 1520, 107),
    (71, 1020, 103), (42, 680, 93), (65, 1660, 83), (73, 1600, 81), (34, 320, 81)],
   [(81, 13980, 183), (81, 13900, 163), (81, 13800, 142), (81, 13660, 122), (81, 13540, 113), (81, 13440, 107),
    (81, 13380, 103), (81, 13340, 93), (81, 13200, 83), (81, 13000, 81), (81, 12960, 81)])


end Rel.Lang.Test
