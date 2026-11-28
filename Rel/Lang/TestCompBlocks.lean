import Rel.Run.Lang.EmitC

/-! `compWithB bound` against `Tab.compWith bound` at a small bound, so the block loop runs on a handful of rows: the
    plan's answer (row count and the words of both columns) is the model's, in the one-block branch, the cut branch
    with several blocks, and the cut branch with a single block (`nb = 1`, no loop round). -/

namespace Rel.Lang.TestCompBlocks

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel

abbrev I := Obj.atom .i64

/-- The table of the sorted, distinct pairs `ps`. -/
def tab (ps : List (Nat × Nat)) : Tab I I :=
  let a := ps.toArray
  ⟨a.size.toUSize, Arr.ofFn .i64 a.size.toUSize fun i => (a[i.1]?.getD (0, 0)).1.toUInt64,
    Arr.ofFn .i64 a.size.toUSize fun i => (a[i.1]?.getD (0, 0)).2.toUInt64⟩

/-- The plan's table in registers: its count and one `i64` column per side, each a literal. -/
def tabB (T : Tab I I) : Bld TabB := do
  pure ⟨← lit (.size T.n), [.atom "" .i64 (← lit (Reg.put T.key.enc))], [.atom "" .i64 (← lit (Reg.put T.val.enc))]⟩

/-- The plan of `compWithB bound R S` run: the answer's row count and the words of its two columns. -/
def planAns (bound : Nat) (R S : Tab I I) : IO (Nat × Array UInt64 × Array UInt64) := do
  let b : Bld TabB := do compWithB bound (← tabB R) (← tabB S)
  let (T, is, _, fs, gs) ← match b.run (#[], 0, #[], #[]) with
    | .ok r => pure r | .error e => throw (IO.userError s!"plan: {e}")
  let (rs, _) ← match ({ funs := fs, globals := gs, main := is.toList : Plan }).run abiOf with
    | .ok r => pure r | .error e => throw (IO.userError s!"run: {e}")
  let .size n := rs[T.n]?.getD (.bit false) | throw (IO.userError "the answer's count is no size")
  let w (cs : Cols) : IO (Array UInt64) := match cs with
    | [.atom _ _ e] => match rs[e]?.bind (Reg.get? (α := Enc)) with
      | some e => pure (Enc.raw .i64 n e)
      | none => throw (IO.userError "an answer column is no Enc")
    | _ => throw (IO.userError "the answer is not two atom columns")
  pure (n.toNat, ← w T.key, ← w T.val)

/-- `compWithB bound R S` answers what `Tab.compWith bound R S` does. -/
def agree (bound : Nat) (R S : List (Nat × Nat)) : IO Unit := do
  let (R, S) := (tab R, tab S)
  let M ← match R.compWith bound S with
    | .ok M => pure M | .error e => throw (IO.userError s!"model: {e}")
  let (n, k, v) ← planAns bound R S
  let want := (M.n.toNat, Enc.raw .i64 M.n M.key.enc, Enc.raw .i64 M.n M.val.enc)
  unless (n, k, v) == want do throw (IO.userError s!"bound {bound}: plan {(n, k, v)}, model {want}")
  IO.println s!"bound {bound}: {n} rows agree"

-- 6 × 6 rows over 3 middle values, 12 output rows, windows of 4: three blocks, so two loop rounds
#eval agree 4 ((List.range 6).map fun i => (i, i % 3)) ([(0, 0), (0, 3), (1, 1), (1, 4), (2, 2), (2, 5)])
-- the product is past the bound, the expansion (4 rows) is not: one block
#eval agree 4 ((List.range 4).map fun i => (i, i)) ((List.range 5).map fun i => (i, i))
-- one group of 9 rows past the bound: a single block, no loop round
#eval agree 4 [(0, 0), (1, 0), (2, 0)] [(0, 0), (0, 1), (0, 2)]
-- a bound past `2^63`: never cut
#eval agree (2 ^ 64) ((List.range 6).map fun i => (i, i % 3)) ([(0, 0), (0, 3), (1, 1), (1, 4), (2, 2), (2, 5)])

end Rel.Lang.TestCompBlocks
