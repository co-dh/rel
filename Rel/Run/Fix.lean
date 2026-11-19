import Rel.Run.Struct

/-! The fixed points `νX : top ∩ f(X)` and `μX : f(X)` of `Tab` (`doc/rel-architecture.zh.typ` §4): a Lean loop
calling the operations until the row count stops, the rule of the old `CRel.fixOn` (`Rel/Run/CRelLoopDef.lean`)
over the five-kernel `Tab.inter` and `Tab.union` (`Rel/Run/SetOps.lean`). Each round is met with (`ν`) or joined to
(`μ`) the table before it, so the rounds form a chain whatever `f` is, and on a chain of canonical tables an equal row
count is an equal relation. -/

namespace Rel

namespace Tab
variable {A B : Obj}

/-- `step` from `X`, at most `n` rounds, until a round leaves the row count as it was; that round's table. A round
of `step` that fails fails the loop, and `n` rounds with the count still moving fail it: never a truncated chain
passed off as the answer. -/
def fixOn (step : Tab A B → Except String (Tab A B)) : Nat → Tab A B → Except String (Tab A B)
  | 0, X => throw s!"Tab.fixOn: the row count still moved at {X.n} rows when the rounds ran out"
  | n + 1, X => do let Y ← step X; if Y.n == X.n then pure Y else fixOn step n Y

/-- **`νX : top ∩ f(X)`**: rounds `X ↦ X ∩ f(X)` from `top` made canonical. A strict round drops a row of the
canonical `top`, so its row count plus one rounds reach the fixed point; the old `Gen.nu`'s `+ 2` is kept. -/
def nu (f : Tab A B → Except String (Tab A B)) (top : Tab A B) : Except String (Tab A B) := do
  let T ← top.canon
  fixOn (fun X => f X >>= X.inter) (T.n.toNat + 2) T

/-- **`μX : f(X)`**: rounds `X ↦ X ∪ f(X)` from `𝟘`, fewer than `cap` of them, the old `Gen.mu`'s bound: `cap`
rounds run fails, the chain has no fixed point that the program's bound admits. -/
def mu (cap : Nat) (f : Tab A B → Except String (Tab A B)) : Except String (Tab A B) := do
  fixOn (fun X => f X >>= X.union) (cap - 1) (← Tab.zero)

/-- **The rounds of a fold** (`fold`, `foldr`, `foldI`), at most `f`: `rest` holds at each key `k` the part of its
array not yet read, `P` its values so far. A round moves the rows of `P` whose key has no element left (`P − dom(el) P`)
to `out`, `peel` splits each `rest` into the element read now and the rest (`cons°` or `snoc°`), and `step` gives the
next values; it ends when `P` is empty, so one round more than the longest array. -/
def foldRounds {K E V : Obj} (peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E)))
    (step : Tab K V → Tab K E → Except String (Tab K V)) :
    Nat → Tab K (.arr E) → Tab K V → Tab K V → Except String (Tab K V)
  | 0, _, P, _ => throw s!"Tab.foldRounds: {P.n} rows still folding when the rounds ran out"
  | f + 1, rest, P, out => do
    if P.n == 0 then return out
    let (el, rest') ← peel rest
    foldRounds peel step f rest' (← step P el) (← out.union (← P.diff (← (← el.dom).comp P)))

end Tab

end Rel
