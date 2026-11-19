import Rel.Lang.Test
import Rel.Lang.TestMss
import Rel.Lang.TestWumpus
import Rel.Lang.TestSelsort
import Rel.Lang.TestKnapsack
import Rel.Lang.TestCircuit
import Rel.Lang.TestHylo
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit
import Rel.Run.Lang.Compile

/-! The differential check of `compile` (`doc/rel-denotation-design.md` §5.1, stage 3): every closed definition of
    every registered program, its term run by `compile`, against the constant `rel_program` generated for it. Where
    `compile` vouches for its table (ok bit set) the generated constant must be ok with the same table; where it does
    not (a `call`, a row not fitting), the definition is counted, so the coverage is visible. -/

namespace Rel.Lang.TestCompile

open Lean Elab Command Tab Rel.Lang Rel.Lang.Expand

/-- No variable bound: a closed definition reads none, and a use of one vouches for nothing. -/
def η₀ : CodeEnv := fun _ _ _ => .closed (.pure (.zero, false))

/-- `t` against the generated constant `k`: `none` where they agree, `some false` where `compile` vouches for
    nothing, `some true` where they differ. `k` runs only where `compile` vouches: a not-ok row reads nothing of it,
    and a definition that runs to its cap would pay that run twice. -/
unsafe def differs (k : Name) {A B : Obj} (t : Tm A B) : CommandElabM (Option Bool) := do
  let c : CRel A B ← IO.lazyPure fun _ => (compile η₀ t).run {}
  if !c.ok then return some false
  let g ← IO.ofExcept ((← getEnv).evalConst (CRel A B) (← getOptions) k)
  pure (if g.ok && g.rel == c.rel then none else some true)

run_cmd do
  let reg := relRegistry.getState (← getEnv)
  let mut same := 0
  let mut open' : List String := []
  for (n, _, _) in reg.progs do
    let some (ds, _, _) := reg.reps[n]? | throwError "TestCompile: the program `{n}` has no numbered terms"
    for (x, r) in ds do
      let ⟨_, _, t⟩ := r
      if t.dem then continue
      match ← unsafe differs (Parse.constOf n x) t with
      | none => same := same + 1
      | some false => open' := open' ++ [s!"{n}.{x}"]
      | some true => throwError "TestCompile: `{n}.{x}`: compile's table is not the generated code's"
  logInfo m!"compile agrees with the generated code on {same} definitions; not ok on {open'.length}: {open'}"

end Rel.Lang.TestCompile
