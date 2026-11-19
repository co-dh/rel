import Rel.Lang.Test

/-! A `ν` whose AC-3 body has a second conjunct `t` free of the variable besides the seed `s`, with `s ⋢ t`:
    `Expand.arcs` skips every conjunct free of the variable, so the result is right only if `t` reaches the seed
    `Gen.nuAC` starts from. It does: `Pre.bound` makes the seed the meet of all such top-level conjuncts. -/

namespace Rel.Lang.TestArcs

open Tab Rel.Lang Rel.Lang.Test

-- ⟦z⟧ = gfp below s ∩ t, t keeping y ∈ {0,2}. (v,d) ∈ A\(Z e) iff ∀w. w A v ⇒ (w,d) ∈ Z, so A = {(y,x)} needs
-- (y,d) ∈ Z at x: x ∈ {0,2}, and {(x,0),(x,2),(y,0),(y,2)} is a fixed point. With t lost the seed is s = ⊤, where
-- the arc removes nothing: all 6 rows. z₁ nests t with the arc, z₂ puts it last, z₃ names s ∩ t.
-- `nuAC` is the old layer's: the kernel path runs `ν` as plain rounds
set_option rel.kernel false in
open Rel.Programs.prelude in
rel_program arcsT where
    obj V = {x,y}
    obj D = 0…2
    A : V ⟶ V ≜ {(y,x)}
    e : D ⟶ D ≜ {(0,0),(1,1),(2,2)}
    s : V ⟶ D ≜ ⊤(V,D)
    t : V ⟶ D ≜ {(x,0),(x,1),(x,2),(y,0),(y,2)}
    st : V ⟶ D ≜ s ∩ t
    uV : V ⟶ V ≜ 𝟙(V)
    uD : D ⟶ D ≜ 𝟙(D)
    z₁ : V ⟶ D ≜ νZ : s ∩ (t ∩ (A\(Z e)))
    z₂ : V ⟶ D ≜ νZ : s ∩ (A\(Z e)) ∩ t
    z₃ : V ⟶ D ≜ νZ : st ∩ (A\(Z e))
    print z₁
    print z₂
    check z₁ = {(x,0),(x,2),(y,0),(y,2)}
    check z₂ = {(x,0),(x,2),(y,0),(y,2)}
    check z₁ = z₃
#guard arcsT.ok
#guard arcsT.prints == ["z₁ = {(x, 0), (x, 2), (y, 0), (y, 2)}", "z₂ = {(x, 0), (x, 2), (y, 0), (y, 2)}"]
-- the delta rounds from the seed `s ∩ t` give `z₁`
#guard acAgree arcsT.expanded "z₁" "st" "uV" "uD" [("A", "e")]
-- every `ν` above took the AC path: the module's constants call `Gen.nuAC` and never the general `Gen.nu`
run_cmd do
  let env ← Lean.getEnv
  let uses (c : Lean.Name) := env.constants.map₂.toList.any fun (_, i) =>
    i.value?.any (·.getUsedConstants.contains c)
  unless uses ``Gen.nuAC && !uses ``Gen.nu do Lean.throwError "a ν of arcsT did not take the AC path"

end Rel.Lang.TestArcs
