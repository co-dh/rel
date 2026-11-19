import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

open Rel.Programs.prelude Programs.blocks in
/-- A body given families of two indices, `∋` at `St` and `ζ∋` at `N` (the `k`-th state's pairs), runs at
    `St×N`: the fibre at `(s,k)` is `s ∩ ζ(k)`. Against the same meet written by hand, and at `(s₀,0)`, `(s₀,1)`. -/
rel_program twoIdx where
    k(S : X ⟶ X, T : X ⟶ X) : X ⟶ X ≜ S ∩ T
    check (Q×𝟙(N))k(∋,ζ∋) = (Q×𝟙(N))⟨π₁∋,π₂ζ∋⟩cor(𝟙)π₁
    print (s₀×{(0,0)})k(∋,ζ∋)
    print (s₀×{(1,1)})k(∋,ζ∋)

-- `ζ(0) = S₀`; `ζ(1)` is `S₀` with `C` moved to the table
#guard twoIdx.ok && twoIdx.prints == [
  "s₀ × {(0, 0)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 0), (A, A)), (((A, A) (B, B) (C, A), 0), (B, B)), " ++
    "(((A, A) (B, B) (C, A), 0), (C, A))}",
  "s₀ × {(1, 1)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 1), (A, A)), (((A, A) (B, B) (C, A), 1), (B, B))}"]


end Rel.Lang.Test
