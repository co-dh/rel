import Rel.Programs.Prelude

/-! The divisions lifted (§e, `binaryL`): an operator with parameters `N ⟶ N` given the families `Rk Sk : K ⟶ N×N`
    runs its body at each key. Each lifted division against the rows worked by hand from its definition, against
    the same division of the fibres unlifted, and against its definition by the rows `∼ ∘ °`. -/

namespace Rel.Lang.TestLiftDiv

rel_program liftDiv where
    obj K = 0…1
    obj N = 0…1
    Rk : K ⟶ N×N ≜ {(0,(0,0)),(0,(0,1)),(0,(1,0)),(1,(1,1))}
    Sk : K ⟶ N×N ≜ {(0,(0,0)),(0,(1,1)),(1,(0,1))}
    R₀ : N ⟶ N ≜ {(0,0),(0,1),(1,0)}
    S₀ : N ⟶ N ≜ {(0,0),(1,1)}
    R₁ : N ⟶ N ≜ {(1,1)}
    S₁ : N ⟶ N ≜ {(0,1)}
    rd(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ R/S
    ld(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ R\S
    sd(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ R ÷ S
    rdRows(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ ∼((∼R)S°)
    ldRows(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ ∼(R°(∼S))
    sdRows(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ ∼((∼R)S°) ∩ (∼((∼S)R°))°
    check rd(Rk,Sk) = {(0,(0,0)),(0,(0,1)),(0,(1,0)),(1,(0,1)),(1,(1,0)),(1,(1,1))}
    check R₀/S₀ = {(0,0),(0,1),(1,0)}
    check R₁/S₁ = {(0,1),(1,0),(1,1)}
    check rd(Rk,Sk) = rdRows(Rk,Sk)
    check ld(Rk,Sk) = {(0,(1,0)),(1,(0,0)),(1,(0,1))}
    check R₀\S₀ = {(1,0)}
    check R₁\S₁ = {(0,0),(0,1)}
    check ld(Rk,Sk) = ldRows(Rk,Sk)
    check sd(Rk,Sk) = {(0,(1,0)),(1,(0,1)),(1,(1,0))}
    check R₀ ÷ S₀ = {(1,0)}
    check R₁ ÷ S₁ = {(0,1),(1,0)}
    check sd(Rk,Sk) = sdRows(Rk,Sk)

-- by hand, at key 0: `R₀ 0 = {0,1}`, `R₀ 1 = {0}`, `S₀ 0 = {0}`, `S₀ 1 = {1}`; `a (R/S) c ⟺ S c ⊆ R a`, so `c = 0`
-- takes `a ∈ {0,1}` and `c = 1` takes `a = 0`. At key 1: `R₁ 1 = {1}`, `S₁ 0 = {1}`, `S₁ 1 = ∅`, so `c = 0` takes
-- `a = 1` and `c = 1` every `a`. `b (R\S) c ⟺ R°b ⊆ S°c`; `÷` pairs the equal images (`(R₀,S₀)`: `1 ↦ 0`).
#guard liftDiv.ok

end Rel.Lang.TestLiftDiv
