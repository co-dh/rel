module

public import Rel.Lang.PlanSpec
public import Rel.RepCanon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `gatherCols` means `ValsB.gather` (`canonT_builds`, stage 1b)

A side `x : ValsB o A n` in registers is `ValsB.regVals x`, in `regsOf` order; `gatherB` of one register is
`kgather` of its `Enc`, which is what `ColB.gather` computes. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The register values of the side `x`, in `regsOf` order: an atom its `Enc`; a product its two sides'; an array its
    payload's count, `lo`, `hi`, then its payload's; a band sum its one `Opt`; a general sum its tag, then its two
    summands'; `1` none. -/
def _root_.Rel.ValsB.regVals : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → List Val
  | _, .atom _, _, x => [Reg.put (ColB.enc x)]
  | _, .prod _ _, _, x => ValsB.regVals x.1 ++ ValsB.regVals x.2
  | _, .arr _, _, ⟨c, lo, hi, f⟩ => [.size c, Reg.put (ColB.enc lo), Reg.put (ColB.enc hi)] ++ ValsB.regVals f
  | _, .sum _ _, _, s => match ValsB.view s with
    | .opt _ x => [Reg.put x.enc]
    | .gen _ tag x y => Reg.put tag.enc :: (ValsB.regVals x ++ ValsB.regVals y)
  | _, .one, _, _ => []

/-- Every `Enc` is a register that reads back as itself (`foR` its parts, `pos` none). -/
theorem enc_get_put : ∀ e : Enc, (Reg.get? (Reg.put e) : Option Enc) = some e
  | .foR m p => foR_get_put m p
  | .pos => by
    have hp : (Reg.put (Enc.pos : Enc) : Val) = .ctor (Enc.pos : Enc).ctorIdx #[] #[] := by with_unfolding_all rfl
    rw [hp]
    dsimp only [Reg.get?]
    conv => lhs; whnf
    rw [Array.mapM_eq_mapM_toList]
    simp

/-- `ColB.gather` is `kgather` of the column's `Enc`, at either ownership. -/
theorem ColB.gather_kgather : ∀ {o : Bool} {t : QAtomicType} {n m : USize} {ix : Enc} {x : ColB o t n}
    {y : ColB o t m}, ColB.gather m ix x = .ok y → kgather m ix n (ColB.enc x) = .ok (ColB.enc y)
  | false, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Arr.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h
  | true, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Opt.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h

/-- `gatherB m ix n e`, then `c`: the registers `m`, `n` hold the counts `mv`, `nv`, `ix` and `e` the `Enc`s `iv`,
    `ev`; the new register holds `kgather mv iv nv ev`. -/
theorem gatherB_builds {fg fg' : Array Fun × Array Fun} {rs out : Array Val} {m ix n e : Nat} {mv nv : USize}
    {iv ev ov : Enc} {c : Nat → Bld (Array Nat)}
    (hm : rs[m]? = some (.size mv)) (hi : rs[ix]? = some (Reg.put iv)) (hn : rs[n]? = some (.size nv))
    (he : rs[e]? = some (Reg.put ev)) (hk : kgather mv iv nv ev = .ok ov)
    (hc : Builds abiOf fg fg' (c rs.size) (rs.push (Reg.put ov)) out) :
    Builds abiOf fg fg' (gatherB m ix n e >>= c) rs out := by
  unfold gatherB
  refine Builds.call1 (vs := #[.size mv, Reg.put iv, .size nv, Reg.put ev]) (v := Reg.put ov)
    (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi, List.find?]) (by with_unfolding_all rfl) ?_ ?_ rfl hc
  · rw [List.mapM_toArray]
    simp [reg, hm, hi, hn, he]
    rfl
  · have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
    simp [arg, hsz, enc_get_put, hk, Out.out]
    rfl

end Rel.Lang.Plan
