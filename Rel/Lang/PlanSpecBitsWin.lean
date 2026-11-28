module

public import Rel.Lang.PlanSpecBits
public import Rel.Lang.PlanSpecFix
public import Rel.Lang.PlanSpecPack

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `bitsWinB` builds `Tab.bitsWin` (PLAN-THM-E12)

`bitsWinB bits T na g w` is `leW na ∧ leW g ∧ (na·w + g·w) / rowBits < T` as one bit, each `leW x` the test `x · w ≤ bits`
as `w = 0 ∨ ¬ bits / w < x`. Every kernel it calls is total (`div`, `add`, `mul`, `decLt`, `decEq`), so `ite1_builds`
applies at each `∧`, with both branches built. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- `bitsWinB`'s `leW x`: `x · w ≤ bits` as `w = 0 ∨ ¬ bits / w < x`, no product. -/
def leWB (bits w x : Nat) : Bld Nat := do
  ite1 (← call1 (kernel% USize.decEq) #[w, ← lit (.size 0)]) (lit (.bit true)) do
    let q ← call1 (kernel% USize.div) #[← lit (.size bits.toUSize), w]
    ite1 (← call1 (kernel% USize.decLt) #[q, x]) (lit (.bit false)) (lit (.bit true))

theorem bitsWinB_eq (bits T na g w : Nat) : bitsWinB bits T na g w = (do
    unless bits < 2 ^ 32 do throw s!"bitsWin: the bound {bits} is not below 2^32, which `kbitrows` reads"
    andB (← leWB bits w na) do andB (← leWB bits w g) do
      let s ← call1 (kernel% USize.add) #[← call1 (kernel% USize.mul) #[na, w], ← call1 (kernel% USize.mul) #[g, w]]
      call1 (kernel% USize.decLt) #[← call1 (kernel% USize.div) #[s, ← lit (.size Tab.rowBits.toUSize)], T]) := rfl

/-- `call1 USize.div` of two size registers holds their quotient. -/
theorem divB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {av bv : USize}
    (ha : rs[a]? = some (.size av)) (hb : rs[b]? = some (.size bv)) :
    Builds abiOf fg fg (do let r ← call1 (kernel% USize.div) #[a, b]; Pure.pure #[r]) rs #[.size (av / bv)] := by
  refine Builds.call1G (vs := #[.size av, .size bv]) (v := .size (av / bv)) (by abiK) (by rop) ?_ ?_ rfl
    fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl
  · rw [List.mapM_toArray]
    simp [reg, ha, hb]
    rfl
  · simp [arg]
    rfl

/-- `call1 USize.add` of two size registers holds their sum. -/
theorem addB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {av bv : USize}
    (ha : rs[a]? = some (.size av)) (hb : rs[b]? = some (.size bv)) :
    Builds abiOf fg fg (do let r ← call1 (kernel% USize.add) #[a, b]; Pure.pure #[r]) rs #[.size (av + bv)] := by
  refine Builds.call1G (vs := #[.size av, .size bv]) (v := .size (av + bv)) (by abiK) (by rop) ?_ ?_ rfl
    fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl
  · rw [List.mapM_toArray]
    simp [reg, ha, hb]
    rfl
  · simp [arg]
    rfl

/-- `call1 USize.decLt` of two size registers holds the bit `a < b`. -/
theorem ltB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {av bv : USize}
    (ha : rs[a]? = some (.size av)) (hb : rs[b]? = some (.size bv)) :
    Builds abiOf fg fg (do let r ← call1 (kernel% USize.decLt) #[a, b]; Pure.pure #[r]) rs #[.bit (decide (av < bv))] := by
  refine Builds.call1G (vs := #[.size av, .size bv]) (v := .bit (decide (av < bv))) (by abiK) (by rop) ?_ ?_ rfl
    fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl
  · rw [List.mapM_toArray]
    simp [reg, ha, hb]
    rfl
  · simp [arg]
    exact out_decLt' _ _

/-- **`leWB` holds the bit `x · w ≤ bits`** (`bits < 2^32`). -/
theorem leWB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {bits x w : Nat} {xv wv : USize}
    (hx : rs[x]? = some (.size xv)) (hw : rs[w]? = some (.size wv)) (hbits : bits < 2 ^ 32) :
    Builds abiOf fg fg (do let r ← leWB bits w x; Pure.pure #[r]) rs
      #[.bit (decide (xv.toNat * wv.toNat ≤ bits))] := by
  have hv : (if decide (wv = 0) then Val.bit true else
      (if decide (bits.toUSize / wv < xv) then Val.bit false else Val.bit true)) =
      .bit (decide (xv.toNat * wv.toNat ≤ bits)) := by
    have hb : bits.toUSize.toNat = bits := by
      rw [Nat.toUSize, USize.toNat_ofNat']
      refine Nat.mod_eq_of_lt ?_
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
    by_cases h0 : wv = 0
    · simp [h0]
    · have hw0 : 0 < wv.toNat := by
        rcases Nat.eq_zero_or_pos wv.toNat with h | h
        · exact absurd (USize.toNat_inj.mp (by simpa using h)) h0
        · exact h
      have hq : (bits.toUSize / wv).toNat = bits / wv.toNat := by rw [USize.toNat_div, hb]
      simp only [h0, decide_false, if_false, Bool.false_eq_true, USize.lt_iff_toNat_lt, hq]
      by_cases hle : xv.toNat * wv.toNat ≤ bits
      · have : ¬ bits / wv.toNat < xv.toNat := by rw [Nat.not_lt, Nat.le_div_iff_mul_le hw0]; exact hle
        simp [hle, this]
      · have : bits / wv.toNat < xv.toNat := by rw [Nat.div_lt_iff_lt_mul hw0]; omega
        simp [hle, this]
  rw [← hv]
  unfold leWB
  simp only [bind_assoc]
  refine Builds.litG fun z R1 hz m1 => ?_
  up m1 [hx hw]
  refine decEq_builds hw hz fun c R2 hc m2 => ?_
  up m2 [hx hw hz]
  refine ite1_builds hc (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl) ?_
  simp only [bind_assoc]
  refine Builds.litG fun l R3 hl m3 => ?_
  up m3 [hx hw hz]
  refine Builds.bind1G (divB_builds hl hw) fun q R4 hq m4 => ?_
  up m4 [hx hw]
  refine Builds.bind1G (ltB_builds hq hx) fun c2 R5 hc2 m5 => ?_
  refine ite1_builds hc2 (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)
    (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)

/-- **`bitsWinB` holds the bit `Tab.bitsWin`** of the five counts its registers hold: no product wraps where it is read
    (a product is read only below `bits < 2^32`, two of them below `2^33`, within the 64-bit `USize`). -/
theorem bitsWinB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {bits T na g w : Nat} {Tv nav gv wv : USize}
    (hT : rs[T]? = some (.size Tv)) (hna : rs[na]? = some (.size nav)) (hg : rs[g]? = some (.size gv))
    (hw : rs[w]? = some (.size wv)) (hbits : bits < 2 ^ 32) (h64 : System.Platform.numBits = 64) :
    Builds abiOf fg fg (do let r ← bitsWinB bits T na g w; Pure.pure #[r]) rs
      #[.bit (Tab.bitsWin bits Tv.toNat nav.toNat gv.toNat wv.toNat)] := by
  have hs2 : USize.size = 2 ^ 64 := by simp [USize.size, h64]
  have hrb : Tab.rowBits.toUSize.toNat = 64 := by
    rw [Nat.toUSize, USize.toNat_ofNat', h64]
    exact Nat.mod_eq_of_lt (by unfold Tab.rowBits; omega)
  have hmul : ∀ a b : USize, a.toNat * b.toNat < 2 ^ 32 → (a * b).toNat = a.toNat * b.toNat := fun a b h => by
    rw [USize.toNat_mul, Nat.mod_eq_of_lt]; rw [h64]; omega
  have hv : (if decide (nav.toNat * wv.toNat ≤ bits) then
      (if decide (gv.toNat * wv.toNat ≤ bits) then
        Val.bit (decide ((nav * wv + gv * wv) / Tab.rowBits.toUSize < Tv)) else Val.bit false)
      else Val.bit false) = .bit (Tab.bitsWin bits Tv.toNat nav.toNat gv.toNat wv.toNat) := by
    by_cases h1 : nav.toNat * wv.toNat ≤ bits
    · by_cases h2 : gv.toNat * wv.toNat ≤ bits
      · have e1 := hmul nav wv (by omega)
        have e2 := hmul gv wv (by omega)
        have e3 : (nav * wv + gv * wv).toNat = nav.toNat * wv.toNat + gv.toNat * wv.toNat := by
          rw [USize.toNat_add, e1, e2, Nat.mod_eq_of_lt]; rw [h64]; omega
        have e4 : ((nav * wv + gv * wv) / Tab.rowBits.toUSize).toNat =
            (nav.toNat * wv.toNat + gv.toNat * wv.toNat) / 64 := by rw [USize.toNat_div, e3, hrb]
        simp only [h1, h2, decide_true, if_true, USize.lt_iff_toNat_lt, e4]
        congr 1
        simp only [Tab.bitsWin, Tab.rowBits, h1, h2, decide_true, Bool.true_and]
        have : nav.toNat * wv.toNat < 2 ^ 32 := by omega
        have : gv.toNat * wv.toNat < 2 ^ 32 := by omega
        simp [*]
        omega
      · simp [h1, h2, Tab.bitsWin]
    · simp [h1, Tab.bitsWin]
  rw [← hv, bitsWinB_eq]
  simp only [hbits, if_true, bind_assoc, pure_bind]
  refine Builds.bind1G (leWB_builds hna hw hbits) fun c1 R1 hc1 m1 => ?_
  up m1 [hT hna hg hw]
  refine ite1_builds hc1 ?_ (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)
  simp only [bind_assoc]
  refine Builds.bind1G (leWB_builds hg hw hbits) fun c2 R2 hc2 m2 => ?_
  up m2 [hT hna hg hw]
  refine ite1_builds hc2 ?_ (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)
  simp only [bind_assoc]
  refine Builds.bind1G (mulB_builds hna hw) fun p1 R3 hp1 m3 => ?_
  up m3 [hT hg hw]
  refine Builds.bind1G (mulB_builds hg hw) fun p2 R4 hp2 m4 => ?_
  up m4 [hT hp1]
  refine Builds.bind1G (addB_builds hp1 hp2) fun s R5 hs m5 => ?_
  up m5 [hT]
  refine Builds.litG fun l R6 hl m6 => ?_
  up m6 [hT hs]
  refine Builds.bind1G (divB_builds hs hl) fun q R7 hq m7 => ?_
  up m7 [hT]
  exact ltB_builds hq hT

end Rel.Lang.Plan
