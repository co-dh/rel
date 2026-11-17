/-! The part of `QLean.Verify.Raw` the Rel kernels reach; `QLean.Verify.Raw` imports it. -/


namespace QLean.Verify

open QLean

theorem toInt_toInt64 (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else x.toNat - 2 ^ 64 := by
  rw [Int64.toInt, show x.toInt64.toBitVec = x.toBitVec from rfl, BitVec.toInt_eq_toNat_cond]
  simp only [UInt64.toNat_toBitVec]
  split <;> split <;> omega

/-- The low `w` bytes of `v` as a two's-complement number: what a signed `w`-byte element denotes. -/
def sx (w : Nat) (v : UInt64) : Int :=
  if v.toNat % 2 ^ (8 * w) < 2 ^ (8 * w - 1) then ((v.toNat % 2 ^ (8 * w) : Nat) : Int)
  else ((v.toNat % 2 ^ (8 * w) : Nat) : Int) - ((2 ^ (8 * w) : Nat) : Int)

/-- `sx` reads only the low `8 * w` bits, which are what a `w`-byte write keeps. -/
theorem sx_mod {w : Nat} (h8 : w ≤ 8) (v : UInt64) : sx w (UInt64.ofNat (v.toNat % 2 ^ (8 * w))) = sx w v := by
  have : v.toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
  simp only [sx, UInt64.toNat_ofNat', Nat.mod_eq_of_lt this, Nat.mod_mod]

theorem pairwise_map_range_iff {α : Type} (R : α → α → Prop) (f : Nat → α) (m : Nat) :
    ((List.range m).map f).Pairwise R ↔ ∀ i j, i < j → j < m → R (f i) (f j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.pairwise_append, ih]
    simp only [List.map_cons, List.map_nil, List.pairwise_singleton, List.mem_map, List.mem_range,
      List.mem_singleton, true_and]
    constructor
    · rintro ⟨h, hm⟩ i j hij hj
      by_cases hjm : j = m
      · subst hjm; exact hm _ ⟨i, hij, rfl⟩ _ rfl
      · exact h i j hij (by omega)
    · intro h
      exact ⟨fun i j hij hj => h i j hij (by omega), by
        rintro _ ⟨i, hi, rfl⟩ _ rfl; exact h i m hi (by omega)⟩

end QLean.Verify
