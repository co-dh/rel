module

public import Rel.Kernel.Db.ObjectFile
public import Rel.Kernel.Db.Own

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The own-format column file read back. `ownWrite` writes `ownImage`'s bytes and `ownMap` answers `ownParse` of the
file's bytes; both are `IO`, so the law is stated on those two pure bodies: every column the writer accepts is parsed
back as itself, header fields and each part byte for byte. -/

namespace Rel.Db

theorem leBytes_size (v w : Nat) : (leBytes v w).size = w := by
  rw [← ByteArray.size_data]; simp [leBytes]

/-- `leAt` reads back the number `leBytes` lays down, below `256 ^ w`. -/
theorem leAt_leBytes (P S : ByteArray) (v w : Nat) (hv : v < 256 ^ w) :
    leAt (P ++ leBytes v w ++ S) P.size w = v := by
  suffices h : ∀ k ≤ w, leAt (P ++ leBytes v w ++ S) P.size k = v % 256 ^ k by
    rw [h w (Nat.le_refl w), Nat.mod_eq_of_lt hv]
  intro k hk
  induction k with
  | zero => simp [leAt, Nat.mod_one]
  | succ k ih =>
    have hl := leBytes_size v w
    have hb : (P ++ leBytes v w ++ S).data[P.size + k]? = some (v / 256 ^ k).toUInt8 := by
      rw [← ByteArray.size_data] at hl
      simp only [ByteArray.data_append]
      rw [Array.getElem?_append_left (by simp only [Array.size_append, ByteArray.size_data] at hl ⊢; omega),
        Array.getElem?_append_right (by simp), ByteArray.size_data, Nat.add_sub_cancel_left]
      simp [leBytes, show k < w by omega]
    simp only [leAt]
    rw [ih (by omega), hb, Nat.mod_pow_succ]
    simp [Nat.mul_comm]

/-- The bound a file's offsets and lengths stay under: `own.rs` writes them as `u64`. -/
def u64Bound : Nat := 18446744073709551616

theorem u64Bound_eq : (256 : Nat) ^ 8 = u64Bound := by unfold u64Bound; rfl

/-- The bytes `M` between `P` and `S`, extracted. -/
theorem extract_mid (P M S : ByteArray) : (P ++ M ++ S).extract P.size (P.size + M.size) = M := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append, ← ByteArray.size_data]
  simp [-ByteArray.size_data]

theorem zeros_size (n : Nat) : (⟨Array.replicate n 0⟩ : ByteArray).size = n := Array.size_replicate

theorem ownLayout_fst_size (ps : Array ByteArray) (a i k : Nat) : (ownLayout ps a i k).1.size = 16 * k := by
  induction k generalizing a i with
  | zero => rfl
  | succ k ih => simp only [ownLayout, ByteArray.size_append, leBytes_size, ih]; omega

theorem ownOff_le (a : Nat) : a + 32 ≤ ownOff a ∧ ownOff a % 8 = 0 := by unfold ownOff; omega

/-- `ownSpans` reads back the `k` parts from part `i` that `ownLayout` lays out from byte `a`, its table at entry `i`
after `P` and the bytes `Q` up to `a` after the table. -/
theorem ownSpans_layout (ps : Array ByteArray) : ∀ (k i a : Nat) (P Q : ByteArray), i + k = ps.size →
    P.size = 24 + 16 * i → P.size + (ownLayout ps a i k).1.size + Q.size = a →
    (P ++ (ownLayout ps a i k).1 ++ Q ++ (ownLayout ps a i k).2).size < u64Bound →
    ownSpans (P ++ (ownLayout ps a i k).1 ++ Q ++ (ownLayout ps a i k).2) i a k = .ok (ps.toList.drop i) := by
  intro k
  induction k with
  | zero => intro i a P Q hk; simp only [Nat.add_zero] at hk; subst hk; intros; simp [ownSpans]
  | succ k ih =>
    intro i a P Q hk hP ha hb
    have hi : i < ps.size := by omega
    have ho := ownOff_le a
    have h4 := ih (i + 1) (ownOff a + ps[i].size) (P ++ leBytes (ownOff a) 8 ++ leBytes ps[i].size 8)
      (Q ++ ⟨Array.replicate (ownOff a - a) 0⟩ ++ ps[i]) (by omega)
    simp only [ownLayout, Array.getElem?_eq_getElem hi, Option.getD_some] at ha hb ⊢
    generalize (ownLayout ps (ownOff a + ps[i].size) (i + 1) k) = r at ha hb h4 ⊢
    simp only [ByteArray.size_append, leBytes_size, zeros_size, ByteArray.append_assoc] at ha hb h4 ⊢
    have h1 := leAt_leBytes P (leBytes ps[i].size 8 ++ r.1 ++ Q ++ ⟨Array.replicate (ownOff a - a) 0⟩ ++ ps[i] ++
      r.2) (ownOff a) 8 (by rw [u64Bound_eq]; omega)
    have h2 := leAt_leBytes (P ++ leBytes (ownOff a) 8) (r.1 ++ Q ++ ⟨Array.replicate (ownOff a - a) 0⟩ ++ ps[i] ++
      r.2) ps[i].size 8 (by rw [u64Bound_eq]; omega)
    have h3 := extract_mid (P ++ leBytes (ownOff a) 8 ++ leBytes ps[i].size 8 ++ r.1 ++ Q ++
      ⟨Array.replicate (ownOff a - a) 0⟩) ps[i] r.2
    simp only [ByteArray.append_assoc, ByteArray.size_append, leBytes_size, zeros_size] at h1 h2 h3
    rw [ownSpans, List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [← hP]
    simp only [h1, h2]
    simp only [ByteArray.size_append, leBytes_size, zeros_size]
    rw [if_neg (by simp [ho.2]), if_neg (by omega)]
    rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
    have e : P.size + (8 + (8 + (r.1.size + (Q.size + (ownOff a - a))))) = ownOff a := by omega
    rw [e] at h3
    rw [h3, h4 (by omega) (by omega) (by omega), Array.getElem_toList]
    rfl

theorem leBytes_one (x : UInt8) : leBytes x.toNat 1 = ⟨#[x]⟩ := by
  apply ByteArray.ext; simp [leBytes, Array.ofFn_succ, UInt8.ofNat_toNat]

theorem ownMagic_prefix (S : ByteArray) : (ownMagic ++ S).extract 0 8 = ownMagic := by
  simpa using extract_mid .empty ownMagic S

/-- **Map after write is the identity**, on the bodies of `ownMap` and `ownWrite`: every column `ownImage` accepts is
parsed back by `ownParse` as itself, field for field and each part byte for byte. The one hypothesis is the file's
`u64` offsets and lengths: a file under `2 ^ 64` bytes. -/
theorem ownParse_ownImage (f : OwnFile) (b : ByteArray) (h : ownImage f = .ok b) (hb : b.size < u64Bound) :
    ownParse b = .ok f := by
  obtain ⟨c, k, n, ps⟩ := f
  simp only [ownImage, ownVersion] at h
  split at h
  · cases h
  rename_i hk
  cases h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hk
  have hnp : ps.size ≤ 3 := by
    have h2 := hk
    generalize k.toNat = kk at h2
    rcases kk with _ | _ | _ | _ | _ | _ | kk <;> simp [ownNParts] at h2 <;> omega
  have hm : ownMagic.size = 8 := rfl
  have hh : (⟨#[7, c, k]⟩ : ByteArray) = leBytes (7 : UInt8).toNat 1 ++ leBytes c.toNat 1 ++ leBytes k.toNat 1 := by
    simp only [leBytes_one]; apply ByteArray.ext; simp [ByteArray.data_append]
  rw [hh] at hb ⊢
  have he : ∀ B : ByteArray, B ++ .empty = B := fun B => by apply ByteArray.ext; simp
  have hr1 := ownLayout_fst_size ps (24 + 16 * ps.size) 0 ps.size
  have hsp := ownSpans_layout ps ps.size 0 (24 + 16 * ps.size)
    (ownMagic ++ leBytes (7 : UInt8).toNat 1 ++ leBytes c.toNat 1 ++ leBytes k.toNat 1 ++ leBytes ps.size 1 ++
      leBytes 0 4 ++ leBytes n.toNat 8) .empty (by omega)
  rw [he] at hsp
  have hn : n.toNat < 256 ^ 8 := Nat.lt_of_lt_of_le n.toNat_lt_size (by simpa using USize.size_le)
  generalize ownLayout ps (24 + 16 * ps.size) 0 ps.size = r at hr1 hsp hb ⊢
  simp only [ByteArray.size_append, leBytes_size, hr1, hm, ByteArray.append_assoc, ByteArray.size_empty] at hb hsp ⊢
  have hsp := hsp trivial (by omega) hb
  have e8 := leAt_leBytes ownMagic (leBytes c.toNat 1 ++ leBytes k.toNat 1 ++ leBytes ps.size 1 ++ leBytes 0 4 ++
    leBytes n.toNat 8 ++ r.1 ++ r.2) (7 : UInt8).toNat 1 (by decide)
  have e9 := leAt_leBytes (ownMagic ++ leBytes (7 : UInt8).toNat 1) (leBytes k.toNat 1 ++ leBytes ps.size 1 ++
    leBytes 0 4 ++ leBytes n.toNat 8 ++ r.1 ++ r.2) c.toNat 1 (by have := c.toNat_lt; simpa using this)
  have e10 := leAt_leBytes (ownMagic ++ leBytes (7 : UInt8).toNat 1 ++ leBytes c.toNat 1) (leBytes ps.size 1 ++
    leBytes 0 4 ++ leBytes n.toNat 8 ++ r.1 ++ r.2) k.toNat 1 (by have := k.toNat_lt; simpa using this)
  have e11 := leAt_leBytes (ownMagic ++ leBytes (7 : UInt8).toNat 1 ++ leBytes c.toNat 1 ++ leBytes k.toNat 1)
    (leBytes 0 4 ++ leBytes n.toNat 8 ++ r.1 ++ r.2) ps.size 1 (by simp; omega)
  have e16 := leAt_leBytes (ownMagic ++ leBytes (7 : UInt8).toNat 1 ++ leBytes c.toNat 1 ++ leBytes k.toNat 1 ++
    leBytes ps.size 1 ++ leBytes 0 4) (r.1 ++ r.2) n.toNat 8 hn
  simp only [ByteArray.size_append, leBytes_size, hm, ByteArray.append_assoc] at e8 e9 e10 e11 e16
  have byte : ∀ (B : ByteArray) (o : Nat) (x : UInt8), leAt B o 1 = x.toNat → (B.data[o]?.getD 0) = x :=
    fun B o x e => UInt8.toNat_inj.mp (by simpa [leAt] using e)
  simp only [ownParse, ownMagic_prefix]
  rw [e8, e10, e11, e16, byte _ _ _ e9]
  simp only [ByteArray.size_append, leBytes_size, hr1, hm]
  rw [if_neg (by omega), if_neg (by simp), if_neg (by decide), if_neg (by simp [hk]), if_neg (by omega)]
  rw [hsp]
  simp [UInt8.ofNat_toNat, USize.ofNat_toNat]
  rfl

end Rel.Db
