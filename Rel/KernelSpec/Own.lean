import Rel.Kernel.Db.ObjectFile
import Rel.Kernel.Db.Own

/-! The own-format column file read back. `ownWrite` writes `ownImage`'s bytes and `ownMap` answers `ownParse` of the
file's bytes; both are `IO`, so the law is stated on those two pure bodies: every column the writer accepts is parsed
back as itself, header fields, domain name and each part byte for byte. -/

namespace Rel.Db

theorem leBytes_length (v w : Nat) : (leBytes v w).length = w := by simp [leBytes]

/-- `leAt` reads back the number `leBytes` lays down, below `256 ^ w`. -/
theorem leAt_leBytes (P S : List UInt8) (v w : Nat) (hv : v < 256 ^ w) :
    leAt ⟨(P ++ leBytes v w ++ S).toArray⟩ P.length w = v := by
  suffices h : ∀ k ≤ w, leAt ⟨(P ++ leBytes v w ++ S).toArray⟩ P.length k = v % 256 ^ k by
    rw [h w (Nat.le_refl w), Nat.mod_eq_of_lt hv]
  intro k hk
  induction k with
  | zero => simp [leAt, Nat.mod_one]
  | succ k ih =>
    have hb : (P ++ (leBytes v w ++ S))[P.length + k]? = some (v / 256 ^ k).toUInt8 := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (by rw [leBytes_length]; omega)]
      simp [leBytes, List.getElem?_range (by omega : k < w)]
    simp only [leAt]
    rw [ih (by omega), Nat.mod_pow_succ]
    simp [hb, Nat.mul_comm]

/-- The bound a file's offsets and lengths stay under: `own.rs` writes them as `u64`. -/
def u64Bound : Nat := 18446744073709551616

theorem u64Bound_eq : (256 : Nat) ^ 8 = u64Bound := by unfold u64Bound; rfl

/-- The bytes `M` between `P` and `S`, extracted. -/
theorem extract_mid (P M S : List UInt8) :
    (ByteArray.mk (P ++ M ++ S).toArray).extract P.length (P.length + M.length) = ⟨M.toArray⟩ := by
  apply ByteArray.ext
  simp

theorem ownLayout_fst_length (a : Nat) (ps : List ByteArray) : (ownLayout a ps).1.length = 16 * ps.length := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih => simp only [ownLayout, List.length_append, leBytes_length, ih, List.length_cons]; omega

theorem ownOff_le (a : Nat) : a + 32 ≤ ownOff a ∧ ownOff a % 8 = 0 := by unfold ownOff; omega

/-- `ownSpans` reads back the parts `ownLayout` lays out from byte `a`, its table at entry `i` after `P` and the bytes
`Q` up to `a` after the table. -/
theorem ownSpans_layout (ps : List ByteArray) : ∀ (i a : Nat) (P Q : List UInt8),
    P.length = 24 + 16 * i → P.length + (ownLayout a ps).1.length + Q.length = a →
    (P ++ ((ownLayout a ps).1 ++ (Q ++ (ownLayout a ps).2))).length < u64Bound →
    ownSpans ⟨(P ++ ((ownLayout a ps).1 ++ (Q ++ (ownLayout a ps).2))).toArray⟩ i a ps.length = .ok ps := by
  induction ps with
  | nil => intros; rfl
  | cons p ps ih =>
    intro i a P Q hP ha hb
    have ho := ownOff_le a
    have h4 := ih (i + 1) (ownOff a + p.size) (P ++ (leBytes (ownOff a) 8 ++ leBytes p.size 8))
      (Q ++ (List.replicate (ownOff a - a) 0 ++ p.data.toList))
    simp only [ownLayout] at ha hb ⊢
    generalize (ownLayout (ownOff a + p.size) ps) = r at ha hb h4 ⊢
    have hs : p.data.toList.length = p.size := Array.length_toList
    have hz : ∀ L : List UInt8, (ByteArray.mk L.toArray).size = L.length := fun _ => List.size_toArray
    simp only [List.length_cons, List.length_append, leBytes_length, List.length_replicate,
      List.append_assoc] at ha hb h4 ⊢
    have h1 := leAt_leBytes P (leBytes p.size 8 ++ (r.1 ++ (Q ++ (List.replicate (ownOff a - a) 0 ++
      (p.data.toList ++ r.2))))) (ownOff a) 8 (by rw [u64Bound_eq]; omega)
    have h2 := leAt_leBytes (P ++ leBytes (ownOff a) 8) (r.1 ++ (Q ++ (List.replicate (ownOff a - a) 0 ++
      (p.data.toList ++ r.2)))) p.size 8 (by rw [u64Bound_eq]; omega)
    have h3 := extract_mid (P ++ (leBytes (ownOff a) 8 ++ (leBytes p.size 8 ++ (r.1 ++ (Q ++
      List.replicate (ownOff a - a) 0))))) p.data.toList r.2
    simp only [List.append_assoc, List.length_append, leBytes_length, List.length_replicate] at h1 h2 h3
    rw [ownSpans]
    simp only [← hP]
    rw [if_neg (by rw [h1]; simp [ho.2]), if_neg (by rw [h1]; omega), if_neg (by rw [h1, h2, hz]; simp only [List.length_append, leBytes_length, List.length_replicate, hs]; simp; omega), h1, h2]
    have e : P.length + (8 + (8 + (r.1.length + (Q.length + (ownOff a - a))))) = ownOff a := by omega
    rw [e, hs] at h3
    rw [h3, h4 (by simp; omega) (by omega) (by simpa using hb)]
    rfl

theorem leBytes_one (x : UInt8) : leBytes x.toNat 1 = [x] := by simp [leBytes, UInt8.ofNat_toNat]

theorem ownMagic_prefix (S : List UInt8) :
    (List.range 8).map (fun o => ((ownMagic ++ S).toArray[o]?).getD 0) = ownMagic := by
  simp [ownMagic, List.range_succ]

/-- **Map after write is the identity**, on the bodies of `ownMap` and `ownWrite`: every column `ownImage` accepts is
parsed back by `ownParse` as itself, field for field and each part byte for byte. The one hypothesis is the file's
`u64` offsets and lengths: a file under `2 ^ 64` bytes. -/
theorem ownParse_ownImage (f : OwnFile) (b : ByteArray) (h : ownImage f = .ok b) (hb : b.size < u64Bound) :
    ownParse b = .ok f := by
  obtain ⟨c, t, k, n, s, ps⟩ := f
  simp only [ownImage] at h
  split at h
  · cases h
  rename_i hk
  split at h
  · cases h
  rename_i hz
  cases h
  generalize hD : s.toUTF8.data.toList = D at hk hz hb ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not, gt_iff_lt,
    Nat.not_lt] at hk
  have hnp : ps.size ≤ 3 := by
    have h2 := hk.1
    generalize k.toNat = kk at h2
    rcases kk with _ | _ | _ | _ | _ | _ | kk <;> simp [ownNParts] at h2 <;> omega
  have hL : ps.toList.length = ps.size := Array.length_toList
  have hr1 := ownLayout_fst_length (24 + 16 * ps.size + D.length) ps.toList
  have hsp := ownSpans_layout ps.toList 0 (24 + 16 * ps.size + D.length)
    (ownMagic ++ [4, c, t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++ leBytes n.toNat 8) D rfl
  have hn : n.toNat < 256 ^ 8 := Nat.lt_of_lt_of_le n.toNat_lt_size (by simpa using USize.size_le)
  generalize ownLayout (24 + 16 * ps.size + D.length) ps.toList = r at hr1 hsp hb ⊢
  have sz : ∀ L : List UInt8, (ByteArray.mk L.toArray).size = L.length := fun _ => List.size_toArray
  simp only [sz, List.length_append, List.length_cons, List.length_nil, leBytes_length, hL, hr1] at hb hsp
  have hsp := hsp (by simp [ownMagic]) (by omega)
  have e8 := leAt_leBytes ownMagic ([c, t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++ leBytes n.toNat 8 ++
    r.1 ++ D ++ r.2) (4 : UInt8).toNat 1 (by decide)
  have e9 := leAt_leBytes (ownMagic ++ [4]) ([t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++
    leBytes n.toNat 8 ++ r.1 ++ D ++ r.2) c.toNat 1 (by have := c.toNat_lt; simpa using this)
  have e10 := leAt_leBytes (ownMagic ++ [4, c]) ([k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++
    leBytes n.toNat 8 ++ r.1 ++ D ++ r.2) t.toNat 1 (by have := t.toNat_lt; simpa using this)
  have e11 := leAt_leBytes (ownMagic ++ [4, c, t]) (leBytes ps.size 2 ++ leBytes D.length 2 ++
    leBytes n.toNat 8 ++ r.1 ++ D ++ r.2) k.toNat 1 (by have := k.toNat_lt; simpa using this)
  have e12 := leAt_leBytes (ownMagic ++ [4, c, t, k]) (leBytes D.length 2 ++ leBytes n.toNat 8 ++ r.1 ++ D ++ r.2)
    ps.size 2 (by simp; omega)
  have e14 := leAt_leBytes (ownMagic ++ [4, c, t, k] ++ leBytes ps.size 2) (leBytes n.toNat 8 ++ r.1 ++ D ++ r.2)
    D.length 2 (by simp; omega)
  have e16 := leAt_leBytes (ownMagic ++ [4, c, t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2) (r.1 ++ D ++ r.2)
    n.toNat 8 hn
  have ed := extract_mid (ownMagic ++ [4, c, t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++ leBytes n.toNat 8 ++
    r.1) D r.2
  simp only [leBytes_one, List.length_append, List.length_cons, List.length_nil, leBytes_length,
    List.append_assoc, List.cons_append, List.nil_append] at e8 e9 e10 e11 e12 e14 e16 hsp
  have ownMagic_len : ownMagic.length = 8 := rfl
  simp only [ownMagic_len] at e8 e9 e10 e11 e12 e14 e16 hsp
  have byte : ∀ (B : ByteArray) (o : Nat) (x : UInt8), leAt B o 1 = x.toNat → (B.data[o]?.getD 0) = x :=
    fun B o x e => UInt8.toNat_inj.mp (by simpa [leAt] using e)
  simp only [ownParse, List.append_assoc, List.cons_append, List.nil_append, ownMagic_prefix]
  rw [e8, e11, e12, e14, e16, byte _ _ _ e9, byte _ _ _ e10]
  simp only [sz, List.length_append, List.length_cons, leBytes_length, hr1, hL, ownMagic_len]
  rw [if_neg (by omega), if_neg (by simp), if_neg (by decide), if_neg (by simp [hk.1]), if_neg (by omega)]
  rw [show (ownMagic ++ [4, c, t, k] ++ leBytes ps.size 2 ++ leBytes D.length 2 ++ leBytes n.toNat 8 ++ r.1).length =
    24 + 16 * ps.size by simp only [List.length_append, leBytes_length, hr1, hL, ownMagic_len]; simp] at ed
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ed
  rw [hsp, ed]
  subst hD
  have hu : String.fromUTF8? ⟨s.toUTF8.data.toList.toArray⟩ = some s := by
    simp only [Array.toArray_toList]
    simp [String.fromUTF8?, s.isValidUTF8]
    rfl
  simp only [bind, Except.bind, hu]
  rw [if_neg (by simpa using hz)]
  simp [UInt8.ofNat_toNat, USize.ofNat_toNat]

/-- **`ownEnc` puts back what `ownParts` took apart**, each part as it was. With `ownParse_ownImage`, a column
`Table.writeVals` writes is mapped back by `Table.readVals` as the `Enc` written; the `IO` around both is not stated. -/
theorem ownEnc_ownParts {X : Type} {e : Ext.Enc X} {k : UInt8} {ps : Array ByteArray}
    (h : ownParts e = .ok (some (k, ps))) : ownEnc k ps = some e := by
  cases e <;> simp only [ownParts] at h <;> cases h <;> rfl

end Rel.Db
