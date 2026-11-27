module

public import Rel.Lang.Laws.Eunion

@[expose] public section

/-! `Λ(S)` has an array at every point where `S`'s target is `flat` (no array, no `general` atom): the target is finite and
    `Obj.key` tells its elements apart, so `lamDen_total` applies. This is what lets the elaborator fuse `Λ(S) E(∋ X)`
    to `Λ(S X)` (`Tm.fuseLam`, architecture §476). -/

namespace Rel.Lang

open Rel Rel.Dep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- An atom is read back from the bits `bitsOf` gives. -/
theorem atomOfBits_bitsOf (a : QAtom) {t : QAtomicType} (h : a.type = t) (hg : t ≠ .general) :
    Column.atomOfBits t (Column.bitsOf a) hg = a := by
  subst h
  cases a <;> simp [Column.atomOfBits, Column.bitsOf, QAtom.type]
  rename_i x; cases x <;> rfl

theorem ascOrd_some (t : QAtomicType) (hg : t ≠ .general) : ∃ f, Kernel.ascOrd t = some f := by
  cases t <;> first | exact absurd rfl hg | exact ⟨_, rfl⟩

theorem bitsOf_u1 (a : QAtom) (h : a.type = .u1) : Column.bitsOf a < 2 := by
  cases a <;> simp [QAtom.type] at h <;> simp [Column.bitsOf] <;> split <;> decide

/-- `atomKey` is one to one on the atoms of a type that has an order code. -/
theorem atomKey_inj {a b : QAtom} {t : QAtomicType} (ha : a.type = t) (hb : b.type = t) (hg : t ≠ .general)
    (h : atomKey a = atomKey b) : a = b := by
  obtain ⟨f, hf⟩ := ascOrd_some t hg
  have key : ∀ x : QAtom, x.type = t → atomKey x = [(f (Column.bitsOf x)).toNat] := fun x hx => by
    unfold atomKey; rw [hx, hf]
  rw [key a ha, key b hb] at h
  have e := UInt64.toNat_inj.1 (List.singleton_inj.1 h)
  have := (Verify.ascOrd_atom hf hg (a := Column.bitsOf a) (b := Column.bitsOf b) fun ht => by
    subst ht; exact ⟨bitsOf_u1 a ha, bitsOf_u1 b hb⟩).1 e
  rwa [atomOfBits_bitsOf a ha hg, atomOfBits_bitsOf b hb hg] at this

/-- **Keys tell the elements of a flat object apart.** -/
theorem Obj.key_inj_of_flat : ∀ (B : Obj), B.flat = true → ∀ b c : B.El, B.key b = B.key c → b = c
  | .atom t, hf, b, c, h => by
    have hg : t ≠ .general := by simpa [Obj.flat] using hf
    cases t <;> first | exact absurd rfl hg | skip
    all_goals simp only [Obj.key] at h
    case u1 => simpa using atomKey_inj (a := .u1 b) (b := .u1 c) rfl rfl hg h
    case u8 => simpa using atomKey_inj (a := .u8 b) (b := .u8 c) rfl rfl hg h
    case char => simpa using atomKey_inj (a := .char b) (b := .char c) rfl rfl hg h
    case i8 => simpa using atomKey_inj (a := .i8 b) (b := .i8 c) rfl rfl hg h
    case i16 => simpa using atomKey_inj (a := .i16 b) (b := .i16 c) rfl rfl hg h
    case i32 => simpa using atomKey_inj (a := .i32 b) (b := .i32 c) rfl rfl hg h
    case date => simpa using atomKey_inj (a := .date b) (b := .date c) rfl rfl hg h
    case i64 => simpa using atomKey_inj (a := .i64 b) (b := .i64 c) rfl rfl hg h
    case datetime => simpa using atomKey_inj (a := .datetime b) (b := .datetime c) rfl rfl hg h
    case f32 => simpa using atomKey_inj (a := .f32 b) (b := .f32 c) rfl rfl hg h
    case f64 => simpa using atomKey_inj (a := .f64 b) (b := .f64 c) rfl rfl hg h
    case sym => simpa using atomKey_inj (a := .sym b) (b := .sym c) rfl rfl hg h
  | .prod a b, hf, (x, y), (x', y'), h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 hf
    simp only [Obj.key] at h
    have e := Obj.key_prefix a x x' _ _ h
    rw [e] at h
    rw [Obj.key_inj_of_flat a ha x x' e, Obj.key_inj_of_flat b hb y y' (List.append_cancel_left h)]
  | .sum a b, hf, .inl x, .inl x', h => by
    simp only [Obj.key, List.cons.injEq, true_and] at h
    rw [Obj.key_inj_of_flat a (Bool.and_eq_true_iff.1 hf).1 x x' h]
  | .sum a b, hf, .inr y, .inr y', h => by
    simp only [Obj.key, List.cons.injEq, true_and] at h
    rw [Obj.key_inj_of_flat b (Bool.and_eq_true_iff.1 hf).2 y y' h]
  | .sum _ _, _, .inl _, .inr _, h => by simp [Obj.key] at h
  | .sum _ _, _, .inr _, .inl _, h => by simp [Obj.key] at h
  | .one, _, (), (), _ => rfl
  | .arr _, hf, _, _, _ => by simp [Obj.flat] at hf

theorem fin_bv (n : Nat) : ∃ l : List (BitVec n), ∀ b, b ∈ l :=
  ⟨(List.finRange (2 ^ n)).map BitVec.ofFin, fun b => List.mem_map.2 ⟨b.toFin, List.mem_finRange _, by simp⟩⟩

theorem fin_of_surj {α β : Type} (f : α → β) (hf : ∀ y, ∃ x, f x = y) :
    (∃ l : List α, ∀ x, x ∈ l) → ∃ l : List β, ∀ y, y ∈ l
  | ⟨l, h⟩ => ⟨l.map f, fun y => by obtain ⟨x, rfl⟩ := hf y; exact List.mem_map_of_mem (h x)⟩

/-- Every carrier is finite: a list holds all its elements. -/
theorem fin_carrier : ∀ t : QAtomicType, ∃ l : List (Carrier t), ∀ x, x ∈ l := by
  have u8 := fin_of_surj UInt8.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 8)
  have u32 := fin_of_surj UInt32.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 32)
  have u64 := fin_of_surj UInt64.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 64)
  have i8 := fin_of_surj Int8.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 8)
  have i16 := fin_of_surj Int16.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 16)
  have i32 := fin_of_surj Int32.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 32)
  have i64 := fin_of_surj Int64.ofBitVec (fun y => ⟨y.toBitVec, rfl⟩) (fin_bv 64)
  intro t
  cases t
  case general => exact ⟨[()], fun _ => by simp⟩
  case u1 => exact ⟨[false, true], fun x => by cases x <;> simp⟩
  all_goals first | exact u8 | exact u32 | exact u64 | exact i8 | exact i16 | exact i32 | exact i64

/-- **A flat object is finite**: a list holds all its elements. -/
theorem Obj.fin_of_flat : ∀ (B : Obj), B.flat = true → ∃ l : List B.El, ∀ b, b ∈ l
  | .atom t, _ => fin_carrier t
  | .prod a b, hf => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 hf
    obtain ⟨l, hl⟩ := Obj.fin_of_flat a ha
    obtain ⟨m, hm⟩ := Obj.fin_of_flat b hb
    exact ⟨l.flatMap fun x => m.map (x, ·), fun (x, y) => List.mem_flatMap.2 ⟨x, hl x, List.mem_map_of_mem (hm y)⟩⟩
  | .sum a b, hf => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 hf
    obtain ⟨l, hl⟩ := Obj.fin_of_flat a ha
    obtain ⟨m, hm⟩ := Obj.fin_of_flat b hb
    refine ⟨l.map Sum.inl ++ m.map Sum.inr, fun | .inl x => ?_ | .inr y => ?_⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem (hl x))
    · exact List.mem_append_right _ (List.mem_map_of_mem (hm y))
  | .one, _ => ⟨[()], fun _ => by simp⟩
  | .arr _, hf => by simp [Obj.flat] at hf

variable {A B C : Obj}

/-- **`Λ(S)` has an array at every point** where `S`'s target is flat. -/
theorem lamDen_of_flat (hB : B.flat = true) (S : Core.Rel (Obj.El A) (Obj.El B)) (a : A.El) : ∃ ys, lamDen S a ys := by
  obtain ⟨l, hl⟩ := Obj.fin_of_flat B hB
  exact lamDen_total S a l (fun b _ => hl b) fun b c _ _ e => Obj.key_inj_of_flat B hB b c e

/-- `Tm.fuseLam` keeps the meaning of the composition it replaces. -/
theorem Tm.fuseLam_den (t : Tm A B) (u : Tm B C) (ρ : Val) : (Tm.fuseLam t u).den ρ = (Tm.comp t u).den ρ := by
  cases B <;> try rfl
  rename_i B
  cases t <;> cases u <;> try rfl
  rename_i S R
  cases R <;> try rfl
  rename_i M X
  cases M <;> try rfl
  by_cases hf : B.flat = true
  · change den ρ (if B.flat = true then _ else _) = _
    rw [if_pos hf]; exact (lamDen_absorb _ _ (lamDen_of_flat hf _)).symm
  · change den ρ (if B.flat = true then _ else _) = _
    rw [if_neg hf]

end Rel.Lang
