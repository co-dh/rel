import Rel.Kernel.Coc
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Encoding` the Rel kernels reach; `Rel.Verify.Encoding` imports it. -/


open Rel.Ext

namespace Rel.Verify

open Rel

/-- What an eight-byte read keeps of a value is all of it. -/
theorem ofNat_toNat_mod64 (v : UInt64) : UInt64.ofNat (v.toNat % 2 ^ 64) = v := by
  rw [Nat.mod_eq_of_lt v.toNat_lt, UInt64.ofNat_toNat]

/-- A run of `w` bytes written and read back is the low `w` bytes of what was written
(`Column.bitsAt_pushBits`), which at `w = 8` is the whole of it. -/
theorem bitsAt_pushBits8 (out : ByteArray) (v : UInt64) :
    Column.bitsAt (Column.pushBits out v 8) out.size 8 = v := by
  -- `Column.bitsAt_pushBits` at full width rather than `bv_decide`, which brings `Lean.ofReduceBool`
  rw [Column.bitsAt_pushBits out v 8 (Nat.le_refl 8), show 8 * 8 = 64 from rfl, ofNat_toNat_mod64]

theorem getElem?_push {α : Type} (a : Array α) (v : α) (i : Nat) :
    (a.push v)[i]? = if i = a.size then some v else a[i]? := by
  split
  · next h => subst h; exact Array.getElem?_push_size
  · next h =>
    rcases Nat.lt_or_gt_of_ne h with h | h
    · rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]
    · rw [Array.getElem?_eq_none (by rw [Array.size_push]; omega), Array.getElem?_eq_none (by omega)]

/-- `Array.range` is `Array.ofFn`, whose loop is private; it is reached here as any `g` with the
loop's two equations, which hold by `rfl` since the loop is structural. -/
theorem toList_range (n : Nat) : (Array.range n).toList = List.range n := by
  have key : ∀ (g : Array Nat → (i : Nat) → i ≤ n → Array Nat), (∀ acc h, g acc 0 h = acc) →
      (∀ acc i (h : i + 1 ≤ n), g acc (i + 1) h = g (acc.push (n - i - 1)) i (Nat.le_of_succ_le h)) →
      ∀ i (h : i ≤ n) acc, acc.toList = List.range acc.size → acc.size + i = n →
        (g acc i h).toList = List.range n := by
    intro g h0 hs i
    induction i with
    | zero => intro h acc ha hn; rw [h0, ha, ← hn]; rfl
    | succ i ih =>
      intro h acc ha hn
      rw [hs, ih _ _ (by rw [Array.toList_push, ha, Array.size_push, List.range_succ, show n - i - 1 = acc.size by omega])
        (by rw [Array.size_push]; omega)]
  unfold Array.range Array.ofFn
  exact key _ (fun _ _ => rfl) (fun _ _ _ => rfl) n (Nat.le_refl n) _ rfl (Nat.zero_add n)

theorem getElem_range (n i : Nat) (h : i < (Array.range n).size) : (Array.range n)[i] = i := by
  rw [← Array.getElem_toList]; simp only [toList_range, List.getElem_range]

/-- The fold behind `blockStarts` carries `blockStart` at the block it has reached, one entry per
block reached and `0` before any, which is the invariant all three parts of the statement are. -/
theorem blockStarts_fold (metadata : ByteArray) (n : Nat) :
    letI s := Nat.fold n (init := ((#[0] : Array Nat), 0)) fun b _ s =>
      let pos := s.2 + Column.blk metadata * Column.widthAt metadata b / 8
      (s.1.push pos, pos)
    s.2 = Column.blockStart metadata n ∧ s.1.size = n + 1 ∧
      ∀ b ≤ n, s.1[b]? = some (Column.blockStart metadata b) := by
  induction n with
  | zero => simp [Column.blockStart]
  | succ n ih =>
    obtain ⟨h2, hsz, hget⟩ := ih
    refine ⟨by simp [Column.blockStart, h2], by simp [hsz], ?_⟩
    intro b hb
    simp only [Nat.fold_succ, getElem?_push, hsz, h2]
    by_cases hbn : b = n + 1
    · subst hbn; simp [Column.blockStart]
    · simp [hbn, hget b (by omega)]

/-- Entry `b` of the table is the sum over the blocks before `b`. Stated at `b ≤ nblk` because the
table has one more entry than there are blocks: the last is where the pack ends. -/
theorem blockStarts_get (metadata : ByteArray) {b : Nat} (h : b ≤ Column.nblk metadata) :
    (Column.blockStarts metadata)[b]? = some (Column.blockStart metadata b) :=
  (blockStarts_fold metadata (Column.nblk metadata)).2.2 b h

/-- One step of `blockStart`: block `c + 1` starts where block `c`'s `blk * width / 8` bytes end. -/
theorem blockStart_succ (M : ByteArray) (c : Nat) :
    Column.blockStart M (c + 1) = Column.blockStart M c + Column.blk M * Column.widthAt M c / 8 := by
  unfold Column.blockStart; rw [Nat.fold_succ]

/-- A block holds at least one element, at any stored `lg`. -/
theorem blk_pos (M : ByteArray) : 0 < Column.blk M := by unfold Column.blk; exact Nat.two_pow_pos _

/-- A block of any width is whole bytes and starts 8-aligned: `blk` is a multiple of 8 at any stored `lg`. -/
theorem blk_dvd8 (M : ByteArray) : 8 ∣ Column.blk M := by
  unfold Column.blk; exact Nat.pow_dvd_pow 2 (show 3 ≤ Column.lgOf M by unfold Column.lgOf; omega)

/-- Where the stored `lg` is one the layout admits, the block size is `2 ^ lg` with no clamping. -/
theorem blk_of_lgAt (M : ByteArray) (h : 6 ≤ Column.lgAt M ∧ Column.lgAt M ≤ 16) :
    Column.blk M = 2 ^ Column.lgAt M := by
  unfold Column.blk Column.lgOf; congr 1; omega

/-- An element below the count lies in a block below the block count `(n + B - 1) / B`. -/
theorem lt_cdiv {B i n : Nat} (hB : 0 < B) (hi : i < n) : i / B < (n + B - 1) / B :=
  Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hB).2 (by have := Nat.div_mul_le_self i B; rw [Nat.succ_mul]; omega))

/-- A block below the block count starts below the count. -/
theorem mul_lt_of_lt_cdiv {B b n : Nat} (hB : 0 < B) (h : b < (n + B - 1) / B) : b * B < n := by
  have := (Nat.le_div_iff_mul_le hB).1 h; rw [Nat.succ_mul] at this; omega

theorem foldl_or_testBit (l : List Nat) (g : Nat → Nat) (a t : Nat) :
    (l.foldl (fun a j => a ||| g j) a).testBit t = (a.testBit t || l.any fun j => (g j).testBit t) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [List.foldl, ih, Nat.testBit_or, Bool.or_assoc]

theorem foldl_or_u8 (l : List Nat) (g : Nat → Nat) (a : UInt8) :
    (l.foldl (fun b j => b ||| (g j).toUInt8) a).toNat = l.foldl (fun a j => a ||| g j % 2 ^ 8) a.toNat := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp [List.foldl, ih, UInt8.toNat_or]

theorem foldl_or_u64 (l : List Nat) (g : Nat → Nat) (a : UInt64) :
    (l.foldl (fun b j => b ||| (g j).toUInt64) a).toNat = l.foldl (fun a j => a ||| g j % 2 ^ 64) a.toNat := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp [List.foldl, ih, UInt64.toNat_or]

theorem ba_push_getElem? (b : ByteArray) (v : UInt8) (i : Nat) :
    (b.push v)[i]? = if i = b.size then some v else b[i]? := by
  show (b.data.push v)[i]? = _
  rw [getElem?_push]; rfl

theorem ba_size_push (b : ByteArray) (v : UInt8) : (b.push v).size = b.size + 1 := by
  show (b.data.push v).size = b.data.size + 1; simp

theorem fold_push_getElem? (L : Nat) (f : Nat → UInt8) (init : ByteArray) :
    (Nat.fold L (init := init) fun k _ acc => acc.push (f k)).size = init.size + L ∧
    ∀ k < L, (Nat.fold L (init := init) fun k _ acc => acc.push (f k))[init.size + k]? = some (f k) := by
  induction L with
  | zero => simp
  | succ L ih =>
    obtain ⟨hs, hg⟩ := ih
    refine ⟨by rw [Nat.fold_succ, ba_size_push]; exact (congrArg (· + 1) hs).trans (by omega), fun k hk => ?_⟩
    simp only [Nat.fold_succ, ba_push_getElem?, hs]
    by_cases hkL : k = L
    · subst hkL; simp
    · simp [hkL, hg k (by omega)]

theorem fold_push0 (L : Nat) (f : Nat → UInt8) (init : ByteArray) (h : init.size = 0) (k : Nat) (hk : k < L) :
    (Nat.fold L (init := init) fun k _ acc => acc.push (f k))[k]? = some (f k) := by
  have := (fold_push_getElem? L f init).2 k hk
  rwa [h, Nat.zero_add] at this

theorem field_of (w p j : Nat) (h1 : j * w ≤ p) (h2 : p < j * w + w) :
    p / w = j ∧ p % w = p - j * w := by
  have hq : p / w = j := Nat.div_eq_of_lt_le h1
    (by rw [Nat.succ_mul]; omega)
  refine ⟨hq, ?_⟩
  have := Nat.mod_add_div p w
  rw [hq, Nat.mul_comm] at this; omega

theorem packRes_byte (B w : Nat) (res : Nat → UInt64) (hw : 0 < w) (k : Nat)
    (hk : k < B * w / 8) :
    ∃ V : UInt8, (Kernel.Coc.packRes B w res)[k]? = some V ∧ ∀ s, V.toNat.testBit s = true ↔
      s < 8 ∧ ((res ((8 * k + s) / w)).toNat % 2 ^ w).testBit ((8 * k + s) % w) = true := by
  unfold Kernel.Coc.packRes
  rw [if_neg (by omega)]
  have h0 : (ByteArray.emptyWithCapacity (B * w / 8)).size = 0 := rfl
  refine ⟨_, fold_push0 _ _ _ h0 k hk, fun s => ?_⟩
  rw [foldl_or_u8, foldl_or_testBit]
  simp only [UInt8.toNat_zero, Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range'_1,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j, -, hs, hle, hlt, hb⟩
    obtain ⟨hq, hr⟩ := field_of w (8 * k + s) j (by omega) (by omega)
    refine ⟨hs, Nat.mod_lt _ hw, ?_⟩
    rw [hq, hr, show 8 * k + s - j * w = s + 8 * k - j * w by omega]; exact hb
  · rintro ⟨hs, hlt, hb⟩
    refine ⟨(8 * k + s) / w, ⟨Nat.div_le_div_right (by omega), ?_⟩, hs, ?_⟩
    · have := Nat.div_le_div_right (c := w) (show 8 * k + s ≤ 8 * k + 7 by omega)
      have := Nat.div_le_div_right (c := w) (show 8 * k ≤ 8 * k + 7 by omega)
      omega
    · have hm := Nat.mod_add_div' (8 * k + s) w
      have hl := Nat.mod_lt (8 * k + s) hw
      refine ⟨by omega, by omega, ?_⟩
      rw [show s + 8 * k - (8 * k + s) / w * w = (8 * k + s) % w by omega]; exact hb

theorem resAt_packRes (B w : Nat) (hB : 8 ∣ B) (hw : w ≤ 64) (res : Nat → UInt64) (P : ByteArray) (s : Nat)
    (hP : ∀ k < B * w / 8, P[s + k]? = (Kernel.Coc.packRes B w res)[k]?)
    (j : Nat) (hj : j < B) :
    Column.resAt P s w j = ((res j).toNat % 2 ^ w).toUInt64 := by
  by_cases w0 : w = 0
  · subst w0; simp [Column.resAt, Nat.mod_one]
  have hjw : j * w + w ≤ B * w := by
    have := Nat.mul_le_mul_right w (show j + 1 ≤ B from hj); rwa [Nat.succ_mul] at this
  have hb8 : B * w = 8 * (B / 8 * w) := by obtain ⟨q, rfl⟩ := hB; rw [Nat.mul_div_cancel_left q (by decide), Nat.mul_assoc]
  apply UInt64.toNat_inj.1
  unfold Column.resAt
  rw [foldl_or_u64]
  apply Nat.eq_of_testBit_eq; intro u
  rw [foldl_or_testBit]
  apply Bool.eq_iff_iff.2
  simp only [UInt64.toNat_zero, Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range'_1,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow, Bool.and_eq_true,
    decide_eq_true_eq, UInt64.toNat_ofNat', Nat.toUInt64_eq]
  constructor
  · rintro ⟨k, hk, h64, hu, hle, hb⟩
    obtain ⟨V, hV, hbit⟩ := packRes_byte B w res (by omega) k (by omega)
    rw [hP k (by omega), hV, Option.getD_some, hbit,
      show 8 * k + (u + j * w - 8 * k) = u + j * w by omega] at hb
    obtain ⟨hq, hr⟩ := field_of w (u + j * w) j (by omega) (by omega)
    rw [hq, hr, Nat.testBit_mod_two_pow, show u + j * w - j * w = u by omega] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨h64, hu, hb.2.2⟩
  · rintro ⟨h64, hu, hb⟩
    refine ⟨(u + j * w) / 8, ⟨by omega, by omega⟩, h64, hu, by omega, ?_⟩
    obtain ⟨V, hV, hbit⟩ := packRes_byte B w res (by omega) ((u + j * w) / 8) (by omega)
    rw [hP _ (by omega), hV, Option.getD_some, hbit,
      show 8 * ((u + j * w) / 8) + (u + j * w - 8 * ((u + j * w) / 8)) = u + j * w by omega]
    obtain ⟨hq, hr⟩ := field_of w (u + j * w) j (by omega) (by omega)
    rw [hq, hr, Nat.testBit_mod_two_pow, show u + j * w - j * w = u by omega]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, hu, hb⟩

theorem ba_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) : (a ++ b)[i]? = a[i]? := by
  show (a ++ b).data[i]? = a.data[i]?
  rw [ByteArray.data_append, Array.getElem?_append_left h]

theorem ba_append_right (a b : ByteArray) (k : Nat) : (a ++ b)[a.size + k]? = b[k]? := by
  show (a ++ b).data[a.size + k]? = b.data[k]?
  rw [ByteArray.data_append, show a.size = a.data.size from rfl,
    Array.getElem?_append_right (by omega)]
  simp

/-- `w` bytes read at `o` from `A` are the `w` bytes at `o'` from `S` when those bytes agree. -/
theorem bitsAt_shift (A S : ByteArray) (o o' w : Nat) (h : ∀ k < w, A[o + k]? = S[o' + k]?) :
    Column.bitsAt A o w = Column.bitsAt S o' w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [Column.bitsAt_succ, Column.bitsAt_succ, ih (fun k hk => h k (by omega)), h w (by omega)]

/-- The `w`-byte elements of a payload, as `Column.bitsAt` reads them. -/
def elemsW (w : Nat) (d : ByteArray) : List UInt64 := (List.range (d.size / w)).map fun i => Column.bitsAt d (i * w) w

/-- The first `n` ids of a payload packed at `w` bits, as `Column.idAt` reads them: `elemsW`'s
reader for an interned column's ids and a grouping's group ids. -/
def idsW (w n : Nat) (d : ByteArray) : List Nat := (List.range (Column.idsCap d w n)).map (Column.idAt d w ·)

/-- `packIds` reads `f` at the first `n` indices only. -/
theorem packIds_congr (w n : Nat) {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    Column.packIds w n f = Column.packIds w n g := by
  unfold Column.packIds
  split
  · congr 1; funext i hi acc; rw [h i hi]
  · split
    · rfl
    · dsimp only
      congr 1; funext k _ acc; congr 1; congr 1; funext j _ b'
      dsimp only
      by_cases hlt : k * (8 / w) + j < n
      · rw [if_pos hlt, if_pos hlt, h _ hlt]
      · rw [if_neg hlt, if_neg hlt]

/-- A fold of `w`-byte writes: its size, the bytes before it untouched, and element `i` read back
where it was written, modulo `2 ^ (8 * w)`. `Coc.decode`, `Coc.foRMeta`'s sections and `binBytes`'
answer are all one. -/
theorem foldl_pushBits {E : Type} (g : E → UInt64) (w : Nat) (hw : w ≤ 8) (l : List E) (a : ByteArray) :
    (l.foldl (fun acc e => Column.pushBits acc (g e) w) a).size = a.size + w * l.length ∧
    (∀ i < a.size, (l.foldl (fun acc e => Column.pushBits acc (g e) w) a)[i]? = a[i]?) ∧
    ∀ i (h : i < l.length), Column.bitsAt (l.foldl (fun acc e => Column.pushBits acc (g e) w) a) (a.size + w * i) w =
      UInt64.ofNat ((g l[i]).toNat % 2 ^ (8 * w)) := by
  induction l generalizing a with
  | nil => exact ⟨by simp, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | cons e l ih =>
    obtain ⟨hs, hp, hb⟩ := ih (Column.pushBits a (g e) w)
    have hsz := Column.pushBits_size a (g e) w
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [hs, hsz, Nat.mul_succ]; omega,
      fun i hi => by rw [hp i (by omega), Column.pushBits_getElem?_lt _ _ _ _ hi], ?_⟩
    intro i hi
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, Column.bitsAt_congr (Column.pushBits a (g e) w) _ a.size w
        (fun k hk => hp _ (by omega)), Column.bitsAt_pushBits _ _ _ hw]
    | succ i =>
      rw [List.getElem_cons_succ, ← hb i (by simp at hi; omega), hsz,
        show a.size + w * (i + 1) = a.size + w + w * i by rw [Nat.mul_succ]; omega]

/-- `Coc.decode` at a width up to eight holds `n` elements, element `i` being `foRBits`' on the low
`8 * w` bits. -/
theorem decodeW (w : USize) (hw : w.toNat ≤ 8) (md pk : ByteArray) (n : USize) :
    (Kernel.Coc.decode w md pk n).size = w.toNat * n.toNat ∧
    ∀ i < n.toNat, Column.bitsAt (Kernel.Coc.decode w md pk n) (i * w.toNat) w.toNat =
      UInt64.ofNat ((Column.foRBits md pk (Column.blockStarts md) i).toNat % 2 ^ (8 * w.toNat)) := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits id w.toNat hw (Kernel.Coc.elems md pk n) ByteArray.empty
  simp only [Kernel.Coc.decode]
  refine ⟨by simpa [Kernel.Coc.elems] using hs, fun i hi => ?_⟩
  have := hg i (by simp [Kernel.Coc.elems, hi])
  rw [Nat.mul_comm]
  simpa [Kernel.Coc.elems] using this

theorem foldl_push8 {E : Type} (g : E → UInt8) (l : List E) (a : ByteArray) :
    (l.foldl (fun acc e => acc.push (g e)) a).size = a.size + l.length ∧
    (∀ i < a.size, (l.foldl (fun acc e => acc.push (g e)) a)[i]? = a[i]?) ∧
    ∀ i (h : i < l.length), (l.foldl (fun acc e => acc.push (g e)) a)[a.size + i]? = some (g l[i]) := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    obtain ⟨hs, hp, hb⟩ := ih (a.push (g e))
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [hs, ba_size_push]; omega,
      fun i hi => by rw [hp i (by rw [ba_size_push]; omega), ba_push_getElem?, if_neg (by omega)], fun i hi => ?_⟩
    cases i with
    | zero =>
      rw [Nat.add_zero, hp _ (by rw [ba_size_push]; omega), ba_push_getElem?, if_pos rfl, List.getElem_cons_zero]
    | succ i =>
      rw [List.getElem_cons_succ, ← hb i (by simp at hi; omega), ba_size_push, show a.size + (i + 1) = a.size + 1 + i by omega]

theorem ba_append_right' (a b : ByteArray) (i : Nat) (h : a.size ≤ i) : (a ++ b)[i]? = b[i - a.size]? := by
  rw [show i = a.size + (i - a.size) by omega, ba_append_right]; congr 1; omega

theorem foldl_pair_size {E : Type} (f : ByteArray × Nat → E → ByteArray × Nat)
    (hf : ∀ p e, (f p e).1.size = p.1.size + 8) (l : List E) (p : ByteArray × Nat) :
    (l.foldl f p).1.size = p.1.size + 8 * l.length := by
  induction l generalizing p with
  | nil => simp
  | cons e l ih => simp only [List.foldl_cons, ih, hf, List.length_cons]; omega

/-- `Coc.foRMeta`'s size: 33 bytes a block and the 24-byte trailer. -/
theorem foRMeta_size (lg : Nat) (nul : UInt64) (sumn : Nat) (bs : Array (UInt64 × UInt64 × UInt64 × Nat)) :
    (Kernel.Coc.foRMeta lg nul sumn bs).size = 33 * bs.size + 24 := by
  have e0 : ByteArray.empty.size = 0 := rfl
  obtain ⟨s1, -, -⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s2, -, -⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s4, -, -⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.2.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s6, -, -⟩ := foldl_push8 (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.2.2.toUInt8) bs.toList ByteArray.empty
  have sT : (Column.pushBits (Column.pushBits (Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8)
      lg.toUInt64 8).size = 24 := by
    simp only [Column.pushBits_size, e0]
  have s3 := foldl_pair_size (fun (x : ByteArray × Nat) (b : UInt64 × UInt64 × UInt64 × Nat) =>
    (Column.pushBits x.fst x.snd.toUInt64 8, x.snd + 2 ^ lg * b.snd.snd.snd / 8))
    (fun _ _ => by simp only [Column.pushBits_size]) bs.toList (ByteArray.empty, 0)
  simp only [e0, Nat.zero_add, Array.length_toList] at s1 s2 s3 s4 s6
  unfold Kernel.Coc.foRMeta
  simp only [← Array.foldl_toList, ByteArray.size_append, s1, s2, s3, s4, s6, sT]; omega

theorem foRMeta_reads (lg : Nat) (hlg : lg < 2 ^ 64) (nul : UInt64) (sumn : Nat)
    (bs : Array (UInt64 × UInt64 × UInt64 × Nat)) (hw : ∀ b (h : b < bs.size), bs[b].2.2.2 < 256) :
    Column.nblk (Kernel.Coc.foRMeta lg nul sumn bs) = bs.size ∧ Column.lgAt (Kernel.Coc.foRMeta lg nul sumn bs) = lg ∧
    ∀ b (h : b < bs.size), Column.baseAt (Kernel.Coc.foRMeta lg nul sumn bs) b = bs[b].1 ∧
      Column.widthAt (Kernel.Coc.foRMeta lg nul sumn bs) b = bs[b].2.2.2 := by
  have e0 : ByteArray.empty.size = 0 := rfl
  obtain ⟨s1, -, g1⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s2, -, -⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s4, -, -⟩ := foldl_pushBits (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.2.1) 8 (by decide) bs.toList ByteArray.empty
  obtain ⟨s6, -, g6⟩ := foldl_push8 (fun b : UInt64 × UInt64 × UInt64 × Nat => b.2.2.2.toUInt8) bs.toList ByteArray.empty
  have sT2 : (Column.pushBits (Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8).size = 16 := by
    simp only [Column.pushBits_size, e0]
  have sT : (Column.pushBits (Column.pushBits (Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8)
      lg.toUInt64 8).size = 24 := by
    simp only [Column.pushBits_size, e0]
  simp only [e0, Nat.zero_add, Array.length_toList] at s1 s2 s4 s6 g1 g6
  have s3 := foldl_pair_size (fun (x : ByteArray × Nat) (b : UInt64 × UInt64 × UInt64 × Nat) =>
    (Column.pushBits x.fst x.snd.toUInt64 8, x.snd + 2 ^ lg * b.snd.snd.snd / 8))
    (fun _ _ => by simp only [Column.pushBits_size]) bs.toList (ByteArray.empty, 0)
  simp only [e0, Array.length_toList, Nat.zero_add] at s3
  have hn : Column.nblk (Kernel.Coc.foRMeta lg nul sumn bs) = bs.size := by
    rw [Column.nblk, foRMeta_size]; omega
  refine ⟨hn, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · unfold Column.lgAt
    rw [hn]
    unfold Kernel.Coc.foRMeta
    simp only [← Array.foldl_toList]
    rw [bitsAt_shift _ (Column.pushBits (Column.pushBits (Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8)
      lg.toUInt64 8) _ 16 8 (fun k hk => ?_)]
    · have := bitsAt_pushBits8 (Column.pushBits (Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8) lg.toUInt64
      rw [sT2] at this; rw [this, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlg]
    rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append, s1, s2, s3, s4, sT]; omega),
      ba_append_right' _ _ _ (by simp only [ByteArray.size_append, s1, s2, s3, s4]; omega)]
    simp only [ByteArray.size_append, s1, s2, s3, s4]
    have e : ∀ m, m = 16 + k → (Column.pushBits (Column.pushBits (Column.pushBits ByteArray.empty nul 8)
        sumn.toUInt64 8) lg.toUInt64 8)[m]? = (Column.pushBits (Column.pushBits (Column.pushBits ByteArray.empty nul 8)
        sumn.toUInt64 8) lg.toUInt64 8)[16 + k]? := fun m hm => hm ▸ rfl
    exact e _ (by omega)
  · unfold Column.baseAt Kernel.Coc.foRMeta
    simp only [← Array.foldl_toList]
    rw [Nat.mul_comm b 8, Column.bitsAt_congr _ _ (8 * b) 8 (fun k hk => ?_), g1 b hb]
    · simp only [Nat.reduceMul, ofNat_toNat_mod64]; simp
    repeat rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append, s1, s2, s3, s4, sT]; omega)]
  · unfold Column.widthAt
    rw [hn]
    unfold Kernel.Coc.foRMeta
    simp only [← Array.foldl_toList]
    rw [ba_append_right' _ _ _ (by simp only [ByteArray.size_append, s1, s2, s3, s4, sT]; omega)]
    simp only [ByteArray.size_append, s1, s2, s3, s4, sT]
    have e : ∀ m, m = b → (List.foldl (fun acc (e : UInt64 × UInt64 × UInt64 × Nat) => acc.push e.snd.snd.snd.toUInt8)
        ByteArray.empty bs.toList)[m]? = some bs.toList[b].snd.snd.snd.toUInt8 := fun m hm => hm ▸ g6 b hb
    rw [e _ (by omega)]
    have := hw b hb
    simp; omega

theorem packRes_size (B w : Nat) (res : Nat → UInt64) :
    (Kernel.Coc.packRes B w res).size = B * w / 8 := by
  unfold Kernel.Coc.packRes
  split
  · subst_vars; simp
  · rw [(fold_push_getElem? _ _ _).1, show (ByteArray.emptyWithCapacity (B * w / 8)).size = 0 from rfl, Nat.zero_add]

theorem pack_fold {E : Type} (f : ByteArray × Nat → E → ByteArray × Nat) (Q : Nat → E → ByteArray)
    (hf : ∀ a m e, f (a, m) e = (a ++ Q m e, m + 1)) (off : Nat → Nat) (l : List E) (a : ByteArray)
    (m : Nat) (h0 : off m = a.size)
    (hs : ∀ i (h : i < l.length), off (m + i + 1) = off (m + i) + (Q (m + i) l[i]).size) :
    (l.foldl f (a, m)).1.size = off (m + l.length) ∧
    (∀ i < a.size, (l.foldl f (a, m)).1[i]? = a[i]?) ∧
    ∀ i (h : i < l.length), ∀ k < (Q (m + i) l[i]).size,
      (l.foldl f (a, m)).1[off (m + i) + k]? = (Q (m + i) l[i])[k]? := by
  induction l generalizing a m with
  | nil => simp [h0]
  | cons e l ih =>
    have hs0 := hs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hs0
    obtain ⟨is, ip, ie⟩ := ih (a ++ Q m e) (m + 1) (by rw [hs0, h0, ByteArray.size_append])
      (fun i h => by
        have := hs (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + i = m + (i + 1) by omega]; exact this)
    rw [List.foldl_cons, hf]
    refine ⟨by rw [is]; congr 1; simp; omega,
      fun i hi => by rw [ip i (by rw [ByteArray.size_append]; omega), ba_append_left _ _ _ hi], ?_⟩
    intro i hi k hk
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero] at hk ⊢
      rw [h0, ip _ (by rw [ByteArray.size_append]; omega), ba_append_right]
    | succ i =>
      simp only [List.getElem_cons_succ] at hk ⊢
      have := ie i (by simp at hi; omega) k (by rw [show m + 1 + i = m + (i + 1) by omega]; exact hk)
      rw [show m + 1 + i = m + (i + 1) by omega] at this; exact this

theorem pack_fold0 {E : Type} (f : ByteArray × Nat → E → ByteArray × Nat) (Q : Nat → E → ByteArray)
    (hf : ∀ a m e, f (a, m) e = (a ++ Q m e, m + 1)) (off : Nat → Nat) (l : List E) (h0 : off 0 = 0)
    (hs : ∀ i (h : i < l.length), off (i + 1) = off i + (Q i l[i]).size) :
    (l.foldl f (ByteArray.empty, 0)).1.size = off l.length ∧
    ∀ i (h : i < l.length), ∀ k < (Q i l[i]).size,
      (l.foldl f (ByteArray.empty, 0)).1[off i + k]? = (Q i l[i])[k]? := by
  obtain ⟨a, -, c⟩ := pack_fold f Q hf off l ByteArray.empty 0 h0 (fun i h => by simpa using hs i h)
  simp only [Nat.zero_add] at a c
  exact ⟨a, c⟩

theorem foldl_min_le(l : List Nat) (a : Nat) : l.foldl min a ≤ a ∧ ∀ y ∈ l, l.foldl min a ≤ y := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    obtain ⟨h1, h2⟩ := ih (min a e)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

theorem le_foldl_max (l : List Nat) (a : Nat) : a ≤ l.foldl max a ∧ ∀ y ∈ l, y ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    obtain ⟨h1, h2⟩ := ih (max a e)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

theorem lt_widthFor (r : Nat) : r < 2 ^ Column.widthFor r := by
  unfold Column.widthFor; split
  · subst_vars; decide
  · exact Nat.lt_log2_self

theorem widthFor_le (r : Nat) (h : r < 2 ^ 64) : Column.widthFor r ≤ 64 := by
  unfold Column.widthFor; split
  · omega
  · have := (Nat.log2_lt (by assumption)).2 h; omega

theorem keyAt_lt (w : Nat) (hw : w ≤ 8) (x : ByteArray) (i : Nat) : Kernel.Coc.keyAt w x i < 2 ^ 64 := by
  unfold Kernel.Coc.keyAt Kernel.Coc.bias
  apply Nat.xor_lt_two_pow (UInt64.toNat_lt _)
  split
  · decide
  -- `Nat.pow_le_pow_right` to `2 ^ 63`, since `Nat.pow_lt_pow_right` brings `Classical.choice`
  · exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega : 8 * w - 1 ≤ 63)) (by decide)

/-- Element `i` of a block, against that block's extremes and residual width. -/
theorem blockOf_bounds (B w n b : Nat) (hw : w ≤ 8) (x : ByteArray) (i : Nat)
    (h1 : b * B ≤ i) (h2 : i < b * B + B) (h3 : i < n) :
    (Kernel.Coc.blockOf B w n b x).1 ≤ Kernel.Coc.keyAt w x i ∧
    Kernel.Coc.keyAt w x i - (Kernel.Coc.blockOf B w n b x).1 < 2 ^ (Kernel.Coc.blockOf B w n b x).2.2.2 ∧
    (Kernel.Coc.blockOf B w n b x).2.2.2 ≤ 64 := by
  unfold Kernel.Coc.blockOf
  simp only [← Array.foldl_toList]
  have hm : Kernel.Coc.keyAt w x i ∈ ((Array.range (min (b * B + B) n - b * B)).map
      fun j => Kernel.Coc.keyAt w x (b * B + j)).toList := by
    simp only [Array.toList_map, toList_range, List.mem_map, List.mem_range]
    exact ⟨i - b * B, by omega, by congr 1; omega⟩
  obtain ⟨-, hmn⟩ := foldl_min_le _ (Kernel.Coc.keyAt w x (b * B))
  obtain ⟨hlo, hmx⟩ := le_foldl_max _ (Kernel.Coc.keyAt w x (b * B))
  have a := hmn _ hm
  have c := hmx _ hm
  have d := keyAt_lt w hw x (b * B)
  have e : ∀ l : List Nat, (∀ y ∈ l, y < 2 ^ 64) → ∀ a < 2 ^ 64, l.foldl max a < 2 ^ 64 := by
    intro l; induction l with
    | nil => intro _ a ha; exact ha
    | cons y l ih =>
      intro hl a ha; simp only [List.foldl_cons]
      exact ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) _ (by have := hl y List.mem_cons_self; omega)
  refine ⟨a, ?_, widthFor_le _ ?_⟩
  · have := lt_widthFor (List.foldl max (Kernel.Coc.keyAt w x (b * B))
      ((Array.range (min (b * B + B) n - b * B)).map
        fun j => Kernel.Coc.keyAt w x (b * B + j)).toList - List.foldl min (Kernel.Coc.keyAt w x (b * B))
      ((Array.range (min (b * B + B) n - b * B)).map
        fun j => Kernel.Coc.keyAt w x (b * B + j)).toList)
    omega
  · have := e ((Array.range (min (b * B + B) n - b * B)).map fun j => Kernel.Coc.keyAt w x (b * B + j)).toList (fun y hy => by
      simp only [Array.toList_map, toList_range, List.mem_map] at hy
      obtain ⟨_, -, rfl⟩ := hy; exact keyAt_lt w hw x _) _ d
    omega

/-- An element no patch holds: its block's base, plus its frame's lift `fr`, plus its residual. -/
theorem foRBits_of (M P : ByteArray) (i : Nat) (B : Nat) (hB : Column.blk M = B) (base fr : UInt64) (wd : Nat)
    (R : Nat → UInt64)
    (hb : i / B ≤ Column.nblk M) (hwd : wd ≤ 64) (h2 : Column.baseAt M (i / B) = base)
    (h3 : Column.widthAt M (i / B) = wd)
    (h4 : ∀ k < B * wd / 8, P[Column.blockStart M (i / B) + k]? = (Kernel.Coc.packRes B wd R)[k]?)
    (hx : Column.foRExc M P i = none) (hf : Column.foRFrame M P (i / B) = fr) :
    Column.foRBits M P (Column.blockStarts M) i = base + fr + ((R (i % B)).toNat % 2 ^ wd).toUInt64 := by
  subst hB
  unfold Column.foRBits
  rw [hx]
  simp only [hf, blockStarts_get M hb, h2, h3]
  rw [resAt_packRes (Column.blk M) wd (blk_dvd8 M) hwd R P _ h4 _ (Nat.mod_lt _ (blk_pos M))]

theorem unbias_add (w mn k : Nat) (h : mn ≤ k) :
    Kernel.Coc.unbias w mn + (k - mn).toUInt64 = Kernel.Coc.unbias w k := by
  unfold Kernel.Coc.unbias
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

theorem raw_foR (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .u1)
    (n : USize) (M P : ByteArray) :
    Enc.raw (X := X) t n (.foR M P) = (Array.range n.toNat).map fun i =>
      UInt64.ofNat ((Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) := by
  cases t <;> simp_all [Enc.raw]

theorem raw_alp (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .u1)
    (n : USize) (M P a : ByteArray) :
    Enc.raw (X := X) t n (.alp M P a) = (Array.range n.toNat).map fun i =>
      UInt64.ofNat ((Column.alpBits M P a (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) := by
  cases t <;> simp_all [Enc.raw]

theorem raw_bytes (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .u1)
    (n : USize) (x : ByteArray) :
    Enc.raw (X := X) t n (.bytes x) = (Array.range n.toNat).map fun i => Column.bitsAt x (i * w) w := by
  cases t <;> simp_all [Enc.raw]

theorem encode_bytes (t : QAtomicType) (w : Nat) (ht : t.width = some w) (he : Column.encodes t = true)
    (n : USize) (x : ByteArray) :
    Enc.encode (X := X) t n (.bytes x) = .foR (Kernel.Coc.encode w.toUSize x).1 (Kernel.Coc.encode w.toUSize x).2 := by
  simp [Enc.encode, ht, he, Enc.bytesOf]

theorem bitsAt_lt (b : ByteArray) (o w : Nat) (hw : w ≤ 8) : (Column.bitsAt b o w).toNat < 2 ^ (8 * w) := by
  induction w with
  | zero => simp [Column.bitsAt]
  | succ w ih =>
    rw [Column.bitsAt_succ, UInt64.toNat_or]
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le (ih (by omega)) (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [UInt64.toNat_shiftLeft]
      have hs : (8 * w).toUInt64.toNat % 64 = 8 * w := by
        simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
      rw [hs, Nat.shiftLeft_eq]
      have hb := UInt8.toNat_lt ((b[o + w]?.getD 0))
      simp only [UInt8.toNat_toUInt64]
      refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
      rw [show 8 * (w + 1) = 8 * w + 8 by omega, Nat.pow_add, Nat.mul_comm (2 ^ (8 * w))]
      exact Nat.mul_lt_mul_of_pos_right (by simpa using hb) (Nat.two_pow_pos _)


/-- Flipping the top bit of an `m + 1`-bit number adds `2^m` below it and takes it away above. Bit by
bit rather than `bv_decide`, which brings `Lean.ofReduceBool`. -/
theorem xor_top (m n : Nat) (h : n < 2 ^ (m + 1)) :
    n ^^^ 2 ^ m = if n < 2 ^ m then n + 2 ^ m else n - 2 ^ m := by
  have hs := Nat.pow_succ 2 m
  have lo : ∀ a, a < 2 ^ m → a ^^^ 2 ^ m = a + 2 ^ m := fun a ha => by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.add_comm a, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i m with hi | rfl | hi
    · rw [Nat.testBit_two_pow_add_gt hi]; simp [show m ≠ i by omega]
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]; simp
    · have h1 : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
      rw [Nat.add_comm, Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
      simp [show m ≠ i by omega]
  split
  · exact lo _ ‹_›
  · have e : n = (n - 2 ^ m) + 2 ^ m := by omega
    rw [e, Nat.add_sub_cancel, ← lo _ (by omega), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The encoded form holds an element sign-extended to 64 bits, so it agrees with the dense bits on
the element's own `8 * w`, which below eight bytes is all it can; `Enc.raw` reads it cut to those. -/
theorem unbias_keyAt (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray) (i : Nat) :
    (Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i)).toNat % 2 ^ (8 * w) = (Column.bitsAt x (i * w) w).toNat := by
  have hv := bitsAt_lt x (i * w) w hw
  unfold Kernel.Coc.unbias Kernel.Coc.keyAt Kernel.Coc.bias
  by_cases h1 : w = 1
  · -- one byte is not biased: the key is the byte itself
    subst h1
    rw [if_pos rfl, Nat.xor_zero, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    generalize (Column.bitsAt x (i * 1) 1).toNat = v at hv ⊢
    simp only [Nat.reducePow, Nat.reduceMul, Nat.sub_zero] at hv ⊢; omega
  rw [if_neg h1]
  generalize (Column.bitsAt x (i * w) w).toNat = v at hv
  obtain ⟨m, hm⟩ : ∃ m, 8 * w = m + 1 := ⟨8 * w - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 64 = d + (m + 1) := ⟨64 - (m + 1), by omega⟩
  rw [hm] at hv ⊢; rw [show m + 1 - 1 = m by omega]
  have h64 : 2 ^ 64 = 2 ^ d * 2 ^ (m + 1) := by rw [hd, Nat.pow_add]
  have hs := Nat.pow_succ 2 m
  have hle : 2 ^ (m + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hsub := Nat.sub_one_mul (2 ^ d) (2 ^ (m + 1))
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ ⟨2 ^ d, by rw [h64, Nat.mul_comm]⟩,
    xor_top m v hv]
  split
  · rw [show v + 2 ^ m + (2 ^ 64 - 2 ^ m) = v + 2 ^ d * 2 ^ (m + 1) by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hv]
  · rw [show v - 2 ^ m + (2 ^ 64 - 2 ^ m) = v + (2 ^ d - 1) * 2 ^ (m + 1) by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hv]

/-- Five padded sections laid end to end, each read back at its own start. -/
theorem blob_get (pad : ByteArray → ByteArray) (hp : ∀ b k, k < b.size → (pad b)[k]? = b[k]?)
    (hs : ∀ b, b.size ≤ (pad b).size) (S0 S1 S2 S3 S4 : ByteArray) :
    (∀ k < S0.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[k]? = S0[k]?) ∧
    (∀ k < S1.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + k]? = S1[k]?) ∧
    (∀ k < S2.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size + k]? =
      S2[k]?) ∧
    (∀ k < S3.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size +
      (pad S2).size + k]? = S3[k]?) ∧
    (∀ k < S4.size, (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad S4)[(pad S0).size + (pad S1).size +
      (pad S2).size + (pad S3).size + k]? = S4[k]?) := by
  have h0 := hs S0; have h1 := hs S1; have h2 := hs S2; have h3 := hs S3
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by omega)]
    exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega), ba_append_right]
    exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      show (pad S0).size + (pad S1).size + k = (pad S0 ++ pad S1).size + k by rw [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk
  · rw [ba_append_left _ _ _ (by simp only [ByteArray.size_append]; omega),
      show (pad S0).size + (pad S1).size + (pad S2).size + k = (pad S0 ++ pad S1 ++ pad S2).size + k by
        simp only [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk
  · rw [show (pad S0).size + (pad S1).size + (pad S2).size + (pad S3).size + k =
        (pad S0 ++ pad S1 ++ pad S2 ++ pad S3).size + k by simp only [ByteArray.size_append],
      ba_append_right]; exact hp _ _ hk

/-- Core's `List.filter_eq_nil_iff`, which carries `Classical.choice`. -/
theorem filter_nil_of (p : Nat → Bool) (l : List Nat) (h : ∀ a ∈ l, p a = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.filter_cons, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]; rfl

/-- A byte of `a` is the same byte of `a ++ b`. -/
theorem ba_append_of (a b : ByteArray) (i : Nat) (v : UInt8) (h : a[i]? = some v) : (a ++ b)[i]? = some v := by
  by_cases hi : i < a.size
  · rw [ba_append_left _ _ _ hi, h]
  · rw [getElem?_neg a i hi] at h; cases h

/-- A fold each of whose steps keeps `P` ends in `P`: a block's minimum, its frame and its width are each one of
the values their fold is offered. -/
theorem foldl_pick {α β : Type} (P : α → Prop) (g : α → β → α) (l : List β) (a : α) (h0 : P a)
    (h : ∀ a, P a → ∀ b ∈ l, P (g a b)) : P (l.foldl g a) := by
  induction l generalizing a with
  | nil => exact h0
  | cons b l ih => exact ih _ (h a h0 b List.mem_cons_self) fun a ha c hc => h a ha c (List.mem_cons_of_mem _ hc)

/-- `Coc.planOf`'s frame is the minimum or one of the keys and its width at most that of the range; with patching
off they are the minimum and that width. -/
theorem planOf_bounds (pl : Bool) (ks : Array Nat) (mn mx w : Nat) :
    ((Kernel.Coc.planOf pl ks mn mx w).1 = mn ∨ (Kernel.Coc.planOf pl ks mn mx w).1 ∈ ks.toList) ∧
    (Kernel.Coc.planOf pl ks mn mx w).2 ≤ Column.widthFor (mx - mn) ∧
    (pl = false → Kernel.Coc.planOf pl ks mn mx w = (mn, Column.widthFor (mx - mn))) := by
  cases pl
  · exact ⟨Or.inl rfl, Nat.le_refl _, fun _ => rfl⟩
  refine ⟨?_, ?_, fun h => nomatch h⟩
  · show Kernel.Coc.frameAt ks mn _ = mn ∨ Kernel.Coc.frameAt ks mn _ ∈ ks.toList
    unfold Kernel.Coc.frameAt
    rw [← Array.foldl_toList]
    exact foldl_pick (fun f => f = mn ∨ f ∈ ks.toList) _ _ _ (Or.inl rfl) fun a ha k hk => by
      dsimp only; split
      · exact Or.inr hk
      · exact ha
  · show (List.foldl _ (0, _) _).1 ≤ _
    exact foldl_pick (fun p : Nat × Nat => p.1 ≤ Column.widthFor (mx - mn)) _ _ _ (Nat.zero_le _) fun ⟨a, _⟩ ha c hc => by
      dsimp only at ha ⊢; split
      · exact Nat.lt_succ_iff.1 (List.mem_range.1 hc)
      · exact ha

/-- Block `b`'s plan against its keys: the minimum is one of them and at most each, the frame lies from the minimum
to below `2 ^ 64`, the width is at most 64, and with patching off no key lies outside the frame. -/
theorem planBlock_bounds (lg w n : Nat) (hw : w ≤ 8) (pl : Bool) (x : ByteArray) (b : Nat) (hb : b * 2 ^ lg < n) :
    (Kernel.Coc.planBlock lg w n pl x b).1 ≤ (Kernel.Coc.planBlock lg w n pl x b).2.2.2.1 ∧
    (Kernel.Coc.planBlock lg w n pl x b).2.2.2.1 < 2 ^ 64 ∧ (Kernel.Coc.planBlock lg w n pl x b).2.2.2.2 ≤ 64 ∧
    (∃ j, b * 2 ^ lg ≤ j ∧ j < b * 2 ^ lg + 2 ^ lg ∧ j < n ∧
      Kernel.Coc.keyAt w x j = (Kernel.Coc.planBlock lg w n pl x b).1) ∧
    ∀ i, b * 2 ^ lg ≤ i → i < b * 2 ^ lg + 2 ^ lg → i < n →
      (Kernel.Coc.planBlock lg w n pl x b).1 ≤ Kernel.Coc.keyAt w x i ∧
      (pl = false → Kernel.Coc.outside (Kernel.Coc.planBlock lg w n pl x b).2.2.2.1
        (Kernel.Coc.planBlock lg w n pl x b).2.2.2.2 (Kernel.Coc.keyAt w x i) = false) := by
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  have hbo := fun i => blockOf_bounds (2 ^ lg) w n b hw x i
  have hW : (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.2.2 =
      Column.widthFor ((Kernel.Coc.blockOf (2 ^ lg) w n b x).2.1 - (Kernel.Coc.blockOf (2 ^ lg) w n b x).1) := rfl
  have hK : ∀ k ∈ ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
      fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)).toList,
      ∃ j, b * 2 ^ lg ≤ j ∧ j < b * 2 ^ lg + 2 ^ lg ∧ j < n ∧ Kernel.Coc.keyAt w x j = k := by
    intro k hk
    simp only [Array.toList_map, toList_range, List.mem_map, List.mem_range] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    exact ⟨b * 2 ^ lg + j, by omega, by omega, by omega, rfl⟩
  have hmn : (Kernel.Coc.blockOf (2 ^ lg) w n b x).1 ∈ ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
      fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)).toList := by
    show Array.foldl min _ _ ∈ _
    rw [← Array.foldl_toList]
    refine foldl_pick (· ∈ ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
      fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)).toList) _ _ _ ?_ fun a ha k hk => by
      dsimp only
      rcases Nat.le_total a k with h | h
      · rw [Nat.min_eq_left h]; exact ha
      · rw [Nat.min_eq_right h]; exact hk
    simp only [Array.toList_map, toList_range, List.mem_map, List.mem_range]
    exact ⟨0, by omega, rfl⟩
  obtain ⟨hf, hd, hp⟩ := planOf_bounds pl ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
      fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)) (Kernel.Coc.blockOf (2 ^ lg) w n b x).1
    (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.1 w
  rw [← hW] at hd hp
  obtain ⟨j0, h0a, h0b, h0c, h0k⟩ := hK _ hmn
  have hb64 := (hbo j0 h0a h0b h0c).2.2
  have e : Kernel.Coc.planBlock lg w n pl x b = ((Kernel.Coc.blockOf (2 ^ lg) w n b x).1,
      (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.1, (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.2.1,
      Kernel.Coc.planOf pl ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
        fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)) (Kernel.Coc.blockOf (2 ^ lg) w n b x).1
        (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.1 w) := rfl
  rw [e]; dsimp only
  have hf' : ∃ j, b * 2 ^ lg ≤ j ∧ j < b * 2 ^ lg + 2 ^ lg ∧ j < n ∧ Kernel.Coc.keyAt w x j =
      (Kernel.Coc.planOf pl ((Array.range (min (b * 2 ^ lg + 2 ^ lg) n - b * 2 ^ lg)).map
        fun j => Kernel.Coc.keyAt w x (b * 2 ^ lg + j)) (Kernel.Coc.blockOf (2 ^ lg) w n b x).1
        (Kernel.Coc.blockOf (2 ^ lg) w n b x).2.1 w).1 := by
    rcases hf with h | h
    · exact ⟨j0, h0a, h0b, h0c, h0k.trans h.symm⟩
    · exact hK _ h
  obtain ⟨j1, h1a, h1b, h1c, h1k⟩ := hf'
  refine ⟨h1k ▸ (hbo j1 h1a h1b h1c).1, h1k ▸ keyAt_lt w hw x j1, Nat.le_trans hd hb64, ⟨j0, h0a, h0b, h0c, h0k⟩,
    fun i h1 h2 h3 => ⟨(hbo i h1 h2 h3).1, fun hpl => ?_⟩⟩
  rw [hp hpl]
  have := hbo i h1 h2 h3
  simp only [Kernel.Coc.outside, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  -- one `omega` per conjunct: on a conjunction goal `omega` brings in `Classical.choice`
  exact ⟨by omega, by omega⟩

/-- Indices of a strictly increasing list below its count of entries under `m` are those whose entries are. -/
theorem lt_count (L : List Nat) (hL : L.Pairwise (· < ·)) (m k : Nat) (hk : k < L.length) :
    k < (L.filter (· < m)).length ↔ L[k] < m := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    rw [List.pairwise_cons] at hL
    have hnil : ¬ a < m → t.filter (· < m) = [] := fun h =>
      filter_nil_of _ _ fun y hy => decide_eq_false (by have := hL.1 y hy; omega)
    cases k with
    | zero => by_cases h : a < m <;> simp [List.filter_cons, h, hnil]
    | succ k =>
      have hk' : k < t.length := by simpa using hk
      have := hL.1 _ (List.getElem_mem hk')
      by_cases h : a < m
      · simp [List.filter_cons, h, ih hL.2 k hk']
      · simp [List.filter_cons, h, hnil h]; omega

/-- Looking element `i` up in a patch list the way `Column.foRExc` and `Column.alpBits` do — among the entries of
`i`'s block of `B`, by place in the block — finds `i`'s own entry, and finds one whenever `i` is listed. -/
theorem exc_find (B : Nat) (hB : 0 < B) (exc : Array Nat) (hs : exc.toList.Pairwise (· < ·)) (off pos : Nat → Nat)
    (i : Nat) (hoff : ∀ b, b = i / B ∨ b = i / B + 1 → off b = (exc.filter (· < b * B)).size)
    (hpos : ∀ k (h : k < exc.size), pos k = exc[k] % B) :
    (∀ k, ((List.range' (off (i / B)) (off (i / B + 1) - off (i / B))).find? fun k => pos k == i % B) = some k →
      ∃ h : k < exc.size, exc[k] = i) ∧
    (i ∈ exc.toList →
      ((List.range' (off (i / B)) (off (i / B + 1) - off (i / B))).find? fun k => pos k == i % B) ≠ none) := by
  have hc : ∀ b, (exc.filter (· < b * B)).size = (exc.toList.filter (· < b * B)).length := fun b => by
    rw [← Array.toList_filter, Array.length_toList]
  rw [hoff _ (Or.inl rfl), hoff _ (Or.inr rfl), hc, hc]
  have hle : (exc.toList.filter (· < (i / B + 1) * B)).length ≤ exc.size :=
    Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq Array.length_toList)
  have hi1 : i / B * B ≤ i := Nat.div_mul_le_self i B
  have hi2 : i < (i / B + 1) * B := by
    rw [Nat.succ_mul]; have := Nat.div_add_mod i B; have := Nat.mod_lt i hB; rw [Nat.mul_comm] at hi1 ⊢; omega
  -- `k` lies in `i`'s run of the list exactly when its entry lies in `i`'s block
  have hrun : ∀ k (h : k < exc.size), (exc.toList.filter (· < i / B * B)).length ≤ k ∧
      k < (exc.toList.filter (· < (i / B + 1) * B)).length ↔ i / B * B ≤ exc[k] ∧ exc[k] < (i / B + 1) * B := by
    intro k h
    have a := lt_count exc.toList hs (i / B * B) k (by simpa using h)
    have c := lt_count exc.toList hs ((i / B + 1) * B) k (by simpa using h)
    simp only [Array.getElem_toList] at a c
    constructor
    · intro ⟨h1, h2⟩; exact ⟨Nat.le_of_not_lt fun h' => absurd (a.2 h') (by omega), c.1 h2⟩
    · intro ⟨h1, h2⟩; exact ⟨Nat.le_of_not_lt fun h' => absurd (a.1 h') (by omega), c.2 h2⟩
  refine ⟨fun k hk => ?_, fun hm hn => ?_⟩
  · have hp := List.find?_some hk
    have hm := List.mem_of_find?_eq_some hk
    rw [List.mem_range'_1] at hm
    have hks : k < exc.size := by omega
    refine ⟨hks, ?_⟩
    have hb := (hrun k hks).1 ⟨hm.1, by omega⟩
    rw [hpos k hks, beq_iff_eq] at hp
    have hq : exc[k] / B = i / B := Nat.div_eq_of_lt_le hb.1 hb.2
    rw [← Nat.div_add_mod exc[k] B, ← Nat.div_add_mod i B, hq, hp]
  · obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 hm
    have hks : k < exc.size := by simpa using hk
    simp only [Array.getElem_toList] at hki
    have hb := (hrun k hks).2 (by rw [hki]; exact ⟨hi1, hi2⟩)
    rw [List.find?_eq_none] at hn
    exact hn k (by rw [List.mem_range'_1]; exact ⟨by omega, by omega⟩) (by rw [hpos k hks, hki, beq_iff_eq])

/-- `Coc.excBlob` as its five sections, each through a `pad` that keeps its bytes and rounds its size up to 8, at
any count: the sections' layout owes nothing to the arguments. -/
theorem excBlob_eq (word : UInt64) (B w nb : Nat) (x : ByteArray) (exc : Array Nat) (last : ByteArray) :
    ∃ pad : ByteArray → ByteArray, (∀ b k, k < b.size → (pad b)[k]? = b[k]?) ∧
      (∀ b, (pad b).size = (b.size + 7) / 8 * 8) ∧
      Kernel.Coc.excBlob word B w nb x exc last =
        pad (Column.pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) word 8)
        ++ pad (exc.foldl (init := ByteArray.empty) fun acc i => Column.pushBits acc (Column.bitsAt x (i * w) w) w)
        ++ pad ((Array.range (nb + 1)).foldl (init := ByteArray.empty) fun acc b =>
             Column.pushBits acc (exc.filter (· < b * B)).size.toUInt64 4)
        ++ pad (exc.foldl (init := ByteArray.empty) fun acc i => Column.pushBits acc (i % B).toUInt64 2)
        ++ pad last := by
  refine ⟨_, fun b k h => ?_, fun b => ?_, rfl⟩
  · exact ba_append_left _ _ _ h
  · show (b ++ ⟨Array.replicate ((8 - b.size % 8) % 8) 0⟩).size = _
    simp only [ByteArray.size_append]
    show b.size + (Array.replicate ((8 - b.size % 8) % 8) (0 : UInt8)).size = _
    rw [Array.size_replicate]; omega

/-- What each reader of an exception ladder answers on `Coc.excBlob`'s bytes, laid at offset `e` of `P`: the count,
the word, each listed element's bits, the block offsets, the places in the block and the last section. -/
theorem excBlob_reads (word : UInt64) (B : Nat) (hB : 0 < B ∧ B ≤ 65536) (w : Nat) (hw : w ≤ 8) (nb : Nat)
    (x : ByteArray) (exc : Array Nat) (last : ByteArray) (hn : exc.size < 2 ^ 32) (P : ByteArray) (e : Nat)
    (hP : ∀ k < (Kernel.Coc.excBlob word B w nb x exc last).size,
      P[e + k]? = (Kernel.Coc.excBlob word B w nb x exc last)[k]?) :
    (Column.bitsAt P e 8).toNat = exc.size ∧ Column.bitsAt P (e + 8) 8 = word ∧
    (∀ k (h : k < exc.size), Column.bitsAt P (e + 16 + k * w) w = Column.bitsAt x (exc[k] * w) w) ∧
    (∀ b ≤ nb, (Column.bitsAt P (e + (Column.alpSects nb exc.size w).1 + b * 4) 4).toNat =
      (exc.filter (· < b * B)).size) ∧
    (∀ k (h : k < exc.size), (Column.bitsAt P (e + (Column.alpSects nb exc.size w).2.1 + k * 2) 2).toNat =
      exc[k] % B) ∧
    (∀ k < last.size, P[e + (Column.alpSects nb exc.size w).2.2 + k]? = last[k]?) ∧
    16 ≤ (Kernel.Coc.excBlob word B w nb x exc last).size ∧
    (Kernel.Coc.excBlob word B w nb x exc last).size = (Column.alpSects nb exc.size w).2.2 + (last.size + 7) / 8 * 8 := by
  have hsz : ∀ p : Nat → Bool, (exc.filter p).size ≤ exc.size := fun p => by
    have := List.length_filter_le p exc.toList
    rw [← Array.toList_filter, Array.length_toList, Array.length_toList] at this; exact this
  have e0 : ByteArray.empty.size = 0 := rfl
  obtain ⟨pad, hpg, hps, hA⟩ := excBlob_eq word B w nb x exc last
  rw [hA] at hP ⊢
  generalize hS0 : Column.pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) word 8 = S0 at hP ⊢
  generalize hS1 : exc.foldl (init := ByteArray.empty)
    (fun acc i => Column.pushBits acc (Column.bitsAt x (i * w) w) w) = S1 at hP ⊢
  generalize hS2 : (Array.range (nb + 1)).foldl (init := ByteArray.empty)
    (fun acc b => Column.pushBits acc (exc.filter (· < b * B)).size.toUInt64 4) = S2 at hP ⊢
  generalize hS3 : exc.foldl (init := ByteArray.empty)
    (fun acc i => Column.pushBits acc (i % B).toUInt64 2) = S3 at hP ⊢
  have X8 : (Column.pushBits ByteArray.empty exc.size.toUInt64 8).size = 8 := by rw [Column.pushBits_size, e0]
  have z0 : S0.size = 16 := by rw [← hS0, Column.pushBits_size, X8]
  have W1 := foldl_pushBits (fun i => Column.bitsAt x (i * w) w) w hw exc.toList ByteArray.empty
  rw [Array.foldl_toList, hS1, e0] at W1
  have z1 : S1.size = exc.size * w := by rw [W1.1, Array.length_toList, Nat.zero_add, Nat.mul_comm]
  have r1 : ∀ k (h : k < exc.size), Column.bitsAt S1 (w * k) w = Column.bitsAt x (exc[k] * w) w := by
    intro k hk
    have := W1.2.2 k (by simpa using hk)
    simp only [Nat.zero_add, Array.getElem_toList] at this
    rw [this, Nat.mod_eq_of_lt (bitsAt_lt _ _ _ hw), UInt64.ofNat_toNat]
  have hS2' : S2 = (List.range (nb + 1)).foldl (init := ByteArray.empty)
      (fun acc b => Column.pushBits acc (exc.filter (· < b * B)).size.toUInt64 4) := by
    rw [← hS2, ← Array.foldl_toList, toList_range]
  have W2 := foldl_pushBits (fun b => (exc.filter (· < b * B)).size.toUInt64) 4 (by decide)
    (List.range (nb + 1)) ByteArray.empty
  rw [← hS2', e0] at W2
  have z2 : S2.size = 4 * (nb + 1) := by rw [W2.1, List.length_range, Nat.zero_add]
  have r2 : ∀ b ≤ nb, (Column.bitsAt S2 (4 * b) 4).toNat = (exc.filter (· < b * B)).size := by
    intro b hb
    have := W2.2.2 b (by simp; omega)
    rw [Nat.zero_add, List.getElem_range] at this
    rw [this]
    have := hsz (· < b * B)
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]; omega
  have W3 := foldl_pushBits (fun i => (i % B).toUInt64) 2 (by decide) exc.toList ByteArray.empty
  rw [Array.foldl_toList, hS3, e0] at W3
  have z3 : S3.size = 2 * exc.size := by rw [W3.1, Array.length_toList, Nat.zero_add]
  have r3 : ∀ k (h : k < exc.size), (Column.bitsAt S3 (2 * k) 2).toNat = exc[k] % B := by
    intro k hk
    have := W3.2.2 k (by simpa using hk)
    rw [Nat.zero_add] at this
    rw [this]
    have : exc[k] % B < 65536 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hB.1) hB.2
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq, Array.getElem_toList]; omega
  obtain ⟨g0, g1, g2, g3, g4⟩ := blob_get pad hpg (fun b => by rw [hps]; omega) S0 S1 S2 S3 last
  have p0 : (pad S0).size = 16 := by rw [hps, z0]
  have p1 : (pad S1).size = (exc.size * w + 7) / 8 * 8 := by rw [hps, z1]
  have p2 : (pad S2).size = (4 * (nb + 1) + 7) / 8 * 8 := by rw [hps, z2]
  have p3 : (pad S3).size = (2 * exc.size + 7) / 8 * 8 := by rw [hps, z3]
  have p4 : last.size ≤ (pad last).size := by rw [hps]; omega
  have hAs : (pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad last).size =
      (pad S0).size + (pad S1).size + (pad S2).size + (pad S3).size + (pad last).size := by
    simp only [ByteArray.size_append]
  generalize pad S0 ++ pad S1 ++ pad S2 ++ pad S3 ++ pad last = A at g0 g1 g2 g3 g4 hP hAs ⊢
  -- a read of `P` at `e + o` is the read of `A` at `o`, inside `A`
  have hPA : ∀ q o (S : ByteArray) o' len, q = e + o → o + len ≤ A.size →
      (∀ t < len, A[o + t]? = S[o' + t]?) → Column.bitsAt P q len = Column.bitsAt S o' len :=
    fun q o S o' len hq hl h => hq ▸ bitsAt_shift P S (e + o) o' len fun t ht => by
      rw [Nat.add_assoc, hP _ (by omega), h t ht]
  have hcnt := Column.bitsAt_pushBits ByteArray.empty exc.size.toUInt64 8 (by decide)
  rw [e0] at hcnt
  have hwd := Column.bitsAt_pushBits (Column.pushBits ByteArray.empty exc.size.toUInt64 8) word 8 (by decide)
  rw [X8] at hwd
  simp only [Column.alpSects]
  refine ⟨?_, ?_, fun k hk => ?_, fun b hb => ?_, fun k hk => ?_, fun k hk => ?_, by omega,
    by rw [hAs, p0, p1, p2, p3, hps]; omega⟩
  · rw [hPA e 0 S0 0 8 (by omega) (by omega) (fun t ht => by rw [Nat.zero_add]; exact g0 t (by omega)), ← hS0,
      bitsAt_shift _ (Column.pushBits ByteArray.empty exc.size.toUInt64 8) 0 0 8
        (fun t ht => Column.pushBits_getElem?_lt _ _ _ _ (by rw [X8]; omega)), hcnt]
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]; omega
  · rw [hPA _ 8 S0 8 8 rfl (by omega) (fun t ht => g0 _ (by omega)), ← hS0, hwd]
    show UInt64.ofNat (word.toNat % 2 ^ 64) = word
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · have hk' : w * k + w ≤ S1.size := by
      rw [z1, Nat.mul_comm exc.size, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
    rw [← r1 k hk]
    exact hPA _ (16 + w * k) S1 (w * k) w (by rw [Nat.mul_comm]; omega) (by omega) fun t ht => by
      rw [← g1 (w * k + t) (by omega), p0, Nat.add_assoc]
  · rw [← r2 b hb]
    congr 1
    exact hPA _ ((16 + exc.size * w + 7) / 8 * 8 + 4 * b) S2 (4 * b) 4 (by omega) (by omega) fun t ht => by
      rw [← g2 (4 * b + t) (by omega), p0, p1]; congr 1; omega
  · rw [← r3 k hk]
    congr 1
    exact hPA _ (((16 + exc.size * w + 7) / 8 * 8 + (nb + 1) * 4 + 7) / 8 * 8 + 2 * k) S3 (2 * k) 2 (by omega)
      (by omega) fun t ht => by
      rw [← g3 (2 * k + t) (by omega), p0, p1, p2]; congr 1; omega
  · rw [show e + ((((16 + exc.size * w + 7) / 8 * 8 + (nb + 1) * 4 + 7) / 8 * 8 + exc.size * 2 + 7) / 8 * 8) + k =
      e + ((pad S0).size + (pad S1).size + (pad S2).size + (pad S3).size + k) by rw [p0, p1, p2, p3]; omega,
      hP _ (by omega), g4 k hk]

/-- `Column.foRExc`'s reading of a `w`-byte element `v` — one byte as it is, a wider one sign-extended from its
`8 * w` bits by a shift up and an arithmetic shift down — is `unbias` of its key: the form a block minimum is in. -/
theorem sext_unbias (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (v : UInt64) (hv : v.toNat < 2 ^ (8 * w)) :
    (if w == 1 then v else ((v <<< (64 - 8 * w).toUInt64).toInt64 >>> (64 - 8 * w).toUInt64.toInt64).toUInt64) =
      Kernel.Coc.unbias w (v.toNat ^^^ Kernel.Coc.bias w) := by
  by_cases h1 : w = 1
  · subst h1
    unfold Kernel.Coc.unbias Kernel.Coc.bias
    apply UInt64.toNat_inj.1
    simp only [Nat.reduceMul, Nat.reducePow] at hv
    show v.toNat = _
    rw [if_pos rfl, Nat.xor_zero, Nat.sub_zero, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [if_neg (by simpa using h1)]
  apply UInt64.toNat_inj.1
  -- through `toInt` and `Int` division: `BitVec.toNat_sshiftRight` carries `Classical.choice`
  rw [UInt64.toNat, Int64.toBitVec_toUInt64, Int64.toBitVec_shiftRight, UInt64.toBitVec_toInt64,
    UInt64.toBitVec_shiftLeft, BitVec.sshiftRight_eq']
  unfold BitVec.sshiftRight
  rw [BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  unfold Kernel.Coc.unbias Kernel.Coc.bias
  rw [if_neg h1]
  have hb := xor_top (8 * w - 1) v.toNat (by rw [show 8 * w - 1 + 1 = 8 * w by omega]; exact hv)
  rw [hb]
  rcases (by omega : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow, Int.shiftRight_eq_div_pow] at hv ⊢
    simp [Nat.shiftLeft_eq]
    split <;> split <;> omega

/-- `Column.foRExc` on a pack whose patch list `Coc.excBlob` wrote after the residuals: element `i`'s own bits,
sign-extended as a block minimum is, when `i` is listed, and nothing otherwise. -/
theorem foRExc_excBlob (M pack : ByteArray) (B : Nat) (hBM : Column.blk M = B) (hB : 0 < B ∧ B ≤ 65536) (w : Nat)
    (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray) (exc : Array Nat) (hs : exc.toList.Pairwise (· < ·))
    (hn : exc.size < 2 ^ 32) (word : UInt64) (last : ByteArray) (hword : word.toNat % 256 = w)
    (he : Column.blockStart M (Column.nblk M) = pack.size) (i : Nat) (hi : i / B < Column.nblk M) :
    Column.foRExc M (pack ++ Kernel.Coc.excBlob word B w (Column.nblk M) x exc last) i =
      if i ∈ exc.toList then some (Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i)) else none := by
  obtain ⟨hc, hwd, hraw, hoff, hpos, -, h16, -⟩ := excBlob_reads word B hB w hw (Column.nblk M) x exc last hn _
    pack.size (fun k _ => ba_append_right _ _ _)
  obtain ⟨f1, f2⟩ := exc_find B hB.1 exc hs
    (fun b => (Column.bitsAt (pack ++ Kernel.Coc.excBlob word B w (Column.nblk M) x exc last)
      (pack.size + (Column.alpSects (Column.nblk M) exc.size w).1 + b * 4) 4).toNat)
    (fun k => (Column.bitsAt (pack ++ Kernel.Coc.excBlob word B w (Column.nblk M) x exc last)
      (pack.size + (Column.alpSects (Column.nblk M) exc.size w).2.1 + k * 2) 2).toNat) i
    (fun b hb => hoff b (by omega)) hpos
  simp only [Column.alpSects] at f1 f2
  unfold Column.foRExc
  simp only [he, ByteArray.size_append, hwd, hword, hc, hBM, Column.alpSects]
  rw [if_neg (by omega)]
  rcases Decidable.em (i ∈ exc.toList) with hm | hm
  · rw [if_pos hm]
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (f2 hm)
    obtain ⟨hk1, hk2⟩ := f1 k hk
    rw [hk]
    simp only [Option.map]
    rw [hraw k hk1, hk2]
    exact congrArg some (sext_unbias w hw0 hw _ (bitsAt_lt _ _ _ hw))
  · -- by cases, not `Option.eq_none_iff_forall_ne_some`, which carries `Classical.choice`
    rw [if_neg hm, Option.map_eq_none_iff]
    revert f1
    cases (List.range' _ _).find? _ with
    | none => intro _; rfl
    | some k =>
      intro f1
      obtain ⟨hk1, hk2⟩ := f1 k rfl
      exact absurd (hk2 ▸ Array.getElem_mem_toList _) hm

/-- `Column.foRFrame` on a pack whose patch list `Coc.excBlob` wrote after the residuals: block `b`'s entry of the
frames `fs` the list ends in when bit 8 of its word says so, and `0` otherwise. -/
theorem foRFrame_excBlob (M pack : ByteArray) (B : Nat) (hB : 0 < B ∧ B ≤ 65536) (w : Nat) (hw : w ≤ 8)
    (x : ByteArray) (exc : Array Nat) (hn : exc.size < 2 ^ 32) (word : UInt64) (last : ByteArray)
    (hword : word.toNat % 256 = w) (he : Column.blockStart M (Column.nblk M) = pack.size) (fs : Array UInt64)
    (hfs : fs.size = Column.nblk M)
    (hl : word.toNat / 256 % 2 = 1 → last = fs.foldl (fun acc v => Column.pushBits acc v 8) ByteArray.empty)
    (b : Nat) (hb : b < Column.nblk M) :
    Column.foRFrame M (pack ++ Kernel.Coc.excBlob word B w (Column.nblk M) x exc last) b =
      if word.toNat / 256 % 2 = 1 then fs[b]?.getD 0 else 0 := by
  obtain ⟨hc, hwd, -, -, -, hlast, h16, -⟩ := excBlob_reads word B hB w hw (Column.nblk M) x exc last hn _
    pack.size (fun k _ => ba_append_right _ _ _)
  simp only [Column.alpSects] at hlast
  unfold Column.foRFrame
  simp only [he, ByteArray.size_append, hwd, hword, hc, Column.alpSects]
  rcases Nat.mod_two_eq_zero_or_one (word.toNat / 256) with h1 | h1
  · -- `rw`, not `simp [h1]`: deciding `0 = 1` by `simp` brings in `Classical.choice`
    rw [h1, if_neg Nat.zero_ne_one]; exact if_pos (Bool.or_true _)
  have W := foldl_pushBits (fun v : UInt64 => v) 8 (by decide) fs.toList ByteArray.empty
  rw [Array.foldl_toList, ← hl h1] at W
  have hlz : last.size = 8 * fs.size := by rw [W.1]; simp
  have hr := W.2.2 b (by simp; omega)
  simp only [h1, Nat.one_ne_zero, decide_false, Bool.or_false, if_true]
  rw [if_neg (by simp; omega), bitsAt_shift _ last _ (b * 8) 8 (fun t ht => by rw [Nat.add_assoc, hlast _ (by omega)]),
    show b * 8 = ByteArray.empty.size + 8 * b by simp; omega, hr, getElem?_pos fs b (by omega)]
  simp [Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

/-- A pack laid block by block, block `b`'s residuals at the width the metadata `M` declares for it, ends where `M`'s
block starts say the last block does, and holds each block's residuals at that block's start. -/
theorem pack_blockStart {E : Type} (M : ByteArray) (B : Nat) (hB : Column.blk M = B) (bs : Array E) (d : E → Nat)
    (hnb : Column.nblk M = bs.size) (hd : ∀ b (h : b < bs.size), Column.widthAt M b = d bs[b])
    (f : ByteArray × Nat → E → ByteArray × Nat) (Q : Nat → E → Nat → UInt64)
    (hf : ∀ a m e, f (a, m) e = (a ++ Kernel.Coc.packRes B (d e) (Q m e), m + 1)) :
    (bs.foldl f (ByteArray.empty, 0)).1.size = Column.blockStart M (Column.nblk M) ∧
    ∀ i (h : i < bs.size), ∀ k < (Kernel.Coc.packRes B (d bs[i]) (Q i bs[i])).size,
      (bs.foldl f (ByteArray.empty, 0)).1[Column.blockStart M i + k]? = (Kernel.Coc.packRes B (d bs[i]) (Q i bs[i]))[k]? := by
  have h := pack_fold0 f (fun m e => Kernel.Coc.packRes B (d e) (Q m e)) hf (Column.blockStart M) bs.toList rfl
    (fun c h => by rw [packRes_size, blockStart_succ, hB, hd c (by simpa using h)]; simp)
  rw [Array.foldl_toList] at h
  simp only [Array.length_toList, Array.getElem_toList] at h
  exact ⟨by rw [h.1, hnb], h.2⟩

/-- The encoder model reads back element by element, at any block size `2 ^ lg` the layout admits, patched or not:
a kept element is its block's base, plus its frame's lift, plus its residual; a patched one is its own bits. -/
theorem foRBits_encode (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray)
    {patch : Bool} (i : Nat) (hi : i < x.size / w) :
    Column.foRBits (Kernel.Coc.encodeAt lg w.toUSize x patch).1 (Kernel.Coc.encodeAt lg w.toUSize x patch).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg w.toUSize x patch).1) i =
      Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i) := by
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  have hB16 : 2 ^ lg ≤ 65536 := Nat.pow_le_pow_right (by decide) hlg.2
  unfold Kernel.Coc.encodeAt
  simp only [hwt]
  generalize hn : x.size / w = n at *
  have hpb := fun b => planBlock_bounds lg w n hw (patch && decide (n < 2 ^ 32)) x b
  have h32 : (patch && decide (n < 2 ^ 32)) = true → n < 2 ^ 32 := fun h => by simp at h; exact h.2
  generalize (patch && decide (n < 2 ^ 32)) = pl at hpb h32 ⊢
  generalize Kernel.Coc.planBlock lg w n pl x = blk at hpb ⊢
  generalize hbs : Array.map blk (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)) = bs
  have hbsz : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = blk b := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hib : i / 2 ^ lg < bs.size := hbsz ▸ lt_cdiv hBp hi
  have hkeys := fun j (hj : j < n) => (hpb (j / 2 ^ lg) (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hj)).2.2.2.2 j
    (Nat.div_mul_le_self _ _) (by have := Nat.mod_add_div' j (2 ^ lg); have := Nat.mod_lt j hBp; omega) hj
  -- the metadata
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    (bs.map fun x => (Kernel.Coc.unbias w x.1, Kernel.Coc.unbias w x.2.1, x.2.2.1, x.2.2.2.2)) (fun b h => by
      simp only [Array.size_map] at h; simp only [Array.getElem_map]; rw [hbget b h]
      exact Nat.lt_of_le_of_lt (hpb b (mul_lt_of_lt_cdiv hBp (hbsz ▸ h))).2.2.1 (by decide))
  generalize Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) n _ = M at hMr ⊢
  obtain ⟨hnb, hlgM, hMb⟩ := hMr
  -- the pair, not `by omega`: omega's proof of this `∧` goal depends on `Classical.choice`
  have hBM : Column.blk M = 2 ^ lg := by rw [blk_of_lgAt M ⟨hlgM ▸ hlg.1, hlgM ▸ hlg.2⟩, hlgM]
  simp only [Array.size_map] at hnb hMb
  -- the patch list
  -- the patch list reads each plan from `bs`, which is `blk` at every element's block
  have hbg : ∀ j < n, bs.getD (j / 2 ^ lg) default = blk (j / 2 ^ lg) := fun j hj => by
    have h : j / 2 ^ lg < bs.size := hbsz ▸ lt_cdiv hBp hj
    unfold Array.getD; rw [dif_pos h]; exact hbget _ h
  have hexs : (Array.filter (fun i => Kernel.Coc.outside (bs.getD (i / 2 ^ lg) default).2.2.2.1
      (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) (Array.range n)).toList.Pairwise (· < ·) := by
    -- by index, not `List.pairwise_lt_range`, which carries `Classical.choice`
    rw [Array.toList_filter, toList_range]
    exact (List.pairwise_iff_getElem.2 fun i j _ _ h => by rw [List.getElem_range, List.getElem_range]; exact h).filter _
  have hmem : ∀ j, j ∈ (Array.filter (fun i => Kernel.Coc.outside (bs.getD (i / 2 ^ lg) default).2.2.2.1
      (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) (Array.range n)).toList ↔
      j < n ∧ Kernel.Coc.outside (blk (j / 2 ^ lg)).2.2.2.1 (blk (j / 2 ^ lg)).2.2.2.2 (Kernel.Coc.keyAt w x j) = true := by
    intro j; rw [Array.toList_filter, toList_range, List.mem_filter, List.mem_range]
    exact and_congr_right fun h => by rw [hbg j h]
  have hen : (Array.filter (fun i => Kernel.Coc.outside (bs.getD (i / 2 ^ lg) default).2.2.2.1
      (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) (Array.range n)).size ≤ n := by
    rw [← Array.length_toList, Array.toList_filter, toList_range]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  generalize Array.filter (fun i => Kernel.Coc.outside (bs.getD (i / 2 ^ lg) default).2.2.2.1
      (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i)) (Array.range n) = exc at hexs hmem hen ⊢
  have hnil : exc.size = 0 → exc.toList = [] := fun h => by
    rw [← Array.length_toList] at h; exact List.eq_nil_of_length_eq_zero h
  -- a list is written only with patching on, so below `2 ^ 32` elements
  have h32' : exc.size ≠ 0 → exc.size < 2 ^ 32 := fun h => by
    cases hpl : pl
    · -- by cases on the list, not `List.eq_nil_iff_forall_not_mem`, which carries `Classical.choice`
      have he : exc.toList = [] := by
        cases hl : exc.toList with
        | nil => rfl
        | cons j t =>
          have := (hmem j).1 (hl ▸ List.mem_cons_self)
          rw [(hkeys j this.1).2 hpl] at this; exact absurd this.2 Bool.false_ne_true
      exact absurd (by rw [← Array.length_toList, he]; rfl) h
    · exact Nat.lt_of_le_of_lt hen (h32 hpl)
  -- the frames
  have hfr0 : ((Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs).any
      fun a => a != 0) = false → ∀ b (h : b < bs.size), ((blk b).2.2.2.1 - (blk b).1).toUInt64 = 0 := fun h b hb =>
    Decidable.byContradiction fun hne => by
      have : ((Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs).any
          fun a => a != 0) = true := Array.any_eq_true.2 ⟨b, by simpa using hb, by simp [hbget b hb, hne]⟩
      rw [h] at this; cases this
  have hfs : ∀ b (h : b < bs.size), (Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64)
      bs)[b]? = some ((blk b).2.2.2.1 - (blk b).1).toUInt64 := fun b h => by simp [h, hbget b h]
  have hfsz : (Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs).size =
      Column.nblk M := by simp [hnb]
  generalize Array.map (fun x : Nat × Nat × UInt64 × Nat × Nat => (x.2.2.2.1 - x.1).toUInt64) bs = fs
    at hfr0 hfs hfsz ⊢
  have hword : ∀ fr : Bool, (w.toUInt64 ||| if fr = true then 256 else 0).toNat % 256 = w ∧
      ((w.toUInt64 ||| if fr = true then 256 else 0).toNat / 256 % 2 = 1 ↔ fr = true) := by
    intro fr
    rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases fr <;> decide
  generalize (fs.any fun a => a != 0) = frm at hfr0 ⊢
  -- the residuals
  have hQ := pack_blockStart M (2 ^ lg) hBM bs (·.2.2.2.2) hnb (fun c h => by rw [(hMb c h).2]; simp)
    (fun (a : ByteArray × Nat) (e : Nat × Nat × UInt64 × Nat × Nat) =>
      (a.1 ++ Kernel.Coc.packRes (2 ^ lg) e.2.2.2.2 fun j => (if (decide (a.2 * 2 ^ lg + j < n) &&
        !Kernel.Coc.outside e.2.2.2.1 e.2.2.2.2 (Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64, a.2 + 1))
    (fun m (e : Nat × Nat × UInt64 × Nat × Nat) j =>
      (if (decide (m * 2 ^ lg + j < n) && !Kernel.Coc.outside e.2.2.2.1 e.2.2.2.2
        (Kernel.Coc.keyAt w x (m * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64)
    (fun a m e => rfl)
  beta_reduce at hQ
  generalize (Array.foldl _ (ByteArray.empty, 0) bs).1 = pack at hQ ⊢
  have he : Column.blockStart M (Column.nblk M) = pack.size := hQ.1.symm
  -- element `i`'s block
  obtain ⟨hmf, hf64, hd64, ⟨j0, h0a, h0b, h0c, h0k⟩, -⟩ :=
    hpb (i / 2 ^ lg) (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hi)
  have h2 : Column.baseAt M (i / 2 ^ lg) = Kernel.Coc.unbias w (blk (i / 2 ^ lg)).1 := by
    rw [(hMb _ hib).1]; simp [hbget _ hib]
  have h3 : Column.widthAt M (i / 2 ^ lg) = (blk (i / 2 ^ lg)).2.2.2.2 := by
    rw [(hMb _ hib).2]; simp [hbget _ hib]
  generalize htail : (if exc.size = 0 then ByteArray.empty else _) = tail
  cases hk : Kernel.Coc.outside (blk (i / 2 ^ lg)).2.2.2.1 (blk (i / 2 ^ lg)).2.2.2.2 (Kernel.Coc.keyAt w x i)
  · -- kept: base, frame and residual
    have hnot : i ∉ exc.toList := fun h => by rw [hmem, hk] at h; exact Bool.false_ne_true h.2
    have hx : Column.foRExc M (pack ++ tail) i = none ∧
        Column.foRFrame M (pack ++ tail) (i / 2 ^ lg) = ((blk (i / 2 ^ lg)).2.2.2.1 - (blk (i / 2 ^ lg)).1).toUInt64 := by
      split at htail
      · next h0 =>
        subst htail
        have hj0 : j0 / 2 ^ lg = i / 2 ^ lg := Nat.div_eq_of_lt_le h0a (by rw [Nat.succ_mul]; exact h0b)
        have hk0 : Kernel.Coc.outside (blk (i / 2 ^ lg)).2.2.2.1 (blk (i / 2 ^ lg)).2.2.2.2 (blk (i / 2 ^ lg)).1 = false := by
          cases ho : Kernel.Coc.outside (blk (i / 2 ^ lg)).2.2.2.1 (blk (i / 2 ^ lg)).2.2.2.2 (blk (i / 2 ^ lg)).1
          · rfl
          · have := (hmem j0).2 ⟨h0c, by rw [hj0, h0k, ho]⟩
            rw [hnil h0] at this; cases this
        simp only [Kernel.Coc.outside, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hk0
        rw [show (blk (i / 2 ^ lg)).2.2.2.1 = (blk (i / 2 ^ lg)).1 by omega, Nat.sub_self]
        constructor
        · unfold Column.foRExc; simp [he]
        · unfold Column.foRFrame; simp [he]
      · next h0 =>
        subst htail
        rw [← hnb]
        refine ⟨?_, ?_⟩
        · rw [foRExc_excBlob M pack (2 ^ lg) hBM ⟨hBp, hB16⟩ w hw0 hw x exc hexs (h32' h0) _ _ (hword frm).1 he i
            (hnb ▸ hib), if_neg hnot]
        · rw [foRFrame_excBlob M pack (2 ^ lg) ⟨hBp, hB16⟩ w hw x exc (h32' h0) _ _ (hword frm).1 he fs hfsz
            (fun h => if_pos ((hword frm).2.1 h)) _ (hnb ▸ hib)]
          cases frm
          · rw [if_neg (fun h => Bool.false_ne_true ((hword false).2.1 h)), hfr0 rfl _ hib]
          · rw [if_pos ((hword true).2.2 rfl), hfs _ hib]; rfl
    obtain ⟨hx, hfr⟩ := hx
    rw [foRBits_of M (pack ++ tail) i (2 ^ lg) hBM _ _ (blk (i / 2 ^ lg)).2.2.2.2 (fun j =>
      (if (decide (i / 2 ^ lg * 2 ^ lg + j < n) && !Kernel.Coc.outside
        (blk (i / 2 ^ lg)).2.2.2.1 (blk (i / 2 ^ lg)).2.2.2.2 (Kernel.Coc.keyAt w x (i / 2 ^ lg * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (i / 2 ^ lg * 2 ^ lg + j) - (blk (i / 2 ^ lg)).2.2.2.1 else 0).toUInt64)
      (by omega) hd64 h2 h3 ?h4 hx hfr]
    · rw [Nat.div_add_mod']
      have hkf := hk
      simp only [Kernel.Coc.outside, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hkf
      have hkl := keyAt_lt w hw x i
      rw [if_pos (by simp [hi, hk]), Nat.toUInt64_eq, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (show Kernel.Coc.keyAt w x i - (blk (i / 2 ^ lg)).2.2.2.1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show Kernel.Coc.keyAt w x i - (blk (i / 2 ^ lg)).2.2.2.1 < 2 ^ (blk (i / 2 ^ lg)).2.2.2.2
          by omega), ← Nat.toUInt64_eq, unbias_add _ _ _ hmf, unbias_add _ _ _ (by omega)]
    case h4 =>
      intro k hk
      have hq := hQ.2 (i / 2 ^ lg) hib k (by rw [packRes_size, hbget _ hib]; exact hk)
      rw [hbget _ hib] at hq
      rw [getElem?_pos _ k (by rw [packRes_size]; exact hk)] at hq ⊢
      exact ba_append_of _ _ _ _ hq
  · -- patched: its own bits
    have hin : i ∈ exc.toList := (hmem i).2 ⟨hi, hk⟩
    have h0 : exc.size ≠ 0 := fun h => by rw [hnil h] at hin; cases hin
    rw [if_neg h0] at htail; subst htail
    rw [← hnb]
    unfold Column.foRBits
    rw [foRExc_excBlob M pack (2 ^ lg) hBM ⟨hBp, hB16⟩ w hw0 hw x exc hexs (h32' h0) _ _ (hword frm).1 he i
      (hnb ▸ hib), if_pos hin]

/-- **The Frame-of-Reference round trip, element by element**, over `foRBits` and the dense bits: element `i` of
the encoded `x` agrees with `x`'s on the low `8 * w` bits. -/
theorem foRBits_encode_bits (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw1 : 1 < w) (hw : w ≤ 8) (x : ByteArray)
    {patch : Bool} (i : Nat) (hi : i < x.size / w) :
    (Column.foRBits (Kernel.Coc.encodeAt lg w.toUSize x patch).1 (Kernel.Coc.encodeAt lg w.toUSize x patch).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg w.toUSize x patch).1) i).toNat % 2 ^ (8 * w) =
      (Column.bitsAt x (i * w) w).toNat := by
  rw [foRBits_encode lg hlg w (by omega) hw x i hi, unbias_keyAt w (by omega) hw]

/-- At a whole-byte lane `8c`, `Column.resAt` at element `j` is the `c` bytes from `c·j`, as
`Column.bitsAt` reads them: each byte's term is that byte shifted into place, nothing cut off. -/
theorem resAt_lane (P : ByteArray) (c j : Nat) (hc : c ≤ 8) :
    Column.resAt P 0 (8 * c) j = Column.bitsAt P (c * j) c := by
  have hm : j * (8 * c) = 8 * (c * j) := by rw [Nat.mul_left_comm, Nat.mul_comm j c]
  unfold Column.resAt
  generalize hq : c * j = q
  rw [hm, hq, show (8 * q + 8 * c + 7) / 8 - 8 * q / 8 = c by omega, show 8 * q / 8 = q by omega]
  suffices h : ∀ t ≤ c, (List.range' q t).foldl (fun acc k =>
      acc ||| ((P[0 + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (8 * q) % 2 ^ (8 * c)).toUInt64) 0 =
      Column.bitsAt P q t from h c (Nat.le_refl c)
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range'_concat, List.foldl_append, ih (by omega), Column.bitsAt_succ]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    congr 1
    generalize (P[q + t]?.getD 0) = b
    have hb := b.toNat_lt
    rw [show 8 * (q + t) = 8 * q + 8 * t by omega, Nat.pow_add, ← Nat.mul_assoc,
      Nat.mul_comm b.toNat, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    have h1 : b.toNat * 2 ^ (8 * t) < 2 ^ (8 * c) :=
      Nat.lt_of_lt_of_le (by rw [show 8 * (t + 1) = 8 + 8 * t by omega, Nat.pow_add]; exact
        Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ (8 * (t + 1)) ≤ 2 ^ (8 * c))
    rw [Nat.mod_eq_of_lt h1, ← UInt64.toNat_inj]
    have h64 : 2 ^ (8 * c) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.shiftLeft_eq, show 8 * t % 64 = 8 * t by omega, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 h64)]

/-- `Nat.fold` of a step that ignores the bound is the `List.foldl` over `List.range`. -/
theorem fold_eq_foldl_range {α : Type} (n : Nat) (g : Nat → α → α) (a : α) :
    Nat.fold n (fun i _ acc => g i acc) a = (List.range n).foldl (fun acc i => g i acc) a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.fold_succ, ih, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **`idAt` inverts `packIds` at a whole-byte lane** `8c`, for an id the lane holds. -/
theorem idAt_packIds_lane (c n : Nat) (f : Nat → Nat) (hc : 1 ≤ c) (hc8 : c ≤ 8) {i : Nat} (hi : i < n)
    (hf : f i < 2 ^ (8 * c)) : Column.idAt (Column.packIds (8 * c) n f) (8 * c) i = f i := by
  unfold Column.idAt Column.packIds
  rw [if_pos (by omega : 8 ≤ 8 * c), show 8 * c / 8 = c by omega,
    fold_eq_foldl_range (g := fun i acc => Column.pushBits acc (f i).toUInt64 c), resAt_lane _ _ _ hc8]
  have := (foldl_pushBits (fun i => (f i).toUInt64) c hc8 (List.range n)
    (ByteArray.emptyWithCapacity (n * c))).2.2 i (by simpa using hi)
  have he : (ByteArray.emptyWithCapacity (n * c)).size = 0 := rfl
  simp only [List.getElem_range, he, Nat.zero_add] at this
  rw [this]
  have hf64 := Nat.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ (8 * c) ≤ 2 ^ 64)
  simp [Nat.mod_eq_of_lt hf64, Nat.mod_eq_of_lt hf]

/-- A fold that pushes one byte per element lays those bytes after the seed's, in order. -/
theorem foldl_push_data (B : Nat → UInt8) : ∀ (l : List Nat) (a : ByteArray),
    (l.foldl (fun acc k => acc.push (B k)) a).data.toList = a.data.toList ++ l.map B
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_push_data B l]
    simp only [ByteArray.push, Array.toList_push, List.map_cons, List.append_assoc, List.singleton_append]

/-- At a sub-byte lane `w` of `per = 8 / w` fields to a byte, `Column.resAt` at field `r` of byte `q` is
that byte's bits `[r·w, r·w + w)`: the residual's one-byte range is exactly byte `q`. -/
theorem resAt_sub (B : Nat → UInt8) (M w per q r : Nat)
    (hw : w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) (hr : r < per) (hq : q < M) :
    (Column.resAt (Nat.fold M (fun k _ acc => acc.push (B k)) (ByteArray.emptyWithCapacity M)) 0 w
      (q * per + r)).toNat = (B q).toNat / 2 ^ (r * w) % 2 ^ w := by
  rw [show Nat.fold M (fun k _ acc => acc.push (B k)) (ByteArray.emptyWithCapacity M) =
    (List.range M).foldl (fun acc k => acc.push (B k)) (ByteArray.emptyWithCapacity M) from fold_eq_foldl_range M _ _]
  have hd := foldl_push_data B (List.range M) (ByteArray.emptyWithCapacity M)
  generalize (List.range M).foldl (fun acc k => acc.push (B k)) (ByteArray.emptyWithCapacity M) = P at hd
  have h3 : (q * per + r) * w = 8 * q + r * w := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hw1 : 1 ≤ w := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hrw : r * w + w ≤ 8 := by rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have h1 : (q * per + r) * w / 8 = q := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  have h2 : ((q * per + r) * w + w + 7) / 8 = q + 1 := Nat.div_eq_of_lt_le (by rw [h3]; omega) (by rw [h3]; omega)
  have hget : P[0 + q]? = some (B q) := by
    have he : (ByteArray.emptyWithCapacity M).data.toList = [] := rfl
    rw [he, List.nil_append] at hd
    have hs : P.size = M := by rw [ByteArray.size, ← Array.length_toList, hd, List.length_map, List.length_range]
    rw [Nat.zero_add, getElem?_pos P _ (by omega), ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
    simp only [hd, List.getElem_map, List.getElem_range]
  unfold Column.resAt
  rw [h2, h1, Nat.add_sub_cancel_left, List.range'_one]
  simp only [List.foldl_cons, List.foldl_nil, hget, Option.getD_some]
  rw [h3, Nat.pow_add, Nat.mul_comm, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
  have hlt : (B q).toNat / 2 ^ (r * w) % 2 ^ w < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [UInt64.zero_or, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- Field `j` of a byte ORed from `per` fields `u j` of `w` bits each, field `j` at bit `j·w`, is `u j`.
By `decide` over every field value: `per` fields of `w` bits are 256 bytes at each width. -/
theorem byte_field (w per : Nat) (hw : w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) (u : Nat → Nat)
    (hu : ∀ j < per, u j < 2 ^ w) {j : Nat} (hj : j < per) :
    (Nat.fold per (fun j _ b => b ||| (u j).toUInt8 <<< (j * w).toUInt8) (0 : UInt8)).toNat / 2 ^ (j * w) %
      2 ^ w = u j := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h0 := List.mem_range.2 (hu 0 (by decide)); have h1 := List.mem_range.2 (hu 1 (by decide)); have h2 := List.mem_range.2 (hu 2 (by decide))
    have h3 := List.mem_range.2 (hu 3 (by decide)); have h4 := List.mem_range.2 (hu 4 (by decide)); have h5 := List.mem_range.2 (hu 5 (by decide))
    have h6 := List.mem_range.2 (hu 6 (by decide)); have h7 := List.mem_range.2 (hu 7 (by decide))
    simp only [Nat.fold_succ, Nat.fold_zero, Nat.reduceMul]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    all_goals
      generalize u 0 = a0 at *; generalize u 1 = a1 at *; generalize u 2 = a2 at *; generalize u 3 = a3 at *
      generalize u 4 = a4 at *; generalize u 5 = a5 at *; generalize u 6 = a6 at *; generalize u 7 = a7 at *
      revert a7 h7; revert a6 h6; revert a5 h5; revert a4 h4; revert a3 h3; revert a2 h2; revert a1 h1; revert a0 h0
      decide +kernel
  · have h0 := List.mem_range.2 (hu 0 (by decide)); have h1 := List.mem_range.2 (hu 1 (by decide)); have h2 := List.mem_range.2 (hu 2 (by decide))
    have h3 := List.mem_range.2 (hu 3 (by decide))
    simp only [Nat.fold_succ, Nat.fold_zero, Nat.reduceMul]
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    all_goals
      generalize u 0 = a0 at *; generalize u 1 = a1 at *; generalize u 2 = a2 at *; generalize u 3 = a3 at *
      revert a3 h3; revert a2 h2; revert a1 h1; revert a0 h0
      decide +kernel
  · have h0 := List.mem_range.2 (hu 0 (by decide)); have h1 := List.mem_range.2 (hu 1 (by decide))
    simp only [Nat.fold_succ, Nat.fold_zero, Nat.reduceMul]
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals
      generalize u 0 = a0 at *; generalize u 1 = a1 at *
      revert a1 h1; revert a0 h0
      decide +kernel

/-- `packIds`' guard on the last byte's tail fields, moved inside the shift so `byte_field` applies. -/
theorem ite_shift (c : Prop) [Decidable c] (a : Nat) (s : UInt8) :
    (if c then a.toUInt8 <<< s else 0) = (if c then a else 0).toUInt8 <<< s := by
  split <;> simp

/-- **`idAt` inverts `packIds` at a sub-byte lane** 1, 2 or 4, for an id the lane holds. -/
theorem idAt_packIds_sub {w n i : Nat} {f : Nat → Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (hi : i < n) (hf : f i < 2 ^ w) : Column.idAt (Column.packIds w n f) w i = f i := by
  simp only [Column.idAt, Column.packIds, if_neg (show ¬ 8 ≤ w by omega), if_neg (show w ≠ 0 by omega), ite_shift]
  obtain ⟨per, hper, hwp⟩ : ∃ per, 8 / w = per ∧ (w = 1 ∧ per = 8 ∨ w = 2 ∧ per = 4 ∨ w = 4 ∧ per = 2) := by
    rcases hw with rfl | rfl | rfl <;> exact ⟨_, rfl, by decide⟩
  rw [hper]
  have hp : 0 < per := by rcases hwp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < per ∧ i = q * per + r := ⟨i / per, i % per, Nat.mod_lt _ hp, (Nat.div_add_mod' _ _).symm⟩
  have hq : q < (n + per - 1) / per :=
    (Nat.le_div_iff_mul_le hp).2 (by rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega)
  rw [resAt_sub _ _ w per q r hwp hr hq,
    byte_field w per hwp _ (fun j _ => by split <;> first | exact Nat.mod_lt _ (Nat.two_pow_pos _) | exact Nat.two_pow_pos _) hr,
    if_pos hi, Nat.mod_eq_of_lt hf]

/-- **`idAt` inverts `packIds`** at every lane width `Column.laneWidth` answers: `0`, the sub-byte
lanes and every whole-byte lane, which is what `groupIds_spec`'s ids are read at by `overGroups_spec`
and `groupSizes`. -/
theorem idAt_packIds {w n i : Nat} {f : Nat → Nat}
    (hw : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hi : i < n) (hf : f i < 2 ^ w) : Column.idAt (Column.packIds w n f) w i = f i := by
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show f i = 0 by simpa using hf]; simp [Column.idAt, Column.resAt]
  · exact idAt_packIds_sub (by decide) hi hf
  · exact idAt_packIds_sub (by decide) hi hf
  · exact idAt_packIds_sub (by decide) hi hf
  · exact idAt_packIds_lane 1 n f (by decide) (by decide) hi hf
  · exact idAt_packIds_lane 2 n f (by decide) (by decide) hi hf
  · exact idAt_packIds_lane 4 n f (by decide) (by decide) hi hf
  · exact idAt_packIds_lane 8 n f (by decide) (by decide) hi hf

end Rel.Verify

/-- info: 'Rel.Verify.idAt_packIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.idAt_packIds
