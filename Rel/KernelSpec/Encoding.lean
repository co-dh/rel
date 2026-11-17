import Rel.Kernel.Coc
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Encoding` the Rel kernels reach; `Rel.Verify.Encoding` imports it. -/


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
    unfold Kernel.Coc.foRMeta
    simp only [← Array.foldl_toList, Column.nblk, ByteArray.size_append, s1, s2, s3, s4, s6, sT]; omega
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

theorem foRBits_of (M P : ByteArray) (i : Nat) (B : Nat) (hB : Column.blk M = B) (base : UInt64) (wd : Nat)
    (R : Nat → UInt64)
    (hb : i / B ≤ Column.nblk M) (hwd : wd ≤ 64) (h2 : Column.baseAt M (i / B) = base)
    (h3 : Column.widthAt M (i / B) = wd)
    (h4 : ∀ k < B * wd / 8, P[Column.blockStart M (i / B) + k]? = (Kernel.Coc.packRes B wd R)[k]?)
    (h5 : P.size ≤ Column.blockStart M (Column.nblk M)) :
    Column.foRBits M P (Column.blockStarts M) i = base + ((R (i % B)).toNat % 2 ^ wd).toUInt64 := by
  subst hB
  have hx : Column.foRExc M P i = none := by unfold Column.foRExc; simp [h5]
  have hf : Column.foRFrame M P (i / Column.blk M) = 0 := by unfold Column.foRFrame; simp [h5]
  unfold Column.foRBits
  rw [hx]
  simp only [hf, blockStarts_get M hb, h2, h3, UInt64.add_zero]
  rw [resAt_packRes (Column.blk M) wd (blk_dvd8 M) hwd R P _ h4 _ (Nat.mod_lt _ (blk_pos M))]

theorem unbias_add (w mn k : Nat) (h : mn ≤ k) :
    Kernel.Coc.unbias w mn + (k - mn).toUInt64 = Kernel.Coc.unbias w k := by
  unfold Kernel.Coc.unbias
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

/-- The encoder model reads back element by element, at any block size `2 ^ lg` the layout admits. -/
theorem foRBits_encode (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray)
    (i : Nat) (hi : i < x.size / w) :
    Column.foRBits (Kernel.Coc.encodeAt lg w.toUSize x).1 (Kernel.Coc.encodeAt lg w.toUSize x).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg w.toUSize x).1) i = Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i) := by
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  unfold Kernel.Coc.encodeAt
  simp only [hwt]
  generalize hn : x.size / w = n at *
  have hib : i / 2 ^ lg < (n + 2 ^ lg - 1) / 2 ^ lg := lt_cdiv hBp hi
  generalize hbs : Array.map (fun b => Kernel.Coc.blockOf (2 ^ lg) w n b x) (Array.range _) = bs
  have hbsz : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = Kernel.Coc.blockOf (2 ^ lg) w n b x := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hbw : ∀ b (h : b < bs.size), bs[b].2.2.2 ≤ 64 := by
    intro b h; rw [hbget]
    exact (blockOf_bounds (2 ^ lg) w n b hw x (b * 2 ^ lg) (Nat.le_refl _) (by omega)
      (mul_lt_of_lt_cdiv hBp (hbsz ▸ h))).2.2
  generalize hM : Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) n _ = M
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    (bs.map fun (mn, mx, s, wd) => (Kernel.Coc.unbias w mn, Kernel.Coc.unbias w mx, s, wd))
    (fun b h => by simp only [Array.getElem_map]; exact Nat.lt_of_le_of_lt (hbw b (by simpa using h)) (by decide))
  rw [hM] at hMr
  obtain ⟨hnb, hlgM, hMb⟩ := hMr
  -- the pair, not `by omega`: omega's proof of this `∧` goal depends on `Classical.choice`
  have hBM : Column.blk M = 2 ^ lg := by rw [blk_of_lgAt M ⟨hlgM ▸ hlg.1, hlgM ▸ hlg.2⟩, hlgM]
  simp only [Array.size_map] at hnb hMb
  have hblk : i / 2 ^ lg < bs.size := by omega
  have pack_steps : ∀ c (h : c < bs.toList.length), Column.blockStart M (c + 1) = Column.blockStart M c +
      (Kernel.Coc.packRes (2 ^ lg) bs.toList[c].2.2.2 fun j =>
        (if c * 2 ^ lg + j < n then Kernel.Coc.keyAt w x (c * 2 ^ lg + j) - bs.toList[c].1 else 0).toUInt64).size := by
    intro c h
    rw [packRes_size, blockStart_succ, hBM, (hMb c (by simpa using h)).2]
    simp
  obtain ⟨hmn, hres, hwd⟩ := blockOf_bounds (2 ^ lg) w n (i / 2 ^ lg) hw x i
    (Nat.div_mul_le_self _ _) (by have := Nat.mod_add_div' i (2 ^ lg); have := Nat.mod_lt i hBp; omega) hi
  rw [← hbget _ hblk] at hmn hres hwd
  rw [foRBits_of _ _ i (2 ^ lg) hBM (Kernel.Coc.unbias w bs[i / 2 ^ lg].1) bs[i / 2 ^ lg].2.2.2
    (fun j => (if i / 2 ^ lg * 2 ^ lg + j < n then
      Kernel.Coc.keyAt w x (i / 2 ^ lg * 2 ^ lg + j) - bs[i / 2 ^ lg].1
      else 0).toUInt64) (by omega) hwd ((hMb _ hblk).1.trans (by simp)) ((hMb _ hblk).2.trans (by simp)) ?h4 ?h5]
  · rw [Nat.div_add_mod', if_pos hi, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (show _ < 2 ^ 64 by have := keyAt_lt w hw x i; omega), Nat.mod_eq_of_lt hres,
      ← Nat.toUInt64_eq, unbias_add _ _ _ hmn]
  case h4 =>
    intro k hk
    rw [← Array.foldl_toList]
    refine ((pack_fold0 _ (fun m (e : Nat × Nat × UInt64 × Nat) => Kernel.Coc.packRes (2 ^ lg) e.2.2.2 fun j =>
        (if m * 2 ^ lg + j < n then Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.1 else 0).toUInt64)
      ?hf (Column.blockStart M) bs.toList rfl ?hs).2 (i / 2 ^ lg) (by simpa using hblk) k
      (by rw [packRes_size]; simpa using hk)).trans ?_
    case hf => intro a m ⟨mn, mx, s, wd⟩; rfl
    case hs => exact pack_steps
    simp only [Array.getElem_toList]
  case h5 =>
    rw [← Array.foldl_toList]
    refine Nat.le_of_eq (((pack_fold0 _ (fun m (e : Nat × Nat × UInt64 × Nat) => Kernel.Coc.packRes (2 ^ lg) e.2.2.2 fun j =>
        (if m * 2 ^ lg + j < n then Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.1 else 0).toUInt64)
      ?hf (Column.blockStart M) bs.toList rfl ?hs).1).trans ?_)
    case hf => intro a m ⟨mn, mx, s, wd⟩; rfl
    case hs => exact pack_steps
    simp [hnb]

theorem raw_foR (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .boolean)
    (n : USize) (M P : ByteArray) :
    Enc.raw t n (.foR M P) = (Array.range n.toNat).map (Column.foRBits M P (Column.blockStarts M)) := by
  cases t <;> simp_all [Enc.raw]

theorem raw_bytes (t : QAtomicType) (w : Nat) (ht : t.width = some w) (hb : t ≠ .boolean)
    (n : USize) (x : ByteArray) :
    Enc.raw t n (.bytes x) = (Array.range n.toNat).map fun i => Column.bitsAt x (i * w) w := by
  cases t <;> simp_all [Enc.raw]

theorem encode_bytes (t : QAtomicType) (w : Nat) (ht : t.width = some w) (he : Column.encodes t = true)
    (n : USize) (x : ByteArray) :
    Enc.encode t n (.bytes x) = .foR (Kernel.Coc.encode w.toUSize x).1 (Kernel.Coc.encode w.toUSize x).2 := by
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
the element's own `8 * w`, which below eight bytes is all it can. -/
theorem unbias_keyAt (w : Nat) (hw1 : 1 < w) (hw : w ≤ 8) (x : ByteArray) (i : Nat) :
    (Kernel.Coc.unbias w (Kernel.Coc.keyAt w x i)).toNat % 2 ^ (8 * w) = (Column.bitsAt x (i * w) w).toNat := by
  have hv := bitsAt_lt x (i * w) w hw
  unfold Kernel.Coc.unbias Kernel.Coc.keyAt Kernel.Coc.bias
  rw [if_neg (by omega)]
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

/-- **The Frame-of-Reference round trip, element by element**, over `foRBits` and the dense bits, so
without `Classical.choice`: element `i` of the encoded `x` agrees with `x`'s on the low `8 * w` bits. -/
theorem foRBits_encode_bits (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw1 : 1 < w) (hw : w ≤ 8) (x : ByteArray)
    (i : Nat) (hi : i < x.size / w) :
    (Column.foRBits (Kernel.Coc.encodeAt lg w.toUSize x).1 (Kernel.Coc.encodeAt lg w.toUSize x).2
      (Column.blockStarts (Kernel.Coc.encodeAt lg w.toUSize x).1) i).toNat % 2 ^ (8 * w) = (Column.bitsAt x (i * w) w).toNat := by
  rw [foRBits_encode lg hlg w (by omega) hw x i hi, unbias_keyAt w hw1 hw]

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
