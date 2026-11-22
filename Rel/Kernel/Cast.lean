import Rel.Kernel.Dep.Val

/-! # The cast `$` between number atoms (typed base S6, owner ruling J)

`x $ F` replaces each value of `x` by the same NUMBER read at `F`'s atom. A number atom's values are a set of
dyadic rationals `m·2^e`, fixed by its format (`NumFmt`): an integer atom by its bits and sign, a float atom by its
exponent and fraction bits. `embed s t` is the partial function on those values: the word of `t` holding exactly the
value of the word of `s`, none where `t` holds no such word. It never rounds.

Which pairs `$` admits (`castOK`) is read off the two formats, not listed: `s → t` where every value of `s` is a value
of `t` (`NumFmt.exact`), and integer → float in every case, where `embed` is then partial (`i64 → f64` has no image at
`2^53 + 1`). A float → integer or a wide → narrow pair is refused where the program is elaborated. An ordered atom
that is no number atom (`date`, `datetime`, `char`) holds the number its stored word counts (`storeFmt?`, its
`ordNum`'s format: `date` the days since 1970-01-01), so it casts to and from the number atoms by that count; two
such atoms count in different units, so none casts to another. -/

namespace Rel.QAtomicType
open Rel.Dep

/-- A number atom's format: an integer of `bits` bits, signed or not; an IEEE float of `ebits` exponent and `fbits`
    fraction bits. -/
inductive NumFmt
  | int (signed : Bool) (bits : Nat)
  | float (ebits fbits : Nat)
  deriving DecidableEq, Repr

/-- The format of a number atom, an integer's bits read off its width; none at an atom that holds no number
    (`u1 char sym date datetime general`). -/
def numFmt? (t : QAtomicType) : Option NumFmt :=
  match t, t.width with
  | .u8, some w => some (.int false (8 * w))
  | .i8, some w | .i16, some w | .i32, some w | .i64, some w => some (.int true (8 * w))
  | .f32, _ => some (.float 8 23)
  | .f64, _ => some (.float 11 52)
  | _, _ => none

/-- The number atom an ordered atom is stored as and ordered by: a number atom itself, `char` as `u8`, `date` as `i32`
    (days), `datetime` as `i64` (nanoseconds); none at an atom with no order (`u1 sym general`). Order needs no
    arithmetic, so it is read off the storage and not off `numFmt?`, which keeps `$` off `date`. -/
def ordNum (t : QAtomicType) : Option QAtomicType :=
  match t with
  | .char => some .u8
  | .date => some .i32
  | .datetime => some .i64
  | t => if t.numFmt?.isSome then some t else none

/-- The format of the number an ordered atom's word holds: its `ordNum`'s (`date` an `i32` day count). -/
def storeFmt? (t : QAtomicType) : Option NumFmt := t.ordNum.bind numFmt?

/-- `t` is stored as an integer (`storeFmt?`): canon's order on its words is the integer order of their values, the
    order `sums` reads its positions in (`Lang.ordAt_int`); a float's is its bits' until PLAN S5. -/
def intOrd (t : QAtomicType) : Bool := t.storeFmt?.any (· matches .int ..)

/-- The least and the greatest integer of an integer format; a signed one's least word is q's null, no value. -/
def NumFmt.lo : NumFmt → Int
  | .int true b => 1 - 2 ^ (b - 1)
  | _ => 0
def NumFmt.hi : NumFmt → Int
  | .int true b => 2 ^ (b - 1) - 1
  | .int false b => 2 ^ b - 1
  | .float .. => 0

/-- Every value of `f` is a value of `g`: an integer range inside the other, an integer range inside `±2^(p)` of a
    float of `p - 1` fraction bits, a float's exponent and fraction bits each at most the other's. -/
def NumFmt.exact : NumFmt → NumFmt → Bool
  | f@(.int ..), g@(.int ..) => g.lo ≤ f.lo && f.hi ≤ g.hi
  | f@(.int ..), .float _ p => -2 ^ (p + 1) ≤ f.lo && f.hi ≤ 2 ^ (p + 1)
  | .float e p, .float e' p' => e ≤ e' && p ≤ p'
  | .float .., .int .. => false

private theorem two_pow_le_add_one {x y : Nat} (hy : 1 ≤ y) : 2 ^ x ≤ 2 ^ y + 1 ↔ x ≤ y := by
  constructor
  · intro h; apply Decidable.byContradiction; intro hxy
    have : 2 ^ (y + 1) ≤ 2 ^ x := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ≤ 2 ^ y := by simpa using Nat.pow_le_pow_right (n := 2) (by decide) hy
    rw [Nat.pow_succ] at *; omega
  · intro h; have := Nat.pow_le_pow_right (n := 2) (by decide) h; omega

private theorem two_pow_le_one {x : Nat} : 2 ^ x ≤ 1 ↔ x = 0 := by
  constructor
  · intro h; apply Decidable.byContradiction; intro hx
    have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.one_le_iff_ne_zero.2 hx); simp at this; omega
  · intro h; simp [h]

/-- What `exact` runs as: the bounds compared by their exponents. `lo`, `hi` of a 64-bit format are `∓2^63`, past
`Int`'s small values (`±2^31`), so comparing them builds GMP numbers. -/
private def NumFmt.exactImpl : NumFmt → NumFmt → Bool
  | .int s b, .int s' b' =>
    (if s' then !s || b - 1 ≤ b' - 1 else !s || b ≤ 1) &&
    (match s, s' with | true, true => b - 1 ≤ b' - 1 | true, false => b - 1 ≤ b' | false, true => b ≤ b' - 1
                      | false, false => b ≤ b')
  | .int s b, .float _ p => if s then b - 1 ≤ p + 1 else b ≤ p + 1
  | .float e p, .float e' p' => e ≤ e' && p ≤ p'
  | .float .., .int .. => false

@[csimp] private theorem NumFmt.exact_eq_impl : @NumFmt.exact = @NumFmt.exactImpl := by
  funext f g
  have P (x y : Nat) : ((2 : Int) ^ x ≤ 2 ^ y) ↔ x ≤ y := by
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow, ← Int.natCast_pow, Int.ofNat_le]
    exact Nat.pow_le_pow_iff_right (by decide)
  have Q (x p : Nat) : ((2 : Int) ^ x ≤ 2 ^ (p + 1) + 1) ↔ x ≤ p + 1 := by
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow, ← Int.natCast_pow]
    rw [← two_pow_le_add_one (Nat.le_add_left 1 p)]; omega
  have R (x : Nat) : ((2 : Int) ^ x ≤ 1) ↔ x = 0 := by
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow, ← two_pow_le_one]; omega
  have W (x : Nat) : (1 : Int) ≤ 2 ^ x := by simpa using (P 0 x).2 (Nat.zero_le _)
  cases f with
  | int s b => cases g with
    | int s' b' =>
      have := P (b - 1) (b' - 1); have := P (b - 1) b'; have := P b (b' - 1); have := P b b'; have := R (b - 1)
      have := W (b - 1); have := W (b' - 1); have := W b; have := W b'
      cases s <;> cases s' <;>
        (simp only [NumFmt.exact, NumFmt.exactImpl, NumFmt.lo, NumFmt.hi]; rw [Bool.eq_iff_iff]; try simp) <;> omega
    | float e p =>
      have := Q (b - 1) p; have := Q b p; have := W (b - 1); have := W b; have := W (p + 1)
      cases s <;>
        (simp only [NumFmt.exact, NumFmt.exactImpl, NumFmt.lo, NumFmt.hi]; rw [Bool.eq_iff_iff]; try simp) <;> omega
  | float e p => cases g <;> simp [NumFmt.exact, NumFmt.exactImpl]

/-- `$` admits `s → t`: both hold a number (`storeFmt?`), at most one counts in a unit of its own (no number atom:
    `date` days, `datetime` its stored unit), and every value of `s` exact at `t`, or an integer to a float. -/
def castOK (s t : QAtomicType) : Bool :=
  (s == t || s.numFmt?.isSome || t.numFmt?.isSome) &&
  match s.storeFmt?, t.storeFmt? with
  | some (.int ..), some (.float ..) => true
  | some f, some g => f.exact g
  | _, _ => false

/-- The integer a word of a number atom holds as written: an integer atom's value, a float atom's bits. -/
def num : (t : QAtomicType) → Carrier t → Int
  | .u8, x => x.toNat
  | .i8, x => x.toInt
  | .i16, x => x.toInt
  | .i32, x => x.toInt
  | .i64, x => x.toInt
  | .f32, x => x.toNat
  | .f64, x => x.toNat
  | .char, x => x.toNat
  | .date, x => x.toInt
  | .datetime, x => x.toInt
  | _, _ => 0

/-- The word of `t` holding the integer `k` (`num`'s inverse on `t`'s range). -/
def ofNum : (t : QAtomicType) → Int → Carrier t
  | .u8, k => UInt8.ofNat k.toNat
  | .i8, k => Int8.ofInt k
  | .i16, k => Int16.ofInt k
  | .i32, k => Int32.ofInt k
  | .i64, k => Int64.ofInt k
  | .f32, k => UInt32.ofNat k.toNat
  | .f64, k => UInt64.ofNat k.toNat
  | .char, k => UInt8.ofNat k.toNat
  | .date, k => Int32.ofInt k
  | .datetime, k => Int64.ofInt k
  | .u1, _ => default
  | .sym, _ => default
  | .general, _ => default

/-- The value `m·2^e` of the float bits `b`: none at an infinity or a NaN (q's float null). -/
def floatValue (E F b : Nat) : Option (Int × Int) :=
  let ex := b / 2 ^ F % 2 ^ E
  let fr := b % 2 ^ F
  let bias : Int := 2 ^ (E - 1) - 1
  if ex = 2 ^ E - 1 then none else
  let m : Int := if ex = 0 then fr else fr + 2 ^ F
  let e : Int := if ex = 0 then 1 - bias - F else ex - bias - F
  some (if b / 2 ^ (E + F) % 2 = 1 then -m else m, e)

/-- The float bits holding exactly `m·2^e`, `0` the one zero: none past the greatest finite value or where `m·2^e` needs
    more fraction bits than `F` (a normal value) or a bit below the least subnormal one. -/
def floatBits (E F : Nat) (v : Int × Int) : Option Nat :=
  if v.1 = 0 then some 0 else
  let a := v.1.natAbs
  let L := a.log2
  let bias : Int := 2 ^ (E - 1) - 1
  let X := v.2 + L
  let sgn := if v.1 < 0 then 2 ^ (E + F) else 0
  if bias < X then none
  else if 1 - bias ≤ X then
    -- the significand `a·2^(F-L)` lies in `[2^F, 2^(F+1))`: its top bit is the hidden one, the rest the fraction field
    if a % 2 ^ (L - F) = 0 then some (sgn + (X + bias).toNat * 2 ^ F + a / 2 ^ (L - F) * 2 ^ (F - L) % 2 ^ F)
    else none
  else
    let low := 1 - bias - F
    let fr := a / 2 ^ (low - v.2).toNat * 2 ^ (v.2 - low).toNat
    -- a subnormal's whole significand is its fraction field, of `F` bits
    if a % 2 ^ (low - v.2).toNat = 0 ∧ fr < 2 ^ F then some (sgn + fr) else none

/-- The integer `m·2^e`, none where it is not one. -/
def intOf (v : Int × Int) : Option Int :=
  if 0 ≤ v.2 then some (v.1 * 2 ^ v.2.toNat)
  else if v.1 % 2 ^ (-v.2).toNat = 0 then some (v.1 / 2 ^ (-v.2).toNat) else none

/-- The value `m·2^e` of a word of `t`: none at an atom holding no number, at q's integer null, at a float's infinity
    or NaN. -/
def value (t : QAtomicType) (x : Carrier t) : Option (Int × Int) :=
  match t.storeFmt? with
  | some f@(.int ..) => if f.lo ≤ t.num x then some (t.num x, 0) else none
  | some (.float E F) => floatValue E F (t.num x).toNat
  | none => none

/-- The word of `t` holding exactly the value `v`, none where `t` holds no such word. -/
def ofValue (t : QAtomicType) (v : Int × Int) : Option (Carrier t) :=
  match t.storeFmt? with
  | some f@(.int ..) => (intOf v).bind fun k => if f.lo ≤ k ∧ k ≤ f.hi then some (t.ofNum k) else none
  | some (.float E F) => (floatBits E F v).map fun b => t.ofNum b
  | none => none

/-- **The embedding of `s` in `t`**: the word of `t` holding the value of `x`, none where there is none. -/
def embed (s t : QAtomicType) (x : Carrier s) : Option (Carrier t) := (value s x).bind (ofValue t)

/-- The stored word of `x`, as a column holds it (`num`, two's complement past the sign). -/
def word (t : QAtomicType) (x : Carrier t) : UInt64 := UInt64.ofInt (t.num x)

/-- A word as a column holds it, read at `t`: its low `8·w` bits, as `Column.atomOfBits` reads them. -/
def ofBits : (t : QAtomicType) → UInt64 → Carrier t
  | .u1, v => v != 0
  | .u8, v => v.toUInt8
  | .char, v => v.toUInt8
  | .i16, v => v.toUInt16.toInt16
  | .i32, v => v.toUInt32.toInt32
  | .date, v => v.toUInt32.toInt32
  | .i8, v => v.toUInt8.toInt8
  | .i64, v => v.toInt64
  | .datetime, v => v.toInt64
  | .f32, v => v.toUInt32
  | .f64, v => v
  | .sym, v => v
  | .general, _ => default

/-- **`embed` on stored words**, the body of `Op.cast s t`: the word of `t` holding the value of the word `x` read at
    `s`, and `2^63` where there is none, which no image is (`word_ne_nul`), so the row is told by that word alone. -/
def castWord (s t : QAtomicType) (x : UInt64) : UInt64 :=
  ((embed s t (ofBits s x)).map (word t)).getD 0x8000000000000000

/-- **An ordered atom's words widen by its value**: two words holding one value of `t` widen through `t`'s
    `ordNum` to one `i64` word, so an order read on the widened words (`iordAt`) is one of the values. -/
theorem castWord_ofBits {t r : QAtomicType} (hr : t.ordNum = some r) {x y : UInt64} (h : ofBits t x = ofBits t y) :
    castWord r .i64 x = castWord r .i64 y := by
  cases t <;> simp (config := {decide := true}) only [ordNum, numFmt?, width, Option.isSome, reduceCtorEq,
    Option.some.injEq, ite_true, ite_false] at hr <;> subst hr <;>
    exact congrArg (fun v => ((embed _ .i64 v).map (word .i64)).getD 0x8000000000000000) h

/-- The fields of `floatBits`' word: sign `sg`, exponent `ex` (never all ones), fraction `fr`; a negative word is no
    zero. -/
theorem floatBits_some {E F : Nat} {v : Int × Int} {b : Nat} (h : floatBits E F v = some b) :
    ∃ sg ex fr, b = sg * 2 ^ (E + F) + ex * 2 ^ F + fr ∧ sg < 2 ∧ ((ex : Int) ≤ 2 * (2 ^ (E - 1) - 1) ∨ ex = 0) ∧
      fr < 2 ^ F ∧ (sg = 1 → 0 < ex ∨ 0 < fr) := by
  unfold floatBits at h
  dsimp only at h
  have hsg : ∀ c : Prop, [Decidable c] → ∃ sg, (if c then 2 ^ (E + F) else 0) = sg * 2 ^ (E + F) ∧ sg < 2 ∧
      (sg = 1 → c) := fun c _ => by
    by_cases hc : c
    · exact ⟨1, by simp [hc], by omega, fun _ => hc⟩
    · exact ⟨0, by simp [hc], by omega, by omega⟩
  split at h
  · cases h; exact ⟨0, 0, 0, by simp, by omega, .inr rfl, Nat.two_pow_pos F, by omega⟩
  rename_i h0
  split at h; · cases h
  split at h
  · split at h
    · cases h
      obtain ⟨sg, hs, hs2, -⟩ := hsg (v.1 < 0)
      exact ⟨sg, _, _, by rw [hs], hs2, .inl (by omega), Nat.mod_lt _ (Nat.two_pow_pos F), fun _ => .inl (by omega)⟩
    · cases h
  · split at h
    · rename_i hd
      cases h
      obtain ⟨sg, hs, hs2, -⟩ := hsg (v.1 < 0)
      have ha : 0 < v.1.natAbs := Int.natAbs_pos.2 h0
      have hk := Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero hd.1)
      exact ⟨sg, 0, _, by rw [hs]; simp, hs2, .inr rfl, hd.2,
        fun _ => .inr (Nat.mul_pos (Nat.div_pos hk (Nat.two_pow_pos _)) (Nat.two_pow_pos _))⟩
    · cases h

/-- **No image is the word `2^63`**: an integer image lies inside its atom's range, which leaves out `-2^63`, an `f32`
    one below `2^32`, an `f64` one is no negative zero (`floatBits_some`). -/
theorem word_ne_nul {s t : QAtomicType} {x : Carrier s} {y : Carrier t} (h : embed s t x = some y) :
    word t y ≠ 0x8000000000000000 := by
  obtain ⟨v, -, hv⟩ := Option.bind_eq_some_iff.1 h
  intro he
  have hn := congrArg UInt64.toNat he
  cases t <;> simp (config := {decide := true}) only [ofValue, storeFmt?, ordNum, numFmt?, QAtomicType.width,
    ite_true, ite_false, Option.bind_some, Option.bind_none, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, NumFmt.lo, NumFmt.hi, reduceCtorEq, Option.ite_none_right_eq_some] at hv
  case f32 =>
    obtain ⟨b, hb, rfl⟩ := hv
    cases hf : floatBits 8 23 v <;> simp [hf] at hb
    subst hb
    obtain ⟨sg, ex, fr, rfl, h1, h2, h3, h4⟩ := floatBits_some hf
    simp [word, num, ofNum, UInt64.ofInt, UInt64.toNat_ofNat'] at hn
    omega
  case f64 =>
    obtain ⟨b, hb, rfl⟩ := hv
    cases hf : floatBits 11 52 v <;> simp [hf] at hb
    subst hb
    obtain ⟨sg, ex, fr, rfl, h1, h2, h3, h4⟩ := floatBits_some hf
    simp [word, num, ofNum, UInt64.ofInt, UInt64.toNat_ofNat'] at hn
    omega
  case u8 | i8 | i16 | i32 | i64 | char | date | datetime =>
    obtain ⟨k, -, ⟨h1, h2⟩, hy⟩ := hv
    obtain rfl := Option.some.inj hy
    simp [word, num, ofNum, UInt64.ofInt, UInt64.toNat_ofNat', Int8.toInt_ofInt, Int16.toInt_ofInt,
      Int32.toInt_ofInt, Int64.toInt_ofInt, Int.bmod] at hn
    omega

/-- Equality of two words of an atom other than `general` (whose `QValue`s `$` never produces). -/
def decEq : (t : QAtomicType) → t ≠ .general → DecidableEq (Carrier t)
  | .u1, _ => inferInstanceAs (DecidableEq Bool)
  | .u8, _ | .char, _ => inferInstanceAs (DecidableEq UInt8)
  | .i8, _ => inferInstanceAs (DecidableEq Int8)
  | .i16, _ => inferInstanceAs (DecidableEq Int16)
  | .i32, _ | .date, _ => inferInstanceAs (DecidableEq Int32)
  | .i64, _ | .datetime, _ => inferInstanceAs (DecidableEq Int64)
  | .f32, _ => inferInstanceAs (DecidableEq UInt32)
  | .f64, _ => inferInstanceAs (DecidableEq UInt64)
  | .sym, _ => inferInstanceAs (DecidableEq UInt64)
  | .general, h => absurd rfl h

/-- **A word `$` produces at `t` is canonical** (`nonCanonical`, the one predicate): `floatBits`' exponent field is never
    all ones, so no NaN, and a word with the sign bit has a nonzero exponent or fraction, so no `-0`
    (`floatBits_some`). -/
theorem embed_canonical {s t : QAtomicType} {x : Carrier s} {y : Carrier t} (h : embed s t x = some y) :
    nonCanonical t (word t y) = false := by
  have hnul := word_ne_nul h
  obtain ⟨v, -, hv⟩ := Option.bind_eq_some_iff.1 h
  have k (x : Nat) (j : Nat) : x &&& (2 ^ j - 1) = x % 2 ^ j := Nat.and_two_pow_sub_one_eq_mod x j
  cases t <;> simp (config := {decide := true}) only [ofValue, storeFmt?, ordNum, numFmt?, QAtomicType.width,
    ite_true, ite_false, Option.bind_some, Option.bind_none, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, NumFmt.lo, NumFmt.hi, reduceCtorEq, Option.ite_none_right_eq_some] at hv
  case f32 =>
    obtain ⟨b, hb, rfl⟩ := hv
    cases hf : floatBits 8 23 v <;> simp [hf] at hb
    subst hb
    obtain ⟨sg, ex, fr, rfl, h1, h2, h3, h4⟩ := floatBits_some hf
    have hw : (word .f32 (ofNum .f32 (((sg * 2 ^ (8 + 23) + ex * 2 ^ 23 + fr : Nat)) : Int))).toUInt32.toNat =
        sg * 2 ^ 31 + ex * 2 ^ 23 + fr := by
      simp [word, num, ofNum, UInt64.ofInt]; omega
    simp only [nonCanonical, Bits.f32IsNaN, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      bne_eq_false_iff_eq, ne_eq]
    refine ⟨.inl fun hx => ?_, fun hx => ?_⟩
    · have := congrArg UInt32.toNat hx
      rw [UInt32.toNat_and, UInt32.toNat_shiftRight, hw, Nat.shiftRight_eq_div_pow] at this
      have := k ((sg * 2 ^ 31 + ex * 2 ^ 23 + fr) / 2 ^ (23 % 32)) 8
      simp at *
      omega
    · have := congrArg UInt32.toNat hx
      rw [hw] at this
      simp at this
      omega
  case f64 =>
    obtain ⟨b, hb, rfl⟩ := hv
    cases hf : floatBits 11 52 v <;> simp [hf] at hb
    subst hb
    obtain ⟨sg, ex, fr, rfl, h1, h2, h3, h4⟩ := floatBits_some hf
    have hw : (word .f64 (ofNum .f64 (((sg * 2 ^ (11 + 52) + ex * 2 ^ 52 + fr : Nat)) : Int))).toNat =
        sg * 2 ^ 63 + ex * 2 ^ 52 + fr := by
      simp [word, num, ofNum, UInt64.ofInt]; omega
    simp only [nonCanonical, Bits.f64IsNaN, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      bne_eq_false_iff_eq, ne_eq]
    refine ⟨.inl fun hx => ?_, by simpa using hnul⟩
    have := congrArg UInt64.toNat hx
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hw, Nat.shiftRight_eq_div_pow] at this
    have := k ((sg * 2 ^ 63 + ex * 2 ^ 52 + fr) / 2 ^ (52 % 64)) 11
    simp at *
    omega
  all_goals rfl

/-- **A number atom's stored word read back at its type is the atom** (`ofBits` after `word`). -/
theorem ofBits_word {t : QAtomicType} (y : Carrier t) (h : t.storeFmt?.isSome) : ofBits t (word t y) = y := by
  cases t <;> first | exact absurd h (by decide) | simp only [ofBits, word, num]
  case u8 | char => apply UInt8.toNat_inj.1; simp [UInt64.ofInt]; have := y.toNat_lt; omega
  case f32 => apply UInt32.toNat_inj.1; simp [UInt64.ofInt]; have := y.toNat_lt; omega
  case f64 => apply UInt64.toNat_inj.1; simp [UInt64.ofInt]; have := y.toNat_lt; omega
  case i8 =>
    apply Int8.toBitVec_inj.1; simp only [UInt64.ofInt, Int8.toInt]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toInt_eq_toNat_cond]; have := y.toBitVec.isLt; split <;> omega
  case i16 =>
    apply Int16.toBitVec_inj.1; simp only [UInt64.ofInt, Int16.toInt]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toInt_eq_toNat_cond]; have := y.toBitVec.isLt; split <;> omega
  case i32 | date =>
    apply Int32.toBitVec_inj.1; simp only [UInt64.ofInt, Int32.toInt]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toInt_eq_toNat_cond]; have := y.toBitVec.isLt; split <;> omega
  case i64 | datetime =>
    apply Int64.toBitVec_inj.1; simp only [UInt64.ofInt, Int64.toInt]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toInt_eq_toNat_cond]; have := y.toBitVec.isLt; split <;> omega

-- the pairs `$` admits: widenings and integer → float; no float → integer, no narrowing, no atom holding no number
#guard castOK .i32 .i64 && castOK .i64 .f64 && castOK .i32 .f64 && castOK .f32 .f64 && castOK .u8 .i16 &&
  castOK .i64 .f32 && castOK .i64 .i64
#guard !castOK .f64 .i64 && !castOK .i64 .i32 && !castOK .f64 .f32 && !castOK .i8 .u8 && !castOK .i64 .sym &&
  !castOK .i64 .char
-- a date or datetime casts by its count, by the same rule: `i64 → date` narrows (a date is an `i32` count); two
-- atoms counting in units of their own never meet
#guard castOK .date .i32 && castOK .date .i64 && castOK .datetime .i64 && castOK .i32 .date &&
  castOK .i64 .datetime && castOK .date .date
#guard !castOK .i64 .date && !castOK .datetime .i32 && !castOK .date .datetime && !castOK .datetime .date &&
  !castOK .char .date
example : embed .date .i64 (-5) = some (-5) := by decide
example : embed .date .i64 Int32.minValue = none := by decide
example : embed .i32 .date 19000 = some 19000 := by decide
-- `i32 → f64` is total, `i64 → f64` is not: the format rule says which
#guard (numFmt? .i32).bind (fun f => (numFmt? .f64).map f.exact) == some true
#guard (numFmt? .i64).bind (fun f => (numFmt? .f64).map f.exact) == some false

example : embed .i64 .f64 0 = some 0 := by decide
example : embed .i64 .f64 1 = some 0x3ff0000000000000 := by decide
example : embed .i64 .f64 (-1) = some 0xbff0000000000000 := by decide
example : embed .i64 .f64 3 = some 0x4008000000000000 := by decide
example : embed .i64 .f64 (-7) = some 0xc01c000000000000 := by decide
example : embed .i64 .f64 9007199254740992 = some 0x4340000000000000 := by decide
example : embed .i64 .f64 9007199254740993 = none := by decide
example : embed .i64 .f64 4611686018427387904 = some 0x43d0000000000000 := by decide
example : embed .i64 .f64 Int64.minValue = none := by decide
example : embed .i32 .i64 (-5) = some (-5) := by decide
example : embed .i32 .i64 Int32.minValue = none := by decide
example : embed .f32 .f64 0x3fc00000 = some 0x3ff8000000000000 := by decide
example : embed .f32 .f64 0x00000001 = some 0x36a0000000000000 := by decide
example : embed .f32 .f64 0x7f800000 = none := by decide

end Rel.QAtomicType
