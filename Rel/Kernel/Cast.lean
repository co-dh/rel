import Rel.Kernel.Dep.Val

/-! # The cast `$` between number atoms (typed base S6, owner ruling J)

`x $ F` replaces each value of `x` by the same NUMBER read at `F`'s atom. A number atom's values are a set of
dyadic rationals `m·2^e`, fixed by its format (`NumFmt`): an integer atom by its bits and sign, a float atom by its
exponent and fraction bits. `embed s t` is the partial function on those values: the word of `t` holding exactly the
value of the word of `s`, none where `t` holds no such word. It never rounds.

Which pairs `$` admits (`castOK`) is read off the two formats, not listed: `s → t` where every value of `s` is a value
of `t` (`NumFmt.exact`), and integer → float in every case, where `embed` is then partial (`i64 → f64` has no image at
`2^53 + 1`). A float → integer or a wide → narrow pair is refused where the program is elaborated. -/

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

/-- `$` admits `s → t`: both number atoms, and every value of `s` exact at `t`, or an integer to a float. -/
def castOK (s t : QAtomicType) : Bool :=
  match s.numFmt?, t.numFmt? with
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
  | .u1, _ => default
  | .char, _ => default
  | .sym, _ => default
  | .date, _ => default
  | .datetime, _ => default
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
  match t.numFmt? with
  | some f@(.int ..) => if f.lo ≤ t.num x then some (t.num x, 0) else none
  | some (.float E F) => floatValue E F (t.num x).toNat
  | none => none

/-- The word of `t` holding exactly the value `v`, none where `t` holds no such word. -/
def ofValue (t : QAtomicType) (v : Int × Int) : Option (Carrier t) :=
  match t.numFmt? with
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
  | .sym, _ => ""
  | .general, _ => default

/-- **`embed` on stored words**, the body of `Op.cast s t`: the word of `t` holding the value of the word `x` read at
    `s`, and `2^63` where there is none, which no image is (`word_ne_nul`), so the row is told by that word alone. -/
def castWord (s t : QAtomicType) (x : UInt64) : UInt64 :=
  ((embed s t (ofBits s x)).map (word t)).getD 0x8000000000000000

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
  cases t <;> simp only [ofValue, numFmt?, QAtomicType.width, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    NumFmt.lo, NumFmt.hi, reduceCtorEq, Option.ite_none_right_eq_some] at hv
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
  case u8 | i8 | i16 | i32 | i64 =>
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
  | .sym, _ => inferInstanceAs (DecidableEq String)
  | .general, h => absurd rfl h

/-- A word `$` produces at `t` is canonical (`nonCanonical`, the one predicate): `floatBits` writes zero as `+0` and a
    value as a finite word, so no `-0` and no NaN. Decided at the integers where the format changes, not proved for all. -/
def embedCanonical (s t : QAtomicType) (x : Carrier s) : Bool := (embed s t x).all fun y => !nonCanonical t (word t y)

example : [0, 1, -1, 2, -2, 9007199254740992, -9007199254740992, 4611686018427387904, Int64.maxValue,
    -Int64.maxValue].all (embedCanonical .i64 .f64) := by decide
example : [0, 1, -1, 16777216, -16777216, Int32.maxValue, -Int32.maxValue].all (embedCanonical .i32 .f32) := by decide

-- the pairs `$` admits: widenings and integer → float; no float → integer, no narrowing, no non-number atom
#guard castOK .i32 .i64 && castOK .i64 .f64 && castOK .i32 .f64 && castOK .f32 .f64 && castOK .u8 .i16 &&
  castOK .i64 .f32 && castOK .i64 .i64
#guard !castOK .f64 .i64 && !castOK .i64 .i32 && !castOK .f64 .f32 && !castOK .i8 .u8 && !castOK .i64 .sym &&
  !castOK .date .i64 && !castOK .i64 .char
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
