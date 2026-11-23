module

public import Rel.Kernel.Coc
public import Rel.Kernel.Need
public import Rel.Kernel.Op
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Kernel.Elementwise` the Rel kernels reach; `Rel.Kernel.Elementwise` imports it. -/


open Rel.Ext
namespace Rel.Kernel.Ew

/-- Storage classes. `bits` is a `widen` source only: a boolean payload is one bit per element, so
no arithmetic loop is instantiated over it. -/
def u8 : UInt8 := 0
def i16 : UInt8 := 1
def i32 : UInt8 := 2
def i64 : UInt8 := 3
def f32 : UInt8 := 4
def f64 : UInt8 := 5

/-- Comparisons, numbered apart from the value verbs because they are a separate engine with a
separate result shape — a bitmap whatever the operands were. -/
def eq : UInt8 := 0
def ne : UInt8 := 1
def lt : UInt8 := 2
def le : UInt8 := 3
def gt : UInt8 := 4

/-- A comparison of two booleans run by the bit engine is this plus its code, a byte of each operand
at a time: widening the pair to `int` first was 33% of `differ` on a boolean column. -/
def bitCmp : UInt8 := 16


/-- Operand shapes. An atom is passed as a one-element payload and read at index 0. -/
def vv : UInt8 := 0
def va : UInt8 := 1
def av : UInt8 := 2

/-- Bytes per element. -/
def width (cls : UInt8) : Nat :=
  if cls == u8 then 1 else if cls == i16 then 2
  else if cls == i32 || cls == f32 then 4 else 8

/-- Element `i` of a dense payload, as raw bits. A read past the end answers `0`, the convention
`Column.bitsAt` sets and for its reason: the caller is bounded by the count. -/
def elem (cls : UInt8) (x : ByteArray) (i : Nat) : UInt64 :=
  Column.bitsAt x (i * width cls) (width cls)

/-- The pair of operand indices a shape reads at element `i`. -/
def shapeIdx (shape : UInt8) (i : Nat) : Nat × Nat :=
  if shape == vv then (i, i) else if shape == va then (i, 0) else (0, i)

/-- Raw bits read as the signed value q stores at that class. `byte` and `char` are q's only
unsigned fixed-width types and zero-extend; everything else sign-extends, which is what puts q's
null — the minimum of the type — below every other element under a plain comparison. -/
def signed (cls : UInt8) (v : UInt64) : Int64 :=
  if cls == u8 then v.toUInt8.toUInt64.toInt64
  else if cls == i16 then v.toUInt16.toInt16.toInt64
  else if cls == i32 then v.toUInt32.toInt32.toInt64
  else v.toInt64


def ord64 (x y : UInt64) : Ordering :=
  if Bits.f64IsNaN x then (if Bits.f64IsNaN y then .eq else .lt)
  else if Bits.f64IsNaN y then .gt
  else
    let a := Float.ofBits x
    let b := Float.ofBits y
    if a < b then .lt else if b < a then .gt else .eq

def ord32 (x y : UInt32) : Ordering :=
  if Bits.f32IsNaN x then (if Bits.f32IsNaN y then .eq else .lt)
  else if Bits.f32IsNaN y then .gt
  else
    let a := Float32.ofBits x
    let b := Float32.ofBits y
    if a < b then .lt else if b < a then .gt else .eq

/-- The integral value verbs. Nothing wraps here: the caller writes the result back at the class's
own width and *that* truncation is q's wrap, so `2147483647i+1i` is `0Ni` without this saying so.

`&` and `|` need no null case — q's null is the least value of the type, so a signed minimum already
answers `0N&1` with `0N`, measured. `^` reads only its right operand's null: `0N^1` is `1` and
`1^0N` is `1`. -/
def intStep (op : UInt8) (nul x y : Int64) : Int64 :=
  if op == add then (if x == nul || y == nul then nul else x + y)
  else if op == sub then (if x == nul || y == nul then nul else x - y)
  else if op == mul then (if x == nul || y == nul then nul else x * y)
  else if op == fill then (if y == nul then x else y)
  else if op == lesser then (if x < y then x else y)
  else if op == greater then (if y < x then x else y)
  -- q divides toward *minus infinity* and takes the matching remainder: measured, `-7 div 2` is
  -- `-4` and `-7 mod 3` is `2`, which is `Int.fdiv` and `Int.fmod`. A zero divisor is `0N` at both
  -- and is tested here, ahead of the machine divide, which traps on it rather than answering.
  else if op == idiv || op == imod then
    (if x == nul || y == nul || y == 0 then nul
     else Int64.ofInt (if op == idiv then Int.fdiv x.toInt y.toInt else Int.fmod x.toInt y.toInt))
  else Kernel.stop (fun _ => s!"intStep: verb {op} has no integral case; `%` answers a float at every operand type") (fun _ => default)

/-- `Int.fdiv`, `Int.fmod` of two words in words: the machine's truncating `/`, `%`, moved one step toward minus
infinity when the division is inexact and the signs differ (`Int.fdiv_eq_tdiv`, `Int.fmod_eq_tmod`). -/
private theorem fdiv_word (x y : Int64) (hy : y ≠ 0) :
    Int64.ofInt (x.toInt.fdiv y.toInt) = (if x % y != 0 && (x < 0) != (y < 0) then x / y - 1 else x / y) ∧
    Int64.ofInt (x.toInt.fmod y.toInt) = (if x % y != 0 && (x < 0) != (y < 0) then x % y + y else x % y) := by
  have hq : Int64.ofInt (x.toInt.tdiv y.toInt) = x / y :=
    (Int64.ofInt_eq_iff_bmod_eq_toInt _ _).2 (Int64.toInt_div x y).symm
  have hr : Int64.ofInt (x.toInt.tmod y.toInt) = x % y := by rw [← Int64.toInt_mod, Int64.ofInt_toInt]
  have hd : y.toInt ∣ x.toInt ↔ x % y = 0 := by
    rw [Int.dvd_iff_tmod_eq_zero, ← Int64.toInt_mod, ← Int64.toInt_zero, Int64.toInt_inj]
  have hx : 0 ≤ x.toInt ↔ ¬ x < 0 := by rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero]; omega
  have hy' : 0 ≤ y.toInt ↔ ¬ y < 0 := by rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero]; omega
  have hy0 : y.toInt ≠ 0 := fun h => hy (Int64.toInt_inj.1 (h.trans Int64.toInt_zero.symm))
  rw [Int.fdiv_eq_tdiv, Int.fmod_eq_tmod, Int64.ofInt_sub, Int64.ofInt_add, hq, hr]
  by_cases h0 : x % y = 0
  · simp [hd, h0]
  · have hn : ¬ y.toInt ∣ x.toInt := fun h => h0 (hd.1 h)
    have hs : (y < 0 → y.toInt < 0) ∧ (¬ y < 0 → 0 < y.toInt) :=
      ⟨fun h => by rwa [Int64.lt_iff_toInt_lt, Int64.toInt_zero] at h, fun h => by have := hy'.2 h; omega⟩
    by_cases ha : x < 0 <;> by_cases hb : y < 0 <;> simp [hn, hx, hy', h0, ha, hb]
    · have := hs.1 hb; simp [Int.sign_eq_neg_one_of_neg this, Int64.toNatClampNeg, Int.toNat_of_nonpos (Int.le_of_lt this)]
    · have := hs.2 hb; simp [Int.sign_eq_one_of_pos this, Int.natAbs_of_nonneg (Int.le_of_lt this)]

/-- What `intStep` runs as: `idiv` and `imod` by `fdiv_word`, where `Int.fdiv`, `Int.fmod` of `toInt` run in GMP once an
operand is past a small `Int`; every other verb is `intStep` itself. -/
def intStepImpl (op : UInt8) (nul x y : Int64) : Int64 :=
  if (op == idiv || op == imod) && !(x == nul || y == nul || y == 0) then
    let c := x % y != 0 && (x < 0) != (y < 0)
    if op == idiv then (if c then x / y - 1 else x / y) else (if c then x % y + y else x % y)
  else intStep op nul x y

@[csimp] theorem intStep_eq_intStepImpl : @intStep = @intStepImpl := by
  funext op nul x y; unfold intStepImpl; split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at h
    obtain ⟨ho, hn⟩ := h
    have hw := fdiv_word x y hn.2
    rcases ho with rfl | rfl
    · show (if x == nul || y == nul || y == 0 then nul else Int64.ofInt (Int.fdiv x.toInt y.toInt)) = _
      simp [hn, hw.1]
    · show (if x == nul || y == nul || y == 0 then nul else Int64.ofInt (Int.fmod x.toInt y.toInt)) = _
      simp [hn, hw.2, show (imod == idiv) = false by decide]
  · rfl




/-- One bit of a comparison. The integral classes compare their sign-extended payloads, which is
q's order for every type but `char`: there the null is the blank and q goes on ordering it by its
byte, which is what zero-extending a `u8` gives. -/
def cmpStep (op cls : UInt8) (x y : UInt64) : Bool :=
  let o :=
    -- q's comparison tolerance, `QAtom.tolerant`, at `f64` alone: two reals are never that close
    if cls == f64 then
      let o := ord64 x y
      if o != .eq && QAtom.tolerant (Float.ofBits x) (Float.ofBits y) then .eq else o
    else if cls == f32 then ord32 x.toUInt32 y.toUInt32
    else compare (signed cls x) (signed cls y)
  if op == eq then o == .eq else if op == ne then o != .eq
  else if op == lt then o == .lt else if op == le then o != .gt
  else if op == gt then o == .gt else o != .lt

/-- One bit of a value verb at `bits`. Only three verbs reach it: `&` on two booleans is their
minimum, which is `and`; `|` is `or`; and `^` copies its right operand whole, measured — `01b^10b`
is `10b` — booleans having no null to fill. `+ - * %` never arrive, q answering them at `int` or
`float` from a boolean pair, so the class the payload is read at is not `bits` there. A comparison
arrives as `bitCmp` plus its code and is `cmpStep`'s on the two bits. -/
def bitStep (op : UInt8) (x y : Bool) : Bool :=
  if op ≥ bitCmp then cmpStep (op - bitCmp) u8 (if x then 1 else 0) (if y then 1 else 0)
  else if op == lesser then x && y
  else if op == greater then x || y
  else if op == fill then y
  else Kernel.stop (fun _ => s!"bitStep: verb {op} has no boolean case; `+ - * %` widen a boolean pair first") (fun _ => default)













/-- q's six comparisons as a bitmap, one bit per element: the chain's comparison stage, and what `cmp` encodes. The
bits above `n` in the last byte stay `0`: `~` compares payloads, and trailing garbage would make equal vectors
compare unequal. -/
def cmpBitmap (op cls shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray :=
  (List.range ((n.toNat + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte j =>
      let i := k * 8 + j
      let (ia, ib) := shapeIdx shape i
      if i < n.toNat && cmpStep op cls (elem cls a ia) (elem cls b ib) then
        byte ||| (1 <<< j.toUInt8)
      else byte)

/-- q's six comparisons as the `u1` Frame of Reference column `Coc.bools` lays out. -/
def cmp (op cls shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray × ByteArray :=
  Coc.bools n.toNat (Column.bitAt (cmpBitmap op cls shape a b n))



/-- `&`, `|` and `^` over two boolean bitmaps — the one value result that is not a dense payload,
and the reason `x within (lo;hi)` no longer boxes: the two comparisons it is built from already
reach `cmp`, and it was this last `&` between their bitmaps that fell to atoms. Both operands are
already `Column.bits`, so nothing widens and the C runs a byte at a time. The bits above `n` in the
last byte stay `0` for `cmpBitmap`'s reason. This bitmap is the chain's stage and what `bit` encodes. -/
def bitBitmap (op shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray :=
  (List.range ((n.toNat + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte j =>
      let i := k * 8 + j
      let (ia, ib) := shapeIdx shape i
      if i < n.toNat && bitStep op (Column.bitAt a ia) (Column.bitAt b ib) then
        byte ||| (1 <<< j.toUInt8)
      else byte)

/-- A verb of two bitmaps as the `u1` Frame of Reference column `Coc.bools` lays out. -/
def bit (op shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray × ByteArray :=
  Coc.bools n.toNat (Column.bitAt (bitBitmap op shape a b n))






-- 9 and 10 are the encoder stages `rust/src/ew.rs` appends itself and a program never names










end Rel.Kernel.Ew

namespace Rel.Kernel



end Rel.Kernel


namespace Rel.Kernel.Ew



end Rel.Kernel.Ew

namespace Rel.Kernel





end Rel.Kernel
