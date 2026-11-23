import Rel.RepChecks.Canon
import Rel.RepCols

/-! The `#guard` checks of `Rel.RepCols`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


section Checks

/-- The column of the words `ws` at `t`, `wordsFoR` (a kernel's answer form), where `Enc.WF` admits it. -/
private def wordsArr (t : QAtomicType) (ws : Array UInt64) (n : USize) : Option (Arr t n) :=
  if hn : n.toNat = ws.size then
    if ht : t.width.isSome then
      if hu : t = .u1 → ∀ i (h : i < ws.size), ws[i] < 2 then some (Arr.mk _ ((wordsFoR_closed ws hn).2.2 ht hu) (hasNul_wordsFoR ws))
      else none
    else none
  else none

/-- `Arr.concat` of the words `xs` and `ys` at `t`, read back at `t`, against the two read at `t` and appended: the
stored words, compared bit for bit. -/
private def concatKeeps (t : QAtomicType) (xs ys : Array UInt64) : Bool :=
  match wordsArr t xs xs.size.toUSize, wordsArr t ys ys.size.toUSize with
  | some x, some y => match catPlan xs.size.toUSize ys.size.toUSize with
    | .ok (n, off) => match Arr.concat n off x y with
      | .ok z => raw t n z.enc == raw t xs.size.toUSize x.enc ++ raw t ys.size.toUSize y.enc
      | .error _ => false
    | .error _ => false
  | _, _ => false

-- f64 `-0.0`, `+0.0`, a NaN with payload `1`, q's null; f32 `-0.0` and a NaN with payload; i8 `-128` (as its
-- sign-extended word and as its byte), and the max of every width, at every type of fixed width but `u1`
private def W : Array UInt64 := #[0x8000000000000000, 0, 0x7ff0000000000001, 0xfff8000000000000, 0x80000000,
  0x7f800001, 0xffffffffffffff80, 0x80, 0x7f, 0xff, 0x7fff, 0xffff, 0x7fffffff, 0xffffffff, 0x7fffffffffffffff,
  0xffffffffffffffff, 1]
#guard [QAtomicType.u8, .i16, .i32, .i64, .f32, .f64, .char, .i8, .date, .datetime].all fun t =>
  concatKeeps t W W.reverse && concatKeeps t W #[] && concatKeeps t #[] W
#guard concatKeeps .u1 #[0, 1, 1, 0] #[1, 0, 1]

end Checks

end Rel
