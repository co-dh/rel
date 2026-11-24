module

public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Dep.Val` the Rel kernels reach; `Rel.Dep.Val` imports it. -/


namespace Rel.Dep

open Rel

/-- The payload an atom of each atomic type carries — the fiber of `QAtom` over `QAtom.type`.
Types that share a representation share a carrier: a `date` and an `int` are both `Int32`, and
q's own `type` is what tells them apart, exactly as in `QAtom`.

Reducible so that instance search sees through it: without that, `(2 : Carrier .short)` fails
to find `OfNat` and every literal has to be written at its representation type instead of at
its q type, which defeats the point of indexing by the q type. -/
@[reducible] def Carrier : QAtomicType → Type
  -- `general` is a placeholder type (no column holds one), so its carrier is one point
  | .general => Unit
  | .u1 => Bool
  | .u8 | .char => UInt8
  | .i16 => Int16
  | .i32 | .date => Int32
  | .i8 => Int8
  | .i64 | .datetime => Int64
  | .f32 => UInt32
  | .f64 => UInt64
  | .sym => UInt64

/-- The payload of an atom already known to be at `t`; `none` at any other type, and at `general`, which no atom
has. The partiality is the price of reading an *unindexed* atom, and it is paid only at the boundary — inside
`QLean/Dep/` the index travels with the value. -/
def Carrier.of? : (t : QAtomicType) → QAtom → Option (Carrier t)
  | .u1, .u1 x => some x
  | .u8, .u8 x => some x
  | .char, .char x => some x
  | .i8, .i8 x => some x
  | .i16, .i16 x => some x
  | .i32, .i32 x => some x
  | .date, .date x => some x
  | .i64, .i64 x => some x
  | .f32, .f32 x => some x
  | .f64, .f64 x => some x
  | .datetime, .datetime x => some x
  | .sym, .sym x => some x
  | _, _ => none

/-- Every atom is readable at its own type: a value that arrived untyped — off the wire, out
of the interpreter — always enters the indexed world, and only at the type it already had. -/
theorem Carrier.of?_type (a : QAtom) : (Carrier.of? a.type a).isSome := by
  cases a <;> rfl

end Rel.Dep
