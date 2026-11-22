import Rel.Kernel.Value

/-! The part of `Rel.Dep.Val` the Rel kernels reach; `Rel.Dep.Val` imports it. -/


namespace Rel.Dep

open Rel

/-- The payload an atom of each atomic type carries — the fiber of `QAtom` over `QAtom.type`.
Types that share a representation share a carrier: a `date` and an `int` are both `Int32`, and
q's own `type` is what tells them apart, exactly as in `QAtom`.

Reducible so that instance search sees through it: without that, `(2 : Carrier .short)` fails
to find `OfNat` and every literal has to be written at its representation type instead of at
its q type, which defeats the point of indexing by the q type.

`X` is `Ext.QValue`'s extension: it reaches only `general`, whose element is any value. -/
@[reducible] def Ext.Carrier (X : Type) : QAtomicType → Type
  -- a general list's element is any value, boxed: the `xs` of `.general xs`
  | .general => Ext.QValue X
  | .u1 => Bool
  | .u8 | .char => UInt8
  | .i16 => Int16
  | .i32 | .date => Int32
  | .i8 => Int8
  | .i64 | .datetime => Int64
  | .f32 => UInt32
  | .f64 => UInt64
  | .sym => UInt64

/-- rel's own carriers, at no extension, as `QValue` is `Ext.QValue Empty`. -/
abbrev Carrier := Ext.Carrier Empty

/-- The payload of a value already known to be at `t`; `none` at any other type. A general
list's element is any value, so at `general` it is the value itself; an extension value (`.ext`)
is no atom, so at every other type it is `none`. The partiality is the price of reading an
*unindexed* value, and it is paid only at the boundary — inside `QLean/Dep/` the index travels
with the value. -/
def Carrier.of? {X : Type} : (t : QAtomicType) → Ext.QValue X → Option (Ext.Carrier X t)
  | .general, v => some v
  | .u1, .atom (.u1 x) => some x
  | .u8, .atom (.u8 x) => some x
  | .char, .atom (.char x) => some x
  | .i8, .atom (.i8 x) => some x
  | .i16, .atom (.i16 x) => some x
  | .i32, .atom (.i32 x) => some x
  | .date, .atom (.date x) => some x
  | .i64, .atom (.i64 x) => some x
  | .f32, .atom (.f32 x) => some x
  | .f64, .atom (.f64 x) => some x
  | .datetime, .atom (.datetime x) => some x
  | .sym, .atom (.sym x) => some x
  | _, _ => none

/-- Every atom is readable at its own type: a value that arrived untyped — off the wire, out
of the interpreter — always enters the indexed world, and only at the type it already had. -/
theorem Carrier.of?_type {X : Type} (a : QAtom) : (Carrier.of? (X := X) a.type (.atom a)).isSome := by
  cases a <;> rfl

end Rel.Dep
