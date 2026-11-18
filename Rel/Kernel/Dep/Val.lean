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
  | .boolean => Bool
  | .byte | .char => UInt8
  | .short => Int16
  | .int | .month | .date | .minute | .second | .time => Int32
  | .long | .timestamp | .timespan => Int64
  | .real => UInt32
  | .float | .datetime => UInt64
  | .symbol => String

/-- rel's own carriers, at no extension, as `QValue` is `Ext.QValue Empty`. -/
abbrev Carrier := Ext.Carrier Empty

/-- The payload of a value already known to be at `t`; `none` at any other type. A general
list's element is any value, so at `general` it is the value itself; an extension value (`.ext`)
is no atom, so at every other type it is `none`. The partiality is the price of reading an
*unindexed* value, and it is paid only at the boundary — inside `QLean/Dep/` the index travels
with the value. -/
def Carrier.of? {X : Type} : (t : QAtomicType) → Ext.QValue X → Option (Ext.Carrier X t)
  | .general, v => some v
  | .boolean, .atom (.boolean x) => some x
  | .byte, .atom (.byte x) => some x
  | .char, .atom (.char x) => some x
  | .short, .atom (.short x) => some x
  | .int, .atom (.int x) => some x
  | .month, .atom (.month x) => some x
  | .date, .atom (.date x) => some x
  | .minute, .atom (.minute x) => some x
  | .second, .atom (.second x) => some x
  | .time, .atom (.time x) => some x
  | .long, .atom (.long x) => some x
  | .timestamp, .atom (.timestamp x) => some x
  | .timespan, .atom (.timespan x) => some x
  | .real, .atom (.real x) => some x
  | .float, .atom (.float x) => some x
  | .datetime, .atom (.datetime x) => some x
  | .symbol, .atom (.symbol x) => some x
  | _, _ => none

/-- Every atom is readable at its own type: a value that arrived untyped — off the wire, out
of the interpreter — always enters the indexed world, and only at the type it already had. -/
theorem Carrier.of?_type {X : Type} (a : QAtom) : (Carrier.of? (X := X) a.type (.atom a)).isSome := by
  cases a <;> rfl

end Rel.Dep
