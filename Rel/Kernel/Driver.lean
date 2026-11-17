import Rel.Kernel.Coc

/-! The four column drivers of the coc plan §3 (`map`, `fold`, `scan`, `permute`), each a model over `Enc.raw`: an
op is a step function handed to one of them, and its one `@[extern]` takes the `Enc` objects, whatever their kind
(`crate/src/ffi.rs`'s `Col::of` reads the constructor). `ofRaw` is the answer's form, `Enc.answer`'s rule. -/

namespace Rel.Kernel
open Column

/-- `xs` at `w` bytes each, little-endian: the dense payload whose raw elements at a `w`-byte type are `xs`. -/
def dense (w : Nat) (xs : Array UInt64) : ByteArray := xs.foldl (fun acc v => pushBits acc v w) .empty

/-- The column of `n` elements at `t` whose raw elements are `xs`, in the form a kernel writes it: a boolean's bits,
a fixed-width type's payload as `Enc.answer` leaves it. A symbol or general column has no raw elements a driver
could have computed, and no driver answers one; `gen #[]` is that case's value. -/
def ofRaw (t : QAtomicType) (n : USize) (xs : Array UInt64) : Enc :=
  match t, t.width with
  | .boolean, _ => .bits (packIds 1 n.toNat fun i => (xs[i]?.getD 0).toNat)
  | t, some w => Enc.answer t n (.bytes (dense w xs))
  | _, none => .gen #[]

/-- `map`: element `i` of the answer at `t` is `f` of element `i` of every source in `es`, each read at `s`. -/
def map (s t : QAtomicType) (n : USize) (f : List UInt64 → UInt64) (es : List Enc) : Enc :=
  ofRaw t n ((Array.range n.toNat).map fun i => f (es.map fun e => (e.raw s n)[i]?.getD 0))

/-- `fold`: the source's raw elements in position order through `step` from `seed`. -/
def fold {α : Type} (s : QAtomicType) (n : USize) (step : α → UInt64 → α) (seed : α) (e : Enc) : α :=
  (e.raw s n).foldl step seed

/-- `scan`: element `i` of the answer at `t` is `step` folded over the source's first `i + 1` elements from `seed`. -/
def scan (s t : QAtomicType) (n : USize) (step : UInt64 → UInt64 → UInt64) (seed : UInt64) (e : Enc) : Enc :=
  ofRaw t n ((e.raw s n).foldl (fun (a, out) v => (step a v, out.push (step a v))) (seed, #[])).2

/-- `permute`: the `m` answer elements are the source's elements at the positions `ix`, `fill` where one is past
its end. -/
def permute (s : QAtomicType) (n m : USize) (ix : Array Nat) (fill : UInt64) (e : Enc) : Enc :=
  ofRaw s m (ix.map fun j => (e.raw s n)[j]?.getD fill)

end Rel.Kernel
