import Rel.Kernel.Need
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Kernel.Sort` the Rel kernels reach; `Rel.Kernel.Sort` imports it. -/


open Rel.Ext
namespace Rel.Kernel.Order

open Rel.Kernel.Scan (Kind)

/-- q's order on a `float`'s bits, as an unsigned key. Three folds and a monotone map:

* any NaN answers `0`, which is q's null sorting below everything and every NaN equal to every
  other. `0` is not reachable otherwise — the only `b` with `~~~b = 0` is `0xffffffffffffffff`,
  which is itself a NaN;
* `-0.0` answers `+0.0`'s key;
* a negative answers `~~~b`, which reverses the magnitude ordering IEEE gives it, and a non-negative
  answers `b` with the sign bit set, which lifts every positive above every negative. -/
def rank64 (b : UInt64) : UInt64 :=
  if Bits.f64IsNaN b then 0
  else if b == 0x8000000000000000 then 0x8000000000000000
  else if b >>> 63 == 1 then ~~~b
  else b ||| 0x8000000000000000

/-- `rank64` at four bytes. Written out rather than widening through `Float32.toFloat`, which is a
native function and would stop `decide` on every proposition that mentions a `real`. -/
def rank32 (b : UInt32) : UInt32 :=
  if Bits.f32IsNaN b then 0
  else if b == 0x80000000 then 0x80000000
  else if b >>> 31 == 1 then ~~~b
  else b ||| 0x80000000

/-- The unsigned key these raw bits sort by, at each layout. The integral widths flip their sign bit
*within their own width*, which turns q's two's-complement payload order into unsigned order and
puts `0N` — the minimum payload — at key `0`; `byte` and `char` are q's unsigned types and are
already their own key; the float widths rank. A `.bit` is `0` or `1` and needs neither. -/
def rank (k : Kind) (v : UInt64) : UInt64 :=
  match k with
  | .bit | .u8 | .c8 => v
  | .i8 => v ^^^ 0x80
  | .i16 => v ^^^ 0x8000
  | .i32 => v ^^^ 0x80000000
  | .i64 => v ^^^ 0x8000000000000000
  | .f32 => (rank32 v.toUInt32).toUInt64
  | .f64 => rank64 v









/-- The indices at which a key occurs for the first time, in the order they occur — the gather
`distinct` answers with and the key order `group` answers in. -/
def firstsBy {α : Type} [BEq α] (m : Nat) (key : Nat → α) : List Nat :=
  (List.range m).filter fun i => (List.range i).all fun j => key j != key i

/-- Index `i`'s group among the first occurrences `fs` (`firstsBy`): the place of the first one holding its key.
`idsBy` packs it at an id width, `Kernel.kseen` writes it as words; the two answer different forms, so this is shared. -/
def groupIn {α : Type} [BEq α] (fs : List Nat) (key : Nat → α) (i : Nat) : Nat := fs.findIdx (key · == key i)











end Rel.Kernel.Order

namespace Rel.Kernel

open Rel.Kernel.Scan (Kind)
open Rel.Kernel.Order

/-- The layout a column of this type is ordered at. Every q type but the two that have no key of a
fixed width is here, at the layout whose tag is its own (`date` and `datetime` aside, read at `i32` and
`i64`); `char` is at `c8`, whose key is its unsigned byte — the blank is not a null
to a comparison, which is `Eval.missing`'s split read from the ordering side. `symbol` has its own
three entry points. -/
def orderKind : QAtomicType → Option Kind
  | .u1 => some .bit
  | .u8 => some .u8
  | .char => some .c8
  | .i8 => some .i8
  | .i16 => some .i16
  | .i32 | .date => some .i32
  | .i64 | .datetime => some .i64
  | .f32 => some .f32
  | .f64 => some .f64
  | .sym | .general => none


end Rel.Kernel

