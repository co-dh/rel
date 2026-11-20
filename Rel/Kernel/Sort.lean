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










/-- `firsts` over a symbol column. Equality is the bytes, so it is `Column.symCmp … = .eq` and not a second
statement of what two symbols being the same means. -/
def symFirsts (blob : ByteArray) (offs : Array Nat) : List Nat :=
  (List.range (offs.size - 1)).filter fun i =>
    (List.range i).all fun j => Column.symCmp (Column.symKey blob offs j) (Column.symKey blob offs i) != .eq

/-- The blob and offsets of these symbols, in `Column.syms` layout: each one's bytes followed by its
NUL, and the `g + 1` starts. -/
def symsAt (blob : ByteArray) (offs : Array Nat) (is : List Nat) : ByteArray × Array Nat :=
  ( is.foldl (init := ByteArray.empty) fun acc i => (acc ++ Column.symKey blob offs i).push 0
  , (is.foldl (init := (#[0], 0)) fun (o, pos) i =>
      (o.push (pos + (Column.symKey blob offs i).size + 1), pos + (Column.symKey blob offs i).size + 1)).1 )





/-- q's `distinct` over a symbol column, as the payload a `Column.syms` is made of. -/
def distinctSyms (blob : @& ByteArray) (offs : @& Array Nat) : ByteArray × Array Nat :=
  symsAt blob offs (symFirsts blob offs)

/-- A symbol column interned: the distinct symbols in `syms` layout, and one id per element
indexing them, packed at `Column.idWidth` — the fields of `Column.enum`, whose docstring says why
the dictionary is the column's own and not a process-wide table.

The specification is the two kernels beside it, so there is one statement of what "the distinct
symbols" are and one of where a symbol is found: `distinctSyms` in first-occurrence order, and
`findSymScalar` against it. The C does both in the pass `sym_group` already makes — the group of an
element *is* its dictionary index, the groups being numbered in that same order. -/
def internSyms (blob : @& ByteArray) (offs : @& Array Nat) :
    ByteArray × Array Nat × ByteArray :=
  let (db, dof) := distinctSyms blob offs
  (db, dof, Column.packIds (Column.idWidth dof) (offs.size - 1) fun i =>
    (findSymScalar db dof (Column.symKey blob offs i)).toNat)

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

namespace Rel.Column


/-- The same column interned, and unchanged where it is not a symbol payload. `Column.blobOf` is the
other direction and the two are inverse on the symbols, which is the whole obligation: interning is a
choice of representation and owes nothing else, exactly as `Column.encode` owes only its round trip.

Here and not beside `Column.symsOf` for the reason `Column.encode` is here and not beside
`Column.ofAtoms`: the kernel that does the work is downstream of `QLean/Value.lean`, and the place a
column is *materialised* is `Eval.vectorOf`, which reaches both of these together.

**The order the arms land in decides whether this pays, and it nearly did not.** With only `distinct`,
`group`, `in` and `?` migrated, calling this from `Eval.vectorOf` lost 16M `1000#xs` 7µs→1035ms,
`xs=xs` 24ms→3.1s and `asc` 109ms→2.5s, because every verb still reaching `Column.blobOf` expands the
dictionary back to a blob. With `#`, `reverse`, `=`, `~`, the gather and the two symbol maps given
arms it wins every line: `reverse` 817ms→3.0, `hsym` 50→3.6, `lower` 35→3.7, `=` 24→6.2, `like`
21→5.9, `asc` 100→43. The maps are where the win is — they run on the *dictionary*, three entries
against sixteen million. -/
def intern (e : Ext.Enc X) : Ext.Enc X :=
  match e with
  | .syms blob offs =>
    let (db, dof, ids) := Rel.Kernel.Order.internSyms blob offs
    .enum db dof ids
  | e => e

end Rel.Column

namespace Rel.Kernel

end Rel.Kernel


namespace Rel.Kernel.Order

open Rel.Kernel.Scan (Kind)

end Rel.Kernel.Order

namespace Rel.Kernel

open Rel.Kernel.Scan (Kind)
open Rel.Kernel.Order



end Rel.Kernel

namespace Rel.Column

end Rel.Column

namespace Rel.Kernel

end Rel.Kernel
