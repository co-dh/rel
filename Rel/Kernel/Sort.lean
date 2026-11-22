import Rel.Kernel.Need
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Kernel.Sort` the Rel kernels reach; `Rel.Kernel.Sort` imports it. -/


open Rel.Ext
namespace Rel.Kernel.Order

open Rel.Kernel.Scan (Kind)









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

/-- The layout a column of this type is ordered at. Every q type but `general`, which has no key of a
fixed width is here, at the layout whose tag is its own (`date` and `datetime` aside, read at `i32` and
`i64`); `char` is at `c8`, whose key is its unsigned byte — the blank is not a null
to a comparison, which is `Eval.missing`'s split read from the ordering side. A symbol is at `i64`: its id, below `2 ^ 63`.
-/
def orderKind : QAtomicType → Option Kind
  | .u1 => some .bit
  | .u8 => some .u8
  | .char => some .c8
  | .i8 => some .i8
  | .i16 => some .i16
  | .i32 | .date => some .i32
  | .i64 | .datetime | .sym => some .i64
  | .f32 => some .f32
  | .f64 => some .f64
  | .general => none


end Rel.Kernel

