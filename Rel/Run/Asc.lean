import Rel.Run.List
import Rel.Run.Bits

/-! The row `asc` of `prims` on `Tab`: architecture §4's `asc` (`kasc`) run on each array's elements, keyed by the cell
they belong to first, so one stable sort orders every cell at once. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

namespace Tab
variable {B : Obj}

/-- **`asc` on the cells `X`** (`ascL`): the elements EXPANDed into `(G, u)` (as `positions`), `kasc` of the key
columns `G` then the elements, whose permutation `p` lists each cell's element rows in a run of its own, stably sorted;
the offsets `u` read through `p` are the new payload, laid out at the old widths (`Vals.cells`); then `canon`. Only an
element type with an integer order code (`ascLayout`, not a float) is sorted, the one `Obj.key_ordCode` ties to `Obj.lt`. -/
def asc {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr .long)) :=
  match B, X with
  | .atom t, ⟨m, lo, hi, f⟩ => match ascLayout t with
    | some (_, false, _) => do
      if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"asc: {n} cells over {m} elements past 2^63"
      let (s, e) ← cellSpan m lo hi
      let w ← colMap .sub n e.enc s.enc
      let (T, G, u) ← expand n w
      let v ← Vals.gather (A := .atom t) T (← colMap .add T (← kgather T G n s.enc) u) f
      let (_, p) ← kasc T [(.atom .i64, G), (.atom t, v.enc)]
      let pay ← colArr .add T (← kgather T p T u) (← colConst T 0)
      canon ⟨n, ⟨m, lo, hi, f⟩, ← Vals.cells n w (pay : Vals .long T)⟩
    | _ => throw s!"asc: elements of type {repr t} have no integer order code (a float, whose NaNs and zeros \
        `Obj.lt` merges, a symbol or a general atom): sort an integer column"
  | _, _ => throw "asc: the elements are not atoms: sort an integer column"

end Tab

end Rel
