import Rel.Run.Canon
import Rel.Run.Cols
import Rel.Run.Struct

/-! The row `asc` of `prims` on `Tab`: architecture §4's `canon` (`asc → seen → gather`) of a set, numbered by
position (`Arr.pos`). -/

namespace Rel
open Rel.Ext Rel.Kernel

/-- The first atom type of `A` with no integer order code (`ascLayout`: a float, a symbol, a general atom), the ones
whose `kasc` order `Obj.key_ordCode` does not tie to `Obj.lt`; none when every atom has one. -/
def Obj.ascBad : Obj → Option QAtomicType
  | .atom t => match ascLayout t with | some (_, false, _) => none | _ => some t
  | .prod a b | .sum a b => a.ascBad <|> b.ascBad
  | .arr b => b.ascBad

namespace Tab

/-- **`asc(P)`: the elements of `dom P` numbered in `Obj.lt` order**, `j ↦` the `j`-th smallest from 0: `canon` of the
rows `(0, b)`, `b` a key of `P` (one `kasc`, `kseen`, `kgather`: sorted, no duplicates), keyed by their positions
(`Arr.pos`, no kernel). One key column makes `canon`'s order the one `Λ` reads (`LamLaw .long B`). -/
def asc {B : Obj} (P : Tab B B) : Except String (Tab .long B) :=
  match B.ascBad with
  | some t => .error s!"asc: elements of type {repr t} have no integer order code (a float, whose NaNs and zeros \
      `Obj.lt` merges, a symbol or a general atom): number a set of integers"
  | none => do
    let U ← canon (⟨P.n, ← Arr.zeros .i64 P.n, P.key⟩ : Tab .long B)
    pure ⟨U.n, ← Arr.pos U.n, U.val⟩

end Tab

end Rel
