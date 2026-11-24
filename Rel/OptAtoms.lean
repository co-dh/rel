import Rel.Run.Struct

/-! `Opt.ofAtoms`, the test builder of a `t+1` column from literal atoms, and the `#guard`s of `Tab.inrConvBand` on it.
Outside `Rel.Run`: only tests build a column from atoms, and the decode gate roots at every declaration of the run
libraries. -/

namespace Rel
open Rel Rel.Dep

namespace Opt

/-- The nullable column of `xs`, `none` the null: the values' dense bytes (a null's `0`, never read) and the bitmap of
    the null rows through the one writer `Coc.encode`. `Enc.WF` is decided, never assumed; `none` where an atom is not
    at `t`, or at `general`, whose payload has no block to hold a null. -/
def ofAtoms (t : QAtomicType) (xs : Array (Option QAtom)) : Option (Opt t xs.size.toUSize) :=
  match t.width with
  | none => none
  | some w =>
    if xs.all (·.all (·.type == t)) then
      let b := xs.foldl (init := ByteArray.emptyWithCapacity (xs.size * w)) fun acc a =>
        Column.pushBits acc ((a.map Column.bitsOf).getD 0) w
      let nul := Column.packIds 1 xs.size fun i => (xs[i]?.any Option.isNone).toNat
      let e : Enc := .foR (Kernel.Coc.encode w.toUSize b nul).1 (Kernel.Coc.encode w.toUSize b nul).2
      -- `WF` itself, not `Enc.wf?`: a flagged `u1` block is widened to width 2 for its null, and its metadata then
      -- admits a residual 2 that only the elements rule out (`Column.u1Ok`)
      if h : Enc.WF t xs.size.toUSize e then some (mk e h) else none
    else none

end Opt

-- `inr°` on a `1 + long` column: the rows that are no null, each beside its value; none, some and all null
private def inrBand (xs : List (Option QAtom)) : Option (List ((Unit ⊕ Int64) × Int64)) := do
  let x ← Opt.ofAtoms .i64 xs.toArray
  let T ← (Tab.inrConvBand (a := .one) (b := .long) rfl x).toOption
  pure T.toList
#guard inrBand [some (.i64 5), none, some (.i64 7)] == some [(.inr 5, 5), (.inr 7, 7)]
#guard inrBand [some (.i64 5), some (.i64 6)] == some [(.inr 5, 5), (.inr 6, 6)]
#guard inrBand [none, none, none] == some []
#guard inrBand [] == some []

end Rel
