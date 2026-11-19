import Rel.Kernel.Asc

/-! `seen` (PLAN D.12): the seen-set scan over the rows of several key columns. A row's group is the first row with an
equal key, numbered in order of first occurrence, so `B A B` answers `g = 0 1 0` and `first = 0 1`. It replaces
`distinct`, which numbered runs of adjacent equal rows and so was this scan on a sorted input only. The body is the
foR-reading form of `Order.idsBy`: `Order.firstsBy` over the rows, a row's group the index of its key among them.

Equality is `kasc`'s: two rows are equal when every column's order code at its type (`ascCol`) is, so `-0.0` and `0.0`
are one group and every NaN is one group, and `kasc ≫ kseen` numbers exactly `kasc`'s runs of ties. The `k` in the name
is temporary, as for `kscan`; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- **The seen kernel** (PLAN D.12): over the `n` rows of the columns `es`, each a type and a `foR` read as `kasc` reads
it (`ascCol`), the number `k` of distinct keys, each row's group `g` (`n` words, groups numbered by first occurrence) and
each group's first row `first` (`k` words, ascending), both as `wordsFoR`. A key is a row's order codes across `es`. The
first column that does not read is the error, `ascCol`'s text after its place in `es`. -/
@[extern "qlean_k_seen"]
def kseen (n : USize) (es : @& List (QAtomicType × Enc)) : Except String (Nat × Enc × Enc) := do
  let ks ← es.zipIdx.mapM fun (c, i) => (·.2) <$> (ascCol n c).mapError (s!"seen: es[{i}]: " ++ ·)
  let key := fun i => ks.map (·[i]?.getD 0)
  let fs := Order.firstsBy n.toNat key
  pure (fs.length, wordsFoR (Array.ofFn (n := n.toNat) fun i => (fs.findIdx (key · == key i.1)).toUInt64),
    wordsFoR (fs.map Nat.toUInt64).toArray)

end Rel.Kernel
