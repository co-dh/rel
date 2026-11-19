import Rel.Kernel.Asc

/-! `seen` (PLAN D.12): over rows already in `kasc` order, each row's group and each group's first row. Its callers
compose `kasc ≫ kseen`, so the kernel needs no hash and no direct-addressing table: on sorted rows a group is a run of
adjacent equal rows, found by comparing each row with the one before it. Rows out of order are the error, naming the
first such pair. The body states the answer as `Order.idsBy` does, `Order.firstsBy` over the rows and a row's group
`Order.groupIn` them, which on sorted rows numbers the runs.

Equality is `kasc`'s: two rows are equal when every column's order code at its type (`ascCol`) is, and the code is one
to one on a type's stored bits (`ascOrd_atom`), so equality is equality of stored bits: `-0.0` and `0.0` are two
groups, as are two NaNs with different bits. Normalising NaN and `-0` happens where float words are produced, not here.
`kasc ≫ kseen` numbers exactly `kasc`'s runs of ties. The `k` in the name
is temporary, as for `kscan`; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- **The seen kernel** (PLAN D.12): over the `n` rows of the columns `es`, each a type and a `foR` read as `kasc` reads
it (`ascCol`), rows in `kasc` order (every adjacent pair `lexLe`), the number `k` of distinct keys, each row's group `g`
(`n` words, groups numbered by first occurrence, `Order.groupIn`) and each group's first row `first` (`k` words,
ascending), both as `wordsFoR`. A key is a row's order codes across `es`. The first column that does not read is the
error, `ascCol`'s text after its place in `es`; then the first row that sorts before the row ahead of it, because the
caller is to run `kasc` first. -/
@[extern "qlean_k_seen"]
def kseen (n : USize) (es : @& List (QAtomicType × Enc)) : Except String (Nat × Enc × Enc) := do
  let ks ← es.zipIdx.mapM fun (c, i) => (·.2) <$> (ascCol n c).mapError (s!"seen: es[{i}]: " ++ ·)
  ((List.range (n.toNat - 1)).find? fun i => !lexLe ks i (i + 1)).forM fun i =>
    throw s!"seen: row {i + 1} sorts before row {i}; kseen takes rows in kasc order, so sort them with kasc first"
  let key := fun i => ks.map (·[i]?.getD 0)
  let fs := Order.firstsBy n.toNat key
  pure (fs.length, wordsFoR (Array.ofFn (n := n.toNat) fun i => (Order.groupIn fs key i.1).toUInt64),
    wordsFoR (fs.map Nat.toUInt64).toArray)

end Rel.Kernel
