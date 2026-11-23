import Rel.Run.Gather

/-! `t+1` as one column with in-band nulls (decision K, `Opt`): a written column reads back row for row, nulls in
several blocks of `2 ^ Column.lgEnc`, and `Opt.gather` moves a null with its row. -/

namespace Rel.TestNullband
open Rel

/-- 3000 rows, every 7th from row 3 null: nulls in all three blocks of 1024. -/
def nulRow (i : Nat) : Bool := i % 7 == 3

def longs : Array (Option QAtom) := (Array.range 3000).map fun i =>
  if nulRow i then none else some (.i64 (Int64.ofNat (i * 5) - 7000))

def bools : Array (Option QAtom) := (Array.range 3000).map fun i =>
  if nulRow i then none else some (.u1 (i % 3 == 0))

/-- Every row of `x` against `f`, `none` at the null rows. -/
def agrees {t : QAtomicType} {n : USize} [BEq (El t)] (x : Opt t n) (f : Nat → El t) : Bool :=
  (List.finRange n.toNat).all fun i => x.get i == if nulRow i then none else some (f i)

#guard match Opt.ofAtoms .i64 longs with
  | some x => agrees x fun i => (Int64.ofNat (i * 5) - 7000 : Int64)
  | none => false

#guard match Opt.ofAtoms .u1 bools with
  | some x => agrees x fun i => i % 3 == 0
  | none => false

-- a column with no null writes no flagged block
#guard match Opt.ofAtoms .i64 ((Array.range 3000).map fun i => some (.i64 (Int64.ofNat i))) with
  | some x => !Kernel.hasNul x.enc
  | none => false

-- rows 3 (null), 4, 1004 (null), 1005 and 2999 (null), gathered
#guard match Opt.ofAtoms .i64 longs with
  | some x => match Opt.gather 5 (Ext.Enc.ofBytes 8 (packLongs [3, 4, 1004, 1005, 2999])) x with
    | .ok g => (List.finRange _).map g.get == [none, some (20 - 7000), none, some (5025 - 7000), none]
    | .error _ => false
  | none => false

end Rel.TestNullband
