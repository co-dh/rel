import Rel.Run.Gather
import Rel.OptAtoms

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
  | some x => match Opt.gather 5 (Enc.ofBytes 8 (packLongs [3, 4, 1004, 1005, 2999])) x with
    | .ok g => (List.finRange _).map g.get == [none, some (20 - 7000), none, some (5025 - 7000), none]
    | .error _ => false
  | none => false

-- q's `asc 3 0N 1` is `0N 1 3`: null is below every value, so `kasc` grades it first (`iasc` = `1 2 0`)
#guard match Opt.ofAtoms .i64 #[some (.i64 3), none, some (.i64 1)] with
  | some x => match Kernel.kasc 3 [(.atom .i64, x.enc)] with
    | .ok (_, p) => Enc.raw .i64 3 p == #[1, 2, 0] && match Opt.gather 3 p x with
      | .ok s => (List.finRange _).map s.get == [none, some 1, some 3]
      | .error _ => false
    | .error _ => false
  | none => false

/-- The pairs `(l, r)` of a join on a nullable key: left keys `ls`, right keys `rs`, one column of both sides' keys
sorted (`kasc`) and grouped (`kseen`); left row `l` joins right row `r` where their rows fall in one group. -/
def joinPairs (ls rs : Array (Option QAtom)) : Option (List (Nat × Nat)) := do
  let x ← Opt.ofAtoms .i64 (ls ++ rs)
  let N := (ls ++ rs).size
  let (vs, p) ← (Kernel.kasc N.toUSize [(.atom .i64, x.enc)]).toOption
  let (_, g, _) ← (Kernel.kseen N.toUSize [(.atom .i64, vs.headD .pos)]).toOption
  let ps := Enc.raw .i64 N.toUSize p
  let gs := Enc.raw .i64 N.toUSize g
  -- input row `j`'s group: the group of the sorted row holding it
  let grp := fun j => ((List.range N).find? (ps[·]? == some j.toUInt64)).bind (gs[·]?)
  pure ((List.range ls.size).flatMap fun l => (List.range rs.size).filterMap fun r =>
    if grp l == grp (ls.size + r) then some (l, r) else none)

-- left `0N 2 5`, right `5 0N 7`: the null joins the null (every null is one value, as in q) and no value
#guard joinPairs #[none, some (.i64 2), some (.i64 5)] #[some (.i64 5), none, some (.i64 7)] == some [(0, 1), (2, 0)]

end Rel.TestNullband
