import Rel.RepChecks.Canon
import Rel.RepTabComp

/-! The `#guard` checks of `Rel.RepTabComp`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


section Checks


#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2)]).conv.toOption.map Tab.toList) == some [(1, 3), (2, -1), (2, 1)]
#guard ((tab [(3, 1), (1, 2), (-1, 2), (1, 2)]).comp (tab [(2, 5), (1, -3), (2, 6), (7, 7)])).toOption.map Tab.toList ==
  some [(-1, 5), (-1, 6), (1, 5), (1, 6), (3, -3)]
-- the five-kernel `comp` and `conv` against `R ≫ S` and `R°` as sets of pairs, each pair once: duplicates,
-- negatives, an empty side, no common middle value, a group whose run product is past 1
#guard
  let ts : List (List (Int64 × Int64)) := [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
    [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], [(4, 8)], []]
  ts.all fun ps => (ts.all fun qs => specOk ((tab ps).comp (tab qs))
    (ps.flatMap fun (a, b) => qs.filterMap fun (b', c) => if b == b' then some (a, c) else none)) &&
    specOk (tab ps).conv (ps.map fun (a, b) => (b, a))

/-- Whether `compWith b` (blocked past `b` rows) and `compOne` (one expansion) give the same rows. -/
private def blockedOk (b : Nat) (ps qs : List (Int64 × Int64)) : Bool :=
  match Tab.compWith b (tab ps) (tab qs), (tab ps).compOne (tab qs) with
  | .ok X, .ok Y => X.toList == Y.toList
  | _, _ => false

/-- The block count `compCuts b` gives `tab ps ≫ tab qs` (`1`: one block). -/
private def blockCount (b : Nat) (ps qs : List (Int64 × Int64)) : Option Nat :=
  ((Tab.compGroups (tab ps) (tab qs)).bind (Tab.compCuts b (tab ps).n)).toOption.map fun o => (o.map (·.1)).getD 1

-- middle values `1 2 3` expand to `6 4 4` rows (duplicates `(1, 10)` …): every bound `0 … 15` cuts between groups,
-- at a group's end (`6`, `10`), inside a group larger than the bound (`1 … 5`), or not at all (`14`, `15`); an empty
-- side, no common middle value, and negative words
#guard let ps : List (Int64 × Int64) := [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (4, 3), (1, 3), (1, 1)]
  let qs : List (Int64 × Int64) := [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10), (3, 13), (9, 9)]
  let ts := [ps, qs, [], [(-1, 5), (-2, 5), (7, 7)], [(5, -3), (5, 1), (5, -3)]]
  (List.range 16).all fun b => ts.all fun xs => ts.all fun ys => blockedOk b xs ys
#guard blockCount 3 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 3
#guard blockCount 10 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 2
#guard blockCount 14 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 1

/-- Whether `comp` answers `R ≫ S`: as a set the pairs `(a, c)` with `a {R} b {S} c`. -/
private def compOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab B C) : Bool :=
  let sp := R.toList.flatMap fun (a, b) => S.toList.filterMap fun (b', c) => if b == b' then some (a, c) else none
  match R.comp S with
  | .ok T => T.toList.all sp.contains &&
      sp.all T.toList.contains
  | .error _ => false

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]
/-- The same eight values as `f32` bits. -/
private def f32s : List UInt64 := [0x80000000, 0, 0x7fc00001, 0x7fc00002, 0x7f800000, 0xff800000, 0x3fc00000, 0x80000000]
/-- `-1`, `-128`, `127`, `0`, `1`, `-2`, `-128`, `-1` as `i8` bits. -/
private def i8s : List UInt64 := [0xff, 0x80, 0x7f, 0, 1, 0xfe, 0x80, 0xff]

-- a float middle column, a `foR` column of its stored bits (`Arr.ofFn`) as every fixed-width column is
#guard compOk (⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 9], Arr.ofFn .f64 8 (f64s.getD · 0)⟩ : Tab .long (.atom .f64))
  (⟨5, Arr.ofFn .f64 5 (f64s.reverse.getD · 0), Alg.col [7, 8, 9, 7, 6]⟩ : Tab (.atom .f64) .long)
#guard compOk (⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 9], Arr.ofFn .f32 8 (f32s.getD · 0)⟩ : Tab .long (.atom .f32))
  (⟨5, Arr.ofFn .f32 5 (f32s.reverse.getD · 0), Alg.col [7, 8, 9, 7, 6]⟩ : Tab (.atom .f32) .long)

/-- The five-kernel `canon`, `∪`, `∩`, `−`, `⊑`, `conv` and `comp` against their denotations as sets of pairs on the
same tables, whose key, value or middle column holds the words `ws` at `t` (`Arr.ofFn`). -/
private def typeOk (t : QAtomicType) [BEq (Obj.atom t).El] (ws : List UInt64) (hu : t ≠ .u1 ∧ t.width.isSome) : Bool :=
  let x := Arr.ofFn t 8 (ws.getD · 0) hu
  let ls : List Int64 := [5, 6, 5, 7, 5, 6, 8, 5]
  let K : Tab (.atom t) .long := ⟨8, x, Alg.col ls⟩
  let V : Tab .long (.atom t) := ⟨8, Alg.col ls, x⟩
  let K₂ : Tab (.atom t) .long := ⟨8, x, Alg.col ls.reverse⟩
  let S : Tab (.atom t) .long := ⟨3, Arr.ofFn t 3 (ws.getD · 0) hu, Alg.col [5, 6, 3]⟩
  let k := K.toList; let k₂ := K₂.toList; let s := S.toList; let v := V.toList
  let le (R S : Tab (.atom t) .long) := (R.le S).toOption == some (R.toList.all S.toList.contains)
  let comp {A B C : Obj} [BEq B.El] (r : List (A.El × B.El)) (q : List (B.El × C.El)) : List (A.El × C.El) :=
    r.flatMap fun (a, b) => q.filterMap fun (b', c) => if b == b' then some (a, c) else none
  specOk K.canon k && specOk V.canon v && specOk (K.union K₂) (k ++ k₂) &&
  specOk (K.inter K₂) (k.filter k₂.contains) && specOk (K.diff S) (k.filter (!s.contains ·)) &&
  specOk (S.diff K) (s.filter (!k.contains ·)) && le K K && le K S && le S K &&
  specOk K.conv (k.map fun (a, b) => (b, a)) && specOk (V.comp K) (comp v k) && specOk (K.comp V) (comp k v)

-- floats (`-0.0` apart from `+0.0`, two NaN payloads apart, `±inf`), a narrow signed integer and `datetime` as key,
-- value and middle column
#guard typeOk .f64 f64s ⟨by decide, by decide⟩ && typeOk .f32 f32s ⟨by decide, by decide⟩ &&
  typeOk .i8 i8s ⟨by decide, by decide⟩ && typeOk .datetime f64s ⟨by decide, by decide⟩
-- `-0.0` and `+0.0`, and the two NaNs, are distinct rows: stored-bit equality
#guard ((⟨8, Arr.ofFn .f64 8 (f64s.getD · 0), Alg.col [1, 1, 1, 1, 1, 1, 1, 1]⟩ : Tab (.atom .f64) .long).canon.toOption.map
  Tab.n) == some 7

-- a `u1` middle column (`Arr.bools`) and a tuple middle column
#guard compOk (⟨4, Alg.col [3, 1, 2, 1], Arr.bools 4 fun i => i % 2 == 0⟩ : Tab .long (.atom .u1))
  (⟨3, Arr.bools 3 fun i => i == 1, Alg.col [7, 8, 9]⟩ : Tab (.atom .u1) .long)
#guard compOk (⟨4, Alg.col [3, 1, 2, 1], (Alg.col [1, 1, 2, 2], Alg.col [5, 6, 5, 6])⟩ : Tab .long (.prod .long .long))
  (⟨3, (Alg.col [2, 1, 1], Alg.col [5, 6, 5]), Alg.col [7, 8, 9]⟩ : Tab (.prod .long .long) .long)
-- an `arr` middle column: cells over two payloads (equal cells from different ranges, the empty cell),
-- a side of no payload rows, a table of no rows, tuple elements and nested arrays
#guard let As := [arrTab arrCells arrPay, arrTab [(1, 2, 1), (1, 3, 7), (0, 0, 2), (2, 4, 1), (0, 2, 9)] [9, 5, 1, 5],
    arrTab [(0, 0, 1), (0, 0, 2)] [], arrTab [] arrPay]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let As := [arrOn arrCells (B := .prod .long .long) (Alg.col arrPay, Alg.col [0, 1, 0, 0, 2]),
    arrOn [(1, 3, 7), (0, 0, 2), (2, 5, 1)] (B := .prod .long .long) (Alg.col arrPay, Alg.col [1, 0, 0, 1, 0])]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let As := [arrOn arrCells (arrTab [(1, 2, 1), (0, 2, 7), (0, 0, 2), (2, 4, 1), (3, 4, 5)] [9, 5, 1, 5]).key,
    arrOn [(0, 2, 1), (1, 3, 7)] (arrTab arrCells arrPay).key]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
-- a `sum` middle column, with long and with `arr` summands
#guard let Ss := [sumPos [(false, 0, 1), (true, 1, 2), (false, 2, 1), (true, 0, 2), (false, 5, 3)] [5, 7, 5] [9, 4],
    sumPos [(true, 0, 2), (false, 1, 1), (false, 0, 9), (true, 1, 3)] [7, 5] [9, 8]]
  Ss.all fun R => Ss.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let Ss := [sumArr [(false, 0, 1), (true, 1, 2), (false, 2, 1)] arrCells arrPay [9, 4],
    sumArr [(true, 0, 2), (false, 7, 1), (false, 0, 9)] [(1, 3, 7), (0, 0, 2)] [9, 5, 1, 5] [9]]
  Ss.all fun R => Ss.all fun S => compOk (Tab.mk R.n R.val R.key) S

end Checks

end Rel
