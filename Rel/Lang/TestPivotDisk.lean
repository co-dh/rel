import Rel.Run.Table
import Rel.Programs.FrameJoin

/-! Products generated over a finite object (`doc/dataframe-design.zh.typ` F1): `obj V from "dir" c`, the distinct
    values of a column on disk kept as stored; `schema D = {c ∈ V : A}` and `⟨v ∈ V ↦ e⟩`, one column per element,
    for `get_dummies` (`dummy`) and the wide pivot (`pivotCol`), over a disk object and a declared one alike. The
    directory is under `/data/tmp`. -/

namespace Rel.Lang.TestPivotDisk

open Rel Rel.Lang.Table

/-- Four rows `(c, v)`: `(7, 10)`, `(3, 20)`, `(7, 30)`, `(9, 40)`, written afresh to `d` with its `.d`. -/
def fixture (d : String) : IO Unit := do
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  let col (xs : List Nat) := Arr.ofFn .i64 4 fun i => (xs.getD i.val 0).toUInt64
  write [("c", .long), ("v", .long)] d (col [7, 3, 7, 9], col [10, 20, 30, 40])

#eval fixture "/data/tmp/rel-test-pivot-disk/t"

-- `V` is `{3, 7, 9}`, each stored as its value; `D` is `{c_3, c_7, c_9}`, a column per element, `inl ∗` read as `yes`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program dummiesT where
    obj V from "/data/tmp/rel-test-pivot-disk/t" c
    obj P
    obj N
    obj Y = {no, yes}
    schema T = {c : V, v : N}
    input x : P ⟶ T from "/data/tmp/rel-test-pivot-disk/t"
    schema D = {c ∈ V : 1+1}
    d : P ⟶ D ≜ ⟨e ∈ V ↦ dummy(col T "c", e, x)⟩
    check d ⟨⟨π₁ π₁ [{(∗,yes)}, {(∗,no)}], π₁ π₂ [{(∗,yes)}, {(∗,no)}]⟩, π₂ [{(∗,yes)}, {(∗,no)}]⟩ =
      {(0,((no,yes),no)),(1,((yes,no),no)),(2,((no,yes),no)),(3,((no,no),yes))} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}
    -- the library definition generic over the object: the columns are `V`'s elements, read from the data at this use
    g : P ⟶ D ≜ getDummies(col T "c", x)
    check g = d where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}
    check g col D "c_9" [{(∗,yes)}, {(∗,no)}] = {(0,no),(1,no),(2,no),(3,yes)} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}
    check d col D "c_9" [{(∗,yes)}, {(∗,no)}] = {(0,no),(1,no),(2,no),(3,yes)} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}

#guard dummiesT.ok

-- `obj V from` at the atom the `.d` names: a `date` column, its distinct days in date order, each named as a date
-- literal writes it; `5` rows `(d, v)` with two on 2024.01.15 (day 19737 of the epoch 1970.01.01)
/-- Four rows `(d, v)` of a `date` column `d`: days 19737, 19000, 19737, 19800, written afresh to `p`. -/
def fixtureDate (p : String) : IO Unit := do
  if ← System.FilePath.pathExists p then IO.FS.removeDirAll p
  let days := [19737, 19000, 19737, 19800]
  write [("d", .atom .date), ("v", .long)] p
    (Arr.ofFn .date 4 fun i => (days.getD i.val 0).toUInt64, Arr.ofFn .i64 4 fun i => (10 * (i.val + 1)).toUInt64)

#eval fixtureDate "/data/tmp/rel-test-pivot-disk/dates"

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program datesT where
    obj V from "/data/tmp/rel-test-pivot-disk/dates" d
    obj P
    obj N
    obj Y = {no, yes}
    schema T = {d : V, v : N}
    input x : P ⟶ T from "/data/tmp/rel-test-pivot-disk/dates"
    schema D = {c ∈ V : 1+1}
    d : P ⟶ D ≜ ⟨e ∈ V ↦ dummy(col T "d", e, x)⟩
    check d col D "c_2024.01.15" [{(∗,yes)}, {(∗,no)}] = {(0,yes),(1,no),(2,yes),(3,no)} where x ≜ {(0,(2024.01.15,10)),(1,(2022.01.08,20)),(2,(2024.01.15,30)),(3,(2024.03.18,40))}

#guard datesT.ok

-- a `f64` column: the floats in totalOrder (`-2.5` before `1.5`), each named as a float literal writes it
/-- Three rows `(f, v)`: `f` is `1.5`, `-2.5`, `1.5`; written afresh to `p`. -/
def fixtureF64 (p : String) : IO Unit := do
  if ← System.FilePath.pathExists p then IO.FS.removeDirAll p
  let fs : List Float := [1.5, -2.5, 1.5]
  write [("f", .atom .f64), ("v", .long)] p
    (Arr.ofFn .f64 3 fun i => (fs.getD i.val 0).toBits, Arr.ofFn .i64 3 fun i => (10 * (i.val + 1)).toUInt64)

#eval fixtureF64 "/data/tmp/rel-test-pivot-disk/floats"

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program floatsT where
    obj V from "/data/tmp/rel-test-pivot-disk/floats" f
    obj P
    obj N
    obj Y = {no, yes}
    schema T = {f : V, v : N}
    input x : P ⟶ T from "/data/tmp/rel-test-pivot-disk/floats"
    schema D = {c ∈ V : 1+1}
    d : P ⟶ D ≜ ⟨e ∈ V ↦ dummy(col T "f", e, x)⟩
    check d col D "c_-2.5" [{(∗,yes)}, {(∗,no)}] = {(0,no),(1,yes),(2,no)} where x ≜ {(0,(1.5,10)),(1,(-2.5,20)),(2,(1.5,30))}

#guard floatsT.ok

-- a `sym` column: the ids as stored (a symbol is its 8-byte id), ascending
/-- Three rows `(s, v)`: `s` is the symbol id `5`, `2`, `5`; written afresh to `p`. -/
def fixtureSym (p : String) : IO Unit := do
  if ← System.FilePath.pathExists p then IO.FS.removeDirAll p
  let ids := [5, 2, 5]
  write [("s", .atom .sym), ("v", .long)] p
    (Arr.ofFn .sym 3 fun i => (ids.getD i.val 0).toUInt64, Arr.ofFn .i64 3 fun i => (10 * (i.val + 1)).toUInt64)

#eval fixtureSym "/data/tmp/rel-test-pivot-disk/syms"

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program symsT where
    obj V from "/data/tmp/rel-test-pivot-disk/syms" s
    obj P
    obj N
    obj Y = {no, yes}
    schema T = {s : V, v : N}
    input x : P ⟶ T from "/data/tmp/rel-test-pivot-disk/syms"
    schema D = {c ∈ V : 1+1}
    d : P ⟶ D ≜ ⟨e ∈ V ↦ dummy(col T "s", e, x)⟩
    check d col D "c_5" [{(∗,yes)}, {(∗,no)}] = {(0,yes),(1,no),(2,yes)} where x ≜ {(0,(5,10)),(1,(2,20)),(2,(5,30))}

#guard symsT.ok

-- a `u1` column has no literal to name an element by (`litLayout`), as `schema S from` and `obj F : u1` refuse it
/-- Three rows of a `u1` column `b`, written afresh to `p`. -/
def fixtureBit (p : String) : IO Unit := do
  if ← System.FilePath.pathExists p then IO.FS.removeDirAll p
  write [("b", .atom .u1)] p
    (Arr.mk (Ext.Enc.blank .u1 3) (Ext.Enc.blank_WF .u1 3) (Ext.Enc.blank_plain .u1 3))

#eval fixtureBit "/data/tmp/rel-test-pivot-disk/bits"

/-- error: obj V from /data/tmp/rel-test-pivot-disk/bits b: the column is at the atom u1, and no object of u1 is declared: no literal of u1 is stored -/
#guard_msgs in
rel_program bitsT where
    obj V from "/data/tmp/rel-test-pivot-disk/bits" b

-- the wide pivot over the declared `S = {a,b}`, the rows of `TestFrameNull`'s `pw`: (A,a) 1+4, (B,a) 2, (A,b) 3,
-- (C,b) 5; keys in first-occurrence order A B C, null as 0
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program pivotT where
    obj P
    obj N
    obj K = {A,B,C}
    obj S = {a,b}
    t3 : P ⟶ K×(S×N) ≜ {(0,(A,(a,1))),(1,(B,(a,2))),(2,(A,(b,3))),(3,(A,(a,4))),(4,(C,(b,5)))}
    pw : P ⟶ K×(N×N) ≜ pivotOn(π₁, ⟨w ∈ S ↦ pivotCol(π₁, π₂ π₁, w, F(t3 π₂ π₂) sum, t3)⟩, t3) ⟨π₁, ⟨π₂ π₁ [𝟙, {(∗,0)}], π₂ π₂ [𝟙, {(∗,0)}]⟩⟩
    check pw = {(0,(A,(5,3))),(1,(B,(2,0))),(2,(C,(0,5)))}

#guard pivotT.ok

-- an unbounded object has no elements to generate over
/-- error: line 144, col 21: `N` is no finite object of this program: a schema over an object needs its elements -/
#guard_msgs in
rel_program unboundedT where
    obj N
    schema D = {c ∈ N : N}

end Rel.Lang.TestPivotDisk
