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
    check d ⟨⟨π₁ π₁ [{(∗,no)}, {(∗,yes)}], π₁ π₂ [{(∗,no)}, {(∗,yes)}]⟩, π₂ [{(∗,no)}, {(∗,yes)}]⟩ =
      {(0,((no,yes),no)),(1,((yes,no),no)),(2,((no,yes),no)),(3,((no,no),yes))} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}
    check d col D "c_9" [{(∗,no)}, {(∗,yes)}] = {(0,no),(1,no),(2,no),(3,yes)} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}

#guard dummiesT.ok

-- the wide pivot over the declared `S = {a,b}`, the rows of `TestFrameNull`'s `pw`: (A,a) 1+4, (B,a) 2, (A,b) 3,
-- (C,b) 5; keys in first-occurrence order A B C, null as 0
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program pivotT where
    obj P
    obj N
    obj K = {A,B,C}
    obj S = {a,b}
    t3 : P ⟶ K×(S×N) ≜ {(0,(A,(a,1))),(1,(B,(a,2))),(2,(A,(b,3))),(3,(A,(a,4))),(4,(C,(b,5)))}
    pw : P ⟶ K×(N×N) ≜ pivotOn(π₁, ⟨w ∈ S ↦ pivotCol(π₁, π₂ π₁, w, F(t3 π₂ π₂) sum, t3)⟩, t3) ⟨π₁, ⟨π₂ π₁ [{(∗,0)}, 𝟙], π₂ π₂ [{(∗,0)}, 𝟙]⟩⟩
    check pw = {(0,(A,(5,3))),(1,(B,(2,0))),(2,(C,(0,5)))}

#guard pivotT.ok

-- an unbounded object has no elements to generate over
/-- error: line 57, col 21: `N` is no finite object of this program: a schema over an object needs its elements -/
#guard_msgs in
rel_program unboundedT where
    obj N
    schema D = {c ∈ N : N}

end Rel.Lang.TestPivotDisk
