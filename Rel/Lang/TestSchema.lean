import Rel.Run.Lang.Schema
import Rel.Run.Lang.Embed

/-! `Schema` (PLAN D.11) on a frame of two columns, key `k` and value `v`, as `TestFrame`'s `[K×N]`: each term run by
    `compile` on the frame `x ≫ t`, a frame being its row positions `0…n−1` to its rows. -/

namespace Rel.Lang.TestSchema

open Rel.Lang.Schema

def kv : Schema := [("k", .long), ("v", .long)]

/-- Three rows `(k, v)`: `(1,10) (2,20) (1,30)`. -/
def x : Tab .long kv.obj := ⟨_, Alg.col [0, 1, 2], (Alg.col [1, 2, 1], Alg.col [10, 20, 30])⟩

/-- `x ≫ t`'s pairs and its ok bit. -/
def run (t : Tm kv.obj .long) : List (Int64 × Int64) × Bool :=
  let r : CRel .long .long := (compile (fun _ _ _ => .closed (.pure (.zero, true))) (.comp (.val x) t)).run {}; (r.rel.toList, r.ok)

#guard run (col kv "k") == ([(0, 1), (1, 2), (2, 1)], true)
#guard run (col kv "v") == ([(0, 10), (1, 20), (2, 30)], true)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: no column 'price' in schema [k, v]
-/
#guard_msgs in
example := col kv "price"

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: column 'v' appears twice in schema [v, v]
-/
#guard_msgs in
example := ok (kv.rename "k" "v")

-- each function's term followed by a column of its schema reads the column it was given (`select ≫ col = col`)
def sel := ok (kv.select ["v"])
#guard sel.1 == [("v", .long)] && run (.comp sel.2 (col sel.1 "v")) == run (col kv "v")

def exc := ok (kv.exclude ["v"])
#guard exc.1 == [("k", .long)] && run (.comp exc.2 (col exc.1 "k")) == run (col kv "k")

def ren := ok (kv.rename "v" "w")
#guard ren.1.names == ["k", "w"] && run (.comp ren.2 (col ren.1 "w")) == run (col kv "v")

-- `u ≜ v + 1`, `succ` on the universe `0…63`
def der := ok (kv.derive "u" (.comp (col kv "v") (.succ (.uni (Alg.col ((List.range 64).map Int64.ofNat))))))
#guard der.1.names == ["k", "v", "u"] && run (.comp der.2 (col der.1 "v")) == run (col kv "v")
#guard run (.comp der.2 (col der.1 "u")) == ([(0, 11), (1, 21), (2, 31)], true)

/-! The join of `kv` with `kw`, on `k`: `x'`'s rows pair a row of `kv` with one of `kw`. -/

def kw : Schema := [("k", .long), ("w", .long)]

#guard common kv kw == ["k"]

def jn := ok (kv.join kw)
#guard jn.1.names == ["k", "v", "w"]

/-- Four pairs of rows: `((1,10),(1,7)) ((1,10),(2,8)) ((2,20),(2,8)) ((2,20),(3,9))`. -/
def x' : Tab .long (.prod kv.obj kw.obj) :=
  ⟨_, Alg.col [0, 1, 2, 3], ((Alg.col [1, 1, 2, 2], Alg.col [10, 10, 20, 20]), (Alg.col [1, 2, 2, 3], Alg.col [7, 8, 8, 9]))⟩

-- the pairs whose `k` agree, `0` and `2`, as rows `(k, v, w)`
def joined : CRel .long (.prod (.prod .long .long) .long) := (compile (fun _ _ _ => .closed (.pure (.zero, true))) (.comp (.val x') jn.2)).run {}
#guard joined.ok &&
  (joined.rel.toList : List (Int64 × ((Int64 × Int64) × Int64))) == [(0, ((1, 10), 7)), (2, ((2, 20), 8))]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: no common column in schemas [k, v] and [w]
-/
#guard_msgs in
example := ok (kv.join [("w", .long)])

/-! A program's `schema`: `S` is the object `K×N` (`Schema.obj`), and `col S "…"` its columns, as `col kv "…"` above. -/

rel_program kvProg where
    obj K = {A,B,C}
    obj N = 0…40
    obj P = 0…2
    schema S = {k : K, v : N}
    x : P ⟶ S ≜ {(0,(B,5)),(1,(A,3)),(2,(B,7))}
    y : P ⟶ K×N ≜ x
    k : P ⟶ K ≜ x col S "k"
    v : P ⟶ N ≜ y col S "v"
    check k = {(0,B),(1,A),(2,B)}
    check v = {(0,5),(1,3),(2,7)}

#guard kvProg.ok

-- `ok` reads the column: `v` checked against `k`'s values fails
rel_program kvSwap where
    obj K = {A,B,C}
    obj P = 0…1
    schema S = {k : K, v : K}
    x : P ⟶ S ≜ {(0,(B,A)),(1,(A,C))}
    check x col S "v" = {(0,B),(1,A)}

#guard !kvSwap.ok

/-- error: line 111, col 17: column 'k' appears twice in schema [k, k] -/
#guard_msgs in
rel_program kvTwice where
    obj K = {A,B}
    schema S = {k : K, k : K}

/-- error: line 118, col 17: schema `S`: no column 'w' in schema [k, v] -/
#guard_msgs in
rel_program kvBad where
    obj K = {A,B}
    schema S = {k : K, v : K}
    w : S ⟶ K ≜ col S "w"

end Rel.Lang.TestSchema
