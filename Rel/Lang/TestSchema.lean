import Rel.Run.Lang.Schema
import Rel.Run.Lang.Embed
import Rel.Lang.GenSound
/-! `Schema` (PLAN D.11) on a frame of two columns, key `k` and value `v`, as `TestFrame`'s `[K×N]`: the schemas each
    function builds; the terms run in the programs below. -/

namespace Rel.Lang.TestSchema

open Rel.Lang.Schema

def kv : Schema := [("k", .long), ("v", .long)]

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

-- the schema each function builds
def sel := ok (kv.select ["v"])
#guard sel.1 == [("v", .long)]

def exc := ok (kv.exclude ["v"])
#guard exc.1 == [("k", .long)]

def ren := ok (kv.rename "v" "w")
#guard ren.1.names == ["k", "w"]

def der := ok (kv.derive "u" (.comp (col kv "v") (Tm.cut1 succRow (.uni (Alg.col ((List.range 64).map Int64.ofNat))))))
#guard der.1.names == ["k", "v", "u"]

/-! The join of `kv` with `kw`, on `k`. -/

def kw : Schema := [("k", .long), ("w", .long)]

#guard common kv kw == ["k"]

def jn := ok (kv.join kw)
#guard jn.1.names == ["k", "v", "w"]

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

/-- error: line 89, col 17: column 'k' appears twice in schema [k, k] -/
#guard_msgs in
rel_program kvTwice where
    obj K = {A,B}
    schema S = {k : K, k : K}

/-- error: line 96, col 17: schema `S`: no column 'w' in schema [k, v] -/
#guard_msgs in
rel_program kvBad where
    obj K = {A,B}
    schema S = {k : K, v : K}
    w : S ⟶ K ≜ col S "w"

end Rel.Lang.TestSchema
