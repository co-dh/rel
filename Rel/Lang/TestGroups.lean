import Rel.Run.Lang.Gen

/-! `groups(k)` and `filter(p)` on a frame of 10⁵ rows, as compositions of the existing operators (D.8, dataframe
    F-a, F-b): the frame `R : row ⟶ value`, a key `k : value ⟶ key`, a coreflexive `p` on values.
    - `filter(p) = R p`: composition with the coreflexive, no node of its own.
    - `groups(k) = ran(R k) Λ((R k)°)`: `Λ` run on the keys `R k` reaches (`compT` hands `lam` the range of its left
      side), each key to the canonical list of its rows (`lam_sound`); no universe of the key is read.
    The check: 1000 keys cost what one key costs, where seeding one fold per key of the universe costs |K|×n. -/

namespace Rel.Lang.TestGroups

open Tab Rel.Alg Gen

def n : Nat := 100000

/-- The frame: row `i` holds the value `i·7919 mod 1000`. -/
def R : Fn false .long .long :=
  val _ _ (ofPairs ((List.range n).map fun i => (Int64.ofNat i, Int64.ofNat (i * 7919 % 1000))), true)

/-- The key `v mod m` of each of the 1000 values. -/
def key (m : Nat) : Fn false .long .long :=
  val _ _ (ofPairs ((List.range 1000).map fun v => (Int64.ofNat v, Int64.ofNat (v % m))), true)

/-- The coreflexive of the values below 500. -/
def p : Fn false .long .long := val _ _ (ofPairs ((List.range 500).map fun v => (Int64.ofNat v, Int64.ofNat v)), true)

def groups (k : Fn false .long .long) : Fn false .long (.arr .long) :=
  let rk := comp _ _ _ false R k
  comp _ _ _ true (ran _ _ rk) (lam _ _ true (conv _ _ rk))

def filter : Fn false .long .long := comp _ _ _ false R p

/-- The groups' count, their rows in all, and whether every list ascends strictly; read through `toList`, the
    proof-side decoder, so it stays outside the timed run. -/
def summary (r : CRel .long (.arr .long)) : Nat × Nat × Bool :=
  let l := r.rel.toList
  (l.length, (l.map (·.2.length)).sum,
    r.ok && l.all fun (_, ys) => (ys.zip ys.tail).all fun (a, b) => decide ((a : Int64) < b))

/-- The run of `groups(k)` and its wall time; the row count forces it. -/
def timed (k : Fn false .long .long) : IO (Nat × CRel .long (.arr .long)) := do
  let t0 ← IO.monoMsNow; let r : CRel .long (.arr .long) := (groups k).run {}
  let _ ← IO.ofExcept (if r.rel.n = 0 then .error "groups: no rows" else .ok ())
  let t1 ← IO.monoMsNow; pure (t1 - t0, r)

#eval show IO Unit from do
  -- `filter` first: it builds the frame `R`, so neither timed run pays for building it
  let f : CRel .long .long := filter.run {}
  let _ ← IO.ofExcept (if f.rel.n = 0 then .error "filter: no rows" else .ok ())
  let (t1, r1) ← timed (key 1); let s1 := summary r1
  let (tk, rk) ← timed (key 1000); let sk := summary rk
  IO.println s!"one key: {t1} ms {s1}; 1000 keys: {tk} ms {sk}; filter: {f.rel.n} rows"
  unless s1 == (1, n, true) && sk == (1000, n, true) do throw (IO.userError s!"groups: {s1} {sk}")
  unless f.ok && f.rel.n.toNat == n / 2 do throw (IO.userError s!"filter: {f.rel.n} rows, ok {f.ok}")
  -- one key's run is the unit a fold per key costs; 1000 keys within a small factor of it read no universe
  unless tk ≤ 3 * t1 + 200 do throw (IO.userError s!"groups: 1000 keys {tk} ms against one key {t1} ms")

end Rel.Lang.TestGroups
