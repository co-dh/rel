module

public import Rel.Kernel.Coc
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Kernel.Search` the Rel kernels reach; `Rel.Kernel.Search` imports it. -/


namespace Rel.Kernel

/-- The key an equality compares, with the values q holds equal folded together: the two zeros onto
one, and **every NaN onto one**. At a width whose equality is bit equality this is the identity.

Measured against q 4.1 with a second NaN built as `abs 0n`, whose bits are `0x7ff8…` against `0n`'s
`0xfff8…`: `(abs 0n)~0n` is `1b`, `0n=abs 0n` is `1b`, `(0n,1.0)?abs 0n` is `0`, `(abs 0n) in 0n,1.0`
is `1b`, and `count distinct (0n;1.0;-1.0;abs 0n)` is `3`. The same at `real` with `abs 0Ne`.

`(0n;-0n)` proves none of that and is not evidence for anything: `type -0n` is `-16h`, a *timespan*,
so that pair is a general list of a float and a timespan and nothing about NaN payloads follows from
it. An earlier version of this rule rested on exactly that reading and folded only the zeros.

Masking the sign off leaves `abs`, and IEEE puts every NaN above `+inf` and nothing else there, so
one comparison decides it. -/
def normalise (w : Nat) (float : Bool) (v : UInt64) : UInt64 :=
  if !float then v else
  let abs := v &&& (2 ^ (8 * w - 1) - 1).toUInt64
  let inf : UInt64 := if w == 8 then 0x7ff0000000000000 else 0x7f800000
  if abs == 0 then 0
  else if inf < abs then (if w == 8 then 0xfff8000000000000 else 0xffc00000)
  else v

/-- What `normalise` runs as: the mask by `Column.ones`, the `Nat` `2 ^ 63` being GMP's. -/
def normaliseImpl (w : Nat) (float : Bool) (v : UInt64) : UInt64 :=
  if !float then v else
  let abs := v &&& Column.ones (8 * w - 1)
  let inf : UInt64 := if w == 8 then 0x7ff0000000000000 else 0x7f800000
  if abs == 0 then 0
  else if inf < abs then (if w == 8 then 0xfff8000000000000 else 0xffc00000)
  else v

@[csimp] theorem normalise_eq_impl : @normalise = @normaliseImpl := by
  funext w f v; simp only [normalise, normaliseImpl, Column.ones_eq]



















/-- A **monotone unsigned key**: `x < y` in q's order exactly when this is smaller. Ordering is what
`bin` needs and `normalise` above gives equality, so the two are separate maps over the same bits.

The signed widths flip their sign bit, which turns two's complement into unsigned order and puts q's
null — the least value of the type — lowest, where q has it: `10 20 30 bin 0N` is `-1`. The float
widths fold `-0.0` and every NaN first, exactly as `normalise` does, and then flip: a negative
double's bits descend as its value ascends, so complementing them is the ascending key, and the one
NaN pattern `0xfff8…` complements to a value below every number. -/
def ordKey (w : Nat) (float signed : Bool) (v : UInt64) : UInt64 :=
  let mask : UInt64 := if w == 8 then 0xffffffffffffffff else (2 ^ (8 * w) - 1).toUInt64
  let top : UInt64 := (2 ^ (8 * w - 1)).toUInt64
  if float then
    let u := normalise w true (v &&& mask)
    if u &&& top != 0 then (~~~u) &&& mask else u ||| top
  else if signed then (v &&& mask) ^^^ top
  else v &&& mask

/-- What `ordKey` runs as: its masks as word powers, as `ordCode`'s. -/
def ordKeyImpl (w : Nat) (float signed : Bool) (v : UInt64) : UInt64 :=
  let mask : UInt64 := if w == 8 then 0xffffffffffffffff else Column.ones (8 * w)
  let top : UInt64 := Column.pow2 (8 * w - 1)
  if float then
    let u := normalise w true (v &&& mask)
    if u &&& top != 0 then (~~~u) &&& mask else u ||| top
  else if signed then (v &&& mask) ^^^ top
  else v &&& mask

@[csimp] theorem ordKey_eq_impl : @ordKey = @ordKeyImpl := by
  funext w f s v
  simp only [ordKey, ordKeyImpl, Column.ones_eq, Column.pow2_eq,
    show Nat.toUInt64 2 = 2 from rfl]

/-- The partition point: the first index the test fails at, over `[lo, hi)`. `bin` advances while
`hay[mid] ≤ k` and answers one below it, `binr` advances while `hay[mid] < k` and answers it — so
the two differ in the test and in nothing else. The `fuel` is `hi - lo`, which strictly shrinks each
step and so is a measure.

**The sentinels are `0` and `n`, not `-1` and `n`**, and on an unsorted operand the two forms visit
different elements and answer differently: measured against q 4.1, `5 1 bin 3` is `1` and
`1 9 3 5 bin 4` is `2`, where a halving seeded at `-1` answers `-1` and `0`. That matters here
because `~/q/q.k` line 46 and line 49 build `aj` and `asof` on `bin` and neither sorts its operand
first, so which index comes back is part of what those two answer.

`order` is an **index payload the walk reads `hay` through**, `Int64` per position, and empty where
each position is its own index. That is the one difference between `bin` over a whole column and the
halving a join runs inside one group of it, so it is a parameter here rather than a second walk. -/
def binStep (w : Nat) (float signed right : Bool) (hay order : ByteArray) (k : UInt64) :
    Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo
    else
      let mid := lo + (hi - lo) / 2
      let ix := if order.isEmpty then mid else (Column.bitsAt order (mid * 8) 8).toNat
      let v := ordKey w float signed (Column.bitsAt hay (ix * w) w)
      if (if right then v < k else v ≤ k) then
        binStep w float signed right hay order k fuel (mid + 1) hi
      else binStep w float signed right hay order k fuel lo mid

/-- q's `x bin y` and `x binr y` at dense payloads of one class, as little-endian `Int64`s. -/
def binBytes (w : USize) (float signed right : Bool) (hay : @& ByteArray) (keys : @& ByteArray) :
    ByteArray :=
  let w := w.toNat
  let n := hay.size / w
  (List.range (keys.size / w)).foldl (init := ByteArray.empty) fun acc j =>
    let p := binStep w float signed right hay ByteArray.empty
      (ordKey w float signed (Column.bitsAt keys (j * w) w)) (n + 1) 0 n
    Column.pushBits acc ((if right then (p : Int) else (p : Int) - 1)).toInt64.toUInt64 8







end Rel.Kernel
