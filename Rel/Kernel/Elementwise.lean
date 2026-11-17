import Rel.Kernel.Coc
import Rel.Kernel.Value

/-! The part of `Rel.Kernel.Elementwise` the Rel kernels reach; `Rel.Kernel.Elementwise` imports it. -/


open Rel.Ext
namespace Rel.Kernel.Ew

/-- Storage classes. `bits` is a `widen` source only: a boolean payload is one bit per element, so
no arithmetic loop is instantiated over it. -/
def u8 : UInt8 := 0
def i16 : UInt8 := 1
def i32 : UInt8 := 2
def i64 : UInt8 := 3
def f32 : UInt8 := 4
def f64 : UInt8 := 5
def bits : UInt8 := 6

/-- Value verbs: `+ - * % ^ & |`. -/
def add : UInt8 := 0
def sub : UInt8 := 1
def mul : UInt8 := 2
def fill : UInt8 := 4
def lesser : UInt8 := 5
def greater : UInt8 := 6

/-- `div` and `mod`, numbered after the seven q spells as glyphs. They are here rather than in an
engine of their own because they are the same loop over the same two payloads; what is not shared is
the *result type*, which `Eval.divModType` gives and which is not always at or above both operands.
`~/q/q.k` line 4 defines `mod:{x-y*x div y}` and both steps below say exactly that. -/
def idiv : UInt8 := 7
def imod : UInt8 := 8

/-- `x xexp y`. Here and not among the monadic maps because it takes two operands, and here at all
because `~/q/q.k` line 4 defines `xlog:{log[y]%log x}` and defines **no** `xexp` — q has a primitive
for this one and a composition for the other, so this file does too. -/
def pow : UInt8 := 9

/-- Comparisons, numbered apart from the value verbs because they are a separate engine with a
separate result shape — a bitmap whatever the operands were. -/
def eq : UInt8 := 0
def ne : UInt8 := 1
def lt : UInt8 := 2
def le : UInt8 := 3
def gt : UInt8 := 4

/-- A comparison of two booleans run by the bit engine is this plus its code, a byte of each operand
at a time: widening the pair to `int` first was 33% of `differ` on a boolean column. -/
def bitCmp : UInt8 := 16

/-- Monadic verbs the engine answers directly. The nine float maps share `neg` and `abs`'s op space
because they share their engine; they are claimed at `f64` alone, q answering a **float** whatever
the argument's type — `sqrt 4e` is `2f` and `sqrt "a"` is `9.848858`, measured. -/
def neg : UInt8 := 0
def abs : UInt8 := 1
def sqrt : UInt8 := 2
def exp : UInt8 := 3
def log : UInt8 := 4
def sin : UInt8 := 5
def cos : UInt8 := 6
def tan : UInt8 := 7
def asin : UInt8 := 8
def acos : UInt8 := 9

/-- Operand shapes. An atom is passed as a one-element payload and read at index 0. -/
def vv : UInt8 := 0
def va : UInt8 := 1
def av : UInt8 := 2

/-- Bytes per element. -/
def width (cls : UInt8) : Nat :=
  if cls == u8 then 1 else if cls == i16 then 2
  else if cls == i32 || cls == f32 then 4 else 8

/-- Element `i` of a dense payload, as raw bits. A read past the end answers `0`, the convention
`Column.bitsAt` sets and for its reason: the caller is bounded by the count. -/
def elem (cls : UInt8) (x : ByteArray) (i : Nat) : UInt64 :=
  Column.bitsAt x (i * width cls) (width cls)

/-- The pair of operand indices a shape reads at element `i`. -/
def shapeIdx (shape : UInt8) (i : Nat) : Nat × Nat :=
  if shape == vv then (i, i) else if shape == va then (i, 0) else (0, i)

/-- Raw bits read as the signed value q stores at that class. `byte` and `char` are q's only
unsigned fixed-width types and zero-extend; everything else sign-extends, which is what puts q's
null — the minimum of the type — below every other element under a plain comparison. -/
def signed (cls : UInt8) (v : UInt64) : Int64 :=
  if cls == u8 then v.toUInt8.toUInt64.toInt64
  else if cls == i16 then v.toUInt16.toInt16.toInt64
  else if cls == i32 then v.toUInt32.toInt32.toInt64
  else v.toInt64

/-- q's `0n` with its **sign bit cleared**, at both float widths; the null itself is
`Rel.nanBits`. `1-0n` is `0x7ff8000000000000` and `0n-1` is `0xfff8000000000000` — q subtracts by
negating and adding, so a null on the right of `-` comes back positive. Measured at `real` too:
`1e-0Ne` is `0x7fc00000`. -/
def pnan64 : UInt64 := 0x7ff8000000000000
def pnan32 : UInt32 := 0x7fc00000

def ord64 (x y : UInt64) : Ordering :=
  if Bits.f64IsNaN x then (if Bits.f64IsNaN y then .eq else .lt)
  else if Bits.f64IsNaN y then .gt
  else
    let a := Float.ofBits x
    let b := Float.ofBits y
    if a < b then .lt else if b < a then .gt else .eq

def ord32 (x y : UInt32) : Ordering :=
  if Bits.f32IsNaN x then (if Bits.f32IsNaN y then .eq else .lt)
  else if Bits.f32IsNaN y then .gt
  else
    let a := Float32.ofBits x
    let b := Float32.ofBits y
    if a < b then .lt else if b < a then .gt else .eq

/-- The integral value verbs. Nothing wraps here: the caller writes the result back at the class's
own width and *that* truncation is q's wrap, so `2147483647i+1i` is `0Ni` without this saying so.

`&` and `|` need no null case — q's null is the least value of the type, so a signed minimum already
answers `0N&1` with `0N`, measured. `^` reads only its right operand's null: `0N^1` is `1` and
`1^0N` is `1`. -/
def intStep (op : UInt8) (nul x y : Int64) : Int64 :=
  if op == add then (if x == nul || y == nul then nul else x + y)
  else if op == sub then (if x == nul || y == nul then nul else x - y)
  else if op == mul then (if x == nul || y == nul then nul else x * y)
  else if op == fill then (if y == nul then x else y)
  else if op == lesser then (if x < y then x else y)
  else if op == greater then (if y < x then x else y)
  -- q divides toward *minus infinity* and takes the matching remainder: measured, `-7 div 2` is
  -- `-4` and `-7 mod 3` is `2`, which is `Int.fdiv` and `Int.fmod`. A zero divisor is `0N` at both
  -- and is tested here, ahead of the machine divide, which traps on it rather than answering.
  else if op == idiv || op == imod then
    (if x == nul || y == nul || y == 0 then nul
     else Int64.ofInt (if op == idiv then Int.fdiv x.toInt y.toInt else Int.fmod x.toInt y.toInt))
  else panic! s!"intStep: verb {op} has no integral case; `%` answers a float at every operand type"

/-- The `float`-width value verbs, over raw bits. A null operand is answered before any conversion,
which is what keeps a payload out of `Float.ofBits` — it rewrites q's `0n` to `0x7ff8…` and so
corrupts every null. `^` and the two extremes read the null themselves rather than short-circuiting:
`0n^1f` is `1f` while `0n&1f` is `0n`. -/
def f64Step (op : UInt8) (x y : UInt64) : UInt64 :=
  if op == fill then (if Bits.f64IsNaN y then x else y)
  else if op == lesser then (if ord64 x y == .gt then y else x)
  else if op == greater then (if ord64 x y == .lt then y else x)
  -- a NaN operand comes back **as it is**, the left one first, and `-` negates its right operand
  -- before choosing because that is how q subtracts: measured, `1f-0n` is `0x7ff8…` where `0n-1f`
  -- and `0n*1f` are `0xfff8…`, and once a positive NaN is in play `(1f-0n)*0n` is positive while
  -- `0n*(1f-0n)` is negative. Two constants cannot say that; the operand's own bits can.
  else if Bits.f64IsNaN x then x
  else if Bits.f64IsNaN y then (if op == sub then y ^^^ 0x8000000000000000 else y)
  else
    let a := Float.ofBits x
    let b := Float.ofBits y
    -- `div` and `mod` floor the quotient and answer a null wherever that floor is not a `long`,
    -- which is `floorStep`'s bound and the same two constants: `9.2e18 div 1.0` is itself where
    -- `1.0 div 0.0` and `1e300 mod 1.0` are not. The two verbs answer *different* nulls there,
    -- `Eval.divModAtoms` records which and why.
    let f := (a / b).floor
    let outside := f ≤ Float.ofBits 0xc3e0000000000000 || Float.ofBits 0x43e0000000000000 ≤ f
    let z := (if op == add then a + b else if op == sub then a - b
              else if op == mul then a * b
              else if op == idiv then f
              else if op == imod then a - b * f
              else if op == pow then a ^ b
              else a / b).toBits
    if op == idiv && outside then Rel.nanBits
    else if op == imod && outside then pnan64
    else if Bits.f64IsNaN z then Rel.nanBits else z

/-- The `real` width, which differs from `f64Step` only in the null patterns and the conversion. -/
def f32Step (op : UInt8) (x y : UInt32) : UInt32 :=
  if op == fill then (if Bits.f32IsNaN y then x else y)
  else if op == lesser then (if ord32 x y == .gt then y else x)
  else if op == greater then (if ord32 x y == .lt then y else x)
  else if Bits.f32IsNaN x then x
  else if Bits.f32IsNaN y then (if op == sub then y ^^^ 0x80000000 else y)
  else
    let a := Float32.ofBits x
    let b := Float32.ofBits y
    let f := (a / b).floor
    let outside := f.toFloat ≤ Float.ofBits 0xc3e0000000000000 ||
      Float.ofBits 0x43e0000000000000 ≤ f.toFloat
    let z := (if op == add then a + b else if op == sub then a - b
              else if op == mul then a * b
              else if op == idiv then f
              else if op == imod then a - b * f
              else if op == pow then (a.toFloat ^ b.toFloat).toFloat32
              else a / b).toBits
    if op == idiv && outside then Rel.nanBits32
    else if op == imod && outside then pnan32
    else if Bits.f32IsNaN z then Rel.nanBits32 else z

/-- One element of a value verb, at whichever family the class belongs to. -/
def valStep (op cls : UInt8) (nul x y : UInt64) : UInt64 :=
  if cls == f64 then f64Step op x y
  else if cls == f32 then (f32Step op x.toUInt32 y.toUInt32).toUInt64
  else (intStep op (signed i64 nul) (signed cls x) (signed cls y)).toUInt64

/-- One bit of a comparison. The integral classes compare their sign-extended payloads, which is
q's order for every type but `char`: there the null is the blank and q goes on ordering it by its
byte, which is what zero-extending a `u8` gives. -/
def cmpStep (op cls : UInt8) (x y : UInt64) : Bool :=
  let o :=
    -- q's comparison tolerance, `QAtom.tolerant`, at `f64` alone: two reals are never that close
    if cls == f64 then
      let o := ord64 x y
      if o != .eq && QAtom.tolerant (Float.ofBits x) (Float.ofBits y) then .eq else o
    else if cls == f32 then ord32 x.toUInt32 y.toUInt32
    else compare (signed cls x) (signed cls y)
  if op == eq then o == .eq else if op == ne then o != .eq
  else if op == lt then o == .lt else if op == le then o != .gt
  else if op == gt then o == .gt else o != .lt

/-- One bit of a value verb at `bits`. Only three verbs reach it: `&` on two booleans is their
minimum, which is `and`; `|` is `or`; and `^` copies its right operand whole, measured — `01b^10b`
is `10b` — booleans having no null to fill. `+ - * %` never arrive, q answering them at `int` or
`float` from a boolean pair, so the class the payload is read at is not `bits` there. A comparison
arrives as `bitCmp` plus its code and is `cmpStep`'s on the two bits. -/
def bitStep (op : UInt8) (x y : Bool) : Bool :=
  if op ≥ bitCmp then cmpStep (op - bitCmp) u8 (if x then 1 else 0) (if y then 1 else 0)
  else if op == lesser then x && y
  else if op == greater then x || y
  else if op == fill then y
  else panic! s!"bitStep: verb {op} has no boolean case; `+ - * %` widen a boolean pair first"

/-- One element of `neg` or `abs`. `neg` at a float width flips the sign bit rather than subtracting
from zero — measured, `neg 0f` is `-0f` where `0f-0f` is `0f`, and `neg 0n` is `0x7ff8…` — and `abs`
clears the same bit. At an integral width `abs` would need no null case of its own, q's null being
the most negative value and negating it wrapping back onto itself; the test is written anyway
because `neg` needs it and one branch serves both. -/
def monFloat (op : UInt8) : Float → Float :=
  if op == sqrt then Float.sqrt else if op == exp then Float.exp
  else if op == log then Float.log else if op == sin then Float.sin
  else if op == cos then Float.cos else if op == tan then Float.tan
  else if op == asin then Float.asin else if op == acos then Float.acos
  else Float.atan

def monStep (op cls : UInt8) (nul v : UInt64) : UInt64 :=
  if op != neg && op != abs then
    if cls != f64 then
      panic! s!"monStep: verb {op} is a float map, claimed at f64 alone, not at class {cls}"
    -- a null argument answers `0n` whichever map it is, its payload never read; out of *domain*
    -- the answer is `0n` too, except that the two arc functions clear the sign bit — measured,
    -- `asin 2` and `acos -0w` are `0x7ff8…` where `sqrt -1`, `log -1` and `tan 0w` are `0xfff8…`
    else if Bits.f64IsNaN v then Rel.nanBits
    else
      let y := (monFloat op (Float.ofBits v)).toBits
      if Bits.f64IsNaN y then (if op == asin || op == acos then pnan64 else Rel.nanBits) else y
  else if cls == f64 || cls == f32 then
    let sign : UInt64 := if cls == f64 then 0x8000000000000000 else 0x80000000
    if op == neg then v ^^^ sign else v &&& (sign - 1)
  else
    let k := signed i64 nul
    let x := signed cls v
    if x == k then k.toUInt64
    else if op == neg then (0 - x).toUInt64
    else if x < 0 then (0 - x).toUInt64 else x.toUInt64

/-- One element of monadic `_` at a float width, which alone answers at another class: both widths
floor to `long`. Out of range the answer is `0N` rather than the saturation a cast would give —
measured, `floor 9.3e18`, `floor 0w` and `floor 0n` are all `0N` — and the bound is tested on the
floored value, which is `QLean/Eval/Mon.lean`'s `floorFloats` exactly, so the two agree at the
boundary rather than nearly. -/
def floorStep (cls : UInt8) (v : UInt64) : Int64 :=
  let isNull := if cls == f32 then Bits.f32IsNaN v.toUInt32 else Bits.f64IsNaN v
  if isNull then Int64.minValue
  else
    let x := if cls == f32 then (Float32.ofBits v.toUInt32).toFloat else Float.ofBits v
    let f := x.floor
    if f ≤ Float.ofBits 0xc3e0000000000000 || Float.ofBits 0x43e0000000000000 ≤ f then
      Int64.minValue
    else if f < Float.ofBits 0 then -(-f).toUInt64.toInt64 else f.toUInt64.toInt64

/-- One element of the promotion. The null is remapped rather than converted, which is what makes
`0Nh+1h` come out `0Ni` and `0N%2` come out `0n`; `nulIn` is the source's null *as the calling verb
reads it*, so `^` passes the char blank and arithmetic passes `noNull`.

`nulOut` is the pattern the null lands on at a **float** target too, and not only at an integer one.
It is the result type's null everywhere but the right operand of `-`, where the engine flips a NaN's
sign and `valPayload` hands it the opposite one so that the flip lands on q's answer. -/
def widenStep (dst : UInt8) (nulIn nulOut : Int64) (v : Int64) : UInt64 :=
  if dst == f64 then
    (if v == nulIn then nulOut.toUInt64 else
      let b := (Float.ofInt v.toInt).toBits
      if Bits.f64IsNaN b then Rel.nanBits else b)
  else if dst == f32 then
    (if v == nulIn then nulOut.toUInt64 else
      (let b := (Float.ofInt v.toInt).toFloat32.toBits
       if Bits.f32IsNaN b then Rel.nanBits32 else b).toUInt64)
  else (if v == nulIn then nulOut else v).toUInt64

/-- Whether a source element is q's *missing* value. `nulIn` is `verbNull false`, so `byte`,
`boolean` and `char` are told `noNull`: `0x00` is a byte like any other and the blank is the byte
32, measured — `` `long$0x00 `` is `0` and `` `long$" " `` is `32`. -/
def castMissing (src : UInt8) (nulIn : Int64) (v : UInt64) : Bool :=
  if src == f64 then Bits.f64IsNaN v
  else if src == f32 then Bits.f32IsNaN v.toUInt32
  else signed src v == nulIn

/-- A source element as a `Float`, which is what a float target writes and what an integral target
rounds. -/
def castFloat (src : UInt8) (v : UInt64) : Float :=
  if src == f64 then Float.ofBits v
  else if src == f32 then (Float32.ofBits v.toUInt32).toFloat
  else Float.ofInt (signed src v).toInt

/-- q's `0W` and `-0W` at an integral class, which is what a cast saturates to. `u8` is `byte` and
`char`, which have no null to stay clear of and wrap instead, so their bounds are the whole range
and the truncation below does the work. -/
def castBounds (dst : UInt8) : Int64 × Int64 :=
  if dst == i16 then (-32767, 32767)
  else if dst == i32 then (-2147483647, 2147483647)
  else (Int64.minValue + 1, Int64.maxValue)

/-- What a cast writes for a missing source, as raw bits at `dst`. `u8` answers `0` rather than a
null of its own — `Eval.castNull`'s rule, and the reason `` `char$0N `` is `"\000"`. -/
def castNul (dst : UInt8) : UInt64 :=
  if dst == f64 then Rel.nanBits else if dst == f32 then Rel.nanBits32.toUInt64
  else if dst == i16 then 0x8000 else if dst == i32 then 0x80000000
  else if dst == i64 then 0x8000000000000000 else 0

/-- The integer a float source casts to: q rounds half **away from zero** — `` `long$2.5 `` is `3`
and `` `long$-2.5 `` is `-3`, measured — and then saturates at the `long` range before the target's
own narrowing, which is `Eval.clampLong`. The two constants are `-2^63` and `2^63` as doubles. -/
def castRound (x : Float) : Int64 :=
  let r := x.round
  if r ≤ Float.ofBits 0xc3e0000000000000 then Int64.minValue + 1
  else if Float.ofBits 0x43e0000000000000 ≤ r then Int64.maxValue
  else if r < Float.ofBits 0 then -(-r).toUInt64.toInt64 else r.toUInt64.toInt64

/-- One element of `$`. -/
def castStep (src dst : UInt8) (nulIn : Int64) (v : UInt64) : UInt64 :=
  if castMissing src nulIn v then castNul dst
  else if dst == f64 then
    let b := (castFloat src v).toBits
    if Bits.f64IsNaN b then Rel.nanBits else b
  else if dst == f32 then
    let b := (castFloat src v).toFloat32.toBits
    (if Bits.f32IsNaN b then Rel.nanBits32 else b).toUInt64
  else
    let n := if src == f64 || src == f32 then castRound (castFloat src v) else signed src v
    let (lo, hi) := castBounds dst
    if dst == u8 then n.toUInt64 &&& 0xff
    else (if n < lo then lo else if hi < n then hi else n).toUInt64

/-- The source element a promotion reads, sign-extended, with a boolean bitmap read a bit at a
time. A `real` source is the one class this cannot answer for, and no verb asks: nothing in q widens
a real onto an integer. -/
def widenRead (src : UInt8) (x : ByteArray) (i : Nat) : Int64 :=
  if src == bits then (if Column.bitAt x i then 1 else 0) else signed src (elem src x i)

/-- q's value verbs over two dense payloads. -/
@[extern "qlean_ew_val"]
def val (op cls shape : UInt8) (nul : Int64) (a b : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    let (ia, ib) := shapeIdx shape i
    Column.pushBits acc (valStep op cls nul.toUInt64 (elem cls a ia) (elem cls b ib)) (width cls)

/-- q's six comparisons, answering the `Column.bits` payload one bit per element. The bits above `n`
in the last byte stay `0`, which `QLean/Value.lean` requires of every boolean payload: `~` compares
payloads, and trailing garbage would make equal vectors compare unequal. -/
@[extern "qlean_ew_cmp"]
def cmp (op cls shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray :=
  (List.range ((n.toNat + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte j =>
      let i := k * 8 + j
      let (ia, ib) := shapeIdx shape i
      if i < n.toNat && cmpStep op cls (elem cls a ia) (elem cls b ib) then
        byte ||| (1 <<< j.toUInt8)
      else byte)

/-- The six comparisons at `long` against an atom, read off the encoded form: a block whose whole
`[base, maxv]` range falls one side of `v` is filled from its metadata without a residual being
touched. No null case, and that is not an omission — q's `0N` is the least `long` there is and the
signed comparison already puts it there, `0N<5` and `0N=0N` both being `1b`, measured.

**Every column is claimed; what the range decides is the cost, not the answer.** A block whose range
straddles `v` is *deep* and its residuals are read, and nothing above chooses between the two — so
the condition to hold in mind is how many blocks are deep, which no type or shape test can see.
Measured at a million longs: `xl<500000`, one deep block in 977, 2.3us; `xg<500`, all 977 deep, 12us.
The C splits the deep blocks across the worker pool and counts *them* rather than the elements to
decide whether to, which is what keeps the first figure where it is. -/
@[extern "qlean_coc_mask_cmp"]
def foRCmp (op : UInt8) (v : Int64) (metadata pack : @& ByteArray) (n : USize) : ByteArray :=
  cmp op i64 va (Coc.decode 8 metadata pack n) (Column.pushBits ByteArray.empty v.toUInt64 8) n

/-- `k + x`, and `k - x` when `neg`, at `long` on the encoded form: the answer is the same column
with every block's minimum moved by `k` — turned round, for `k - x`, the residuals with it — which
is 33 bytes a block against a pass over `n` elements, and it stays encoded for whatever runs next.

`none` is three refusals, all correctness rather than policy, and the dense path answers them. A
block whose minimum is `Int64.minValue` holds q's `0N`, which `1+0N` keeps a null where a shifted
base would make it an ordinary number; `k` being the null is that same case from the other side. A
minimum the shift lands *on* `Int64.minValue` makes a null, which the writer patches and a moved
frame does not hold. And
a shift that leaves `Int64` — q wraps there, measured — would leave `base` and `maxv` no longer the
block's own extremes, which every kernel that skips a whole block reads them as.

**For `k + x` the C is not these bytes, and `bsum` is the one section it parts on.** `k - x` turns
the residuals round, so it goes through the one writer, `qlean_coc_encode_fill`, and is these bytes
exactly. This body re-encodes, so it always answers metadata carrying the per-block sums; `k + x`
moves the metadata it was given and keeps its sums only where they still say what they said —
`rust/src/coc.rs`'s `coc_sums_ok`. Handed metadata that carries no sums, which
is what `Column.appendFoR` leaves, it answers none where this answers the sums it computed. Every
other section, the pack and therefore `Column.atoms` are the same bytes, and the sums are a cache no
denotation reads — `Kernel.matchColumn` takes byte equality as a fast `true` and otherwise compares
payloads. `QLean/Kernel/ElementwiseTest.lean`'s `shiftSections` pins both directions. -/
@[extern "qlean_coc_shift"]
def foRShift (neg : Bool) (k : Int64) (metadata pack : @& ByteArray) (n : USize) :
    Option (ByteArray × ByteArray) :=
  let step := fun x => if neg then k.toInt - x else x + k.toInt
  let xs := (Coc.elems metadata pack n).map (·.toInt64.toInt)
  if k == Int64.minValue || xs.any (fun x => x == Int64.minValue.toInt ||
      step x ≤ Int64.minValue.toInt || Int64.maxValue.toInt < step x) then none
  else
    -- the answer is the dense engine's, re-encoded: a shift moves no block boundary, no width and
    -- no offset, so the C's metadata and this hold the same base, maxv, off and width
    let dense := Coc.decode 8 metadata pack n
    let atom := Column.pushBits ByteArray.empty k.toUInt64 8
    some (Coc.encode 8 (if neg then val sub i64 av Int64.minValue atom dense n
                        else val add i64 va Int64.minValue dense atom n))

/-- Whether an exact integer is still an `Int64`. The two value kernels below decline a block whose
extremes leave it: q wraps there, and a wrapped `base` is no longer the block's own minimum. -/
def inI64 (x : Int) : Bool := Int64.minValue.toInt ≤ x && x ≤ Int64.maxValue.toInt

/-- The six comparisons at `long` between two encoded vectors of the same count. The block grids line
up, both being `Column.blk` elements (`foRPairVV` declines two sizes), so block `b` of one meets block `b` of the other and a pair
whose `[base, maxv]` ranges do not overlap is decided whole — which is the whole of `xl<xd`. Where
they overlap, `base_a + res_a` is compared against `base_b + res_b`. No null case, for `foRCmp`'s
reason.

**Every pair of encoded operands is claimed, and the two branches are three orders of magnitude apart
per element.** `foRPairVV`'s conditions — both `.foR`, both at `i64`, equal counts — say only that
the kernel *answers*; what it costs is how many block pairs overlap, and no operand shape shows that.
Measured at a million longs: `xl<xd`, one deep block pair in 977, 2.3us; `xl<xl`, all 977 deep, 24us
against the 12us the dense engine takes on the same values *in cache*. Out of cache the sign turns
over — at 16M `xg<>yg` is 0.38ms here against 4.2ms dense, this reading a quarter of the bytes — so
the claim is right and it is the deep branch that had to be made to scale, which the C does by
splitting the deep blocks across the worker pool. -/
@[extern "qlean_coc_mask_cmp_vv"]
def foRCmpVV (op : UInt8) (ma pa mb pb : @& ByteArray) (n : USize) : ByteArray :=
  cmp op i64 vv (Coc.decode 8 ma pa n) (Coc.decode 8 mb pb n) n

/-- `x + y`, `x - y` and `x * y` at `long` between two encoded vectors of the same count: the answer's
base and maximum are the results' own extremes and its residual width is what their difference needs,
so it is a pass over the two packs and not over the two dense payloads.

`none` is `foRShift`'s two refusals read one operand at a time — a block whose minimum is
`Int64.minValue` holds q's `0N`, which `0N+1` and `0N*2` keep a null, and extremes that leave `Int64`
would leave `base` and `maxv` no longer the block's own. They are stated over the block extremes and
not over the elements because that is what the C can ask before it has read anything: `base_a+base_b`
can leave `Int64` where no element pair does, the two minima needing not fall at the same index.

`*` asks the **four corner products** instead of two combined extremes. A product is monotone in each
argument once the other's sign is fixed, so every `x*y` over `[base_a, maxv_a] × [base_b, maxv_b]`
lies between the least and the greatest corner, and corners that fit make every element fit. -/
@[extern "qlean_coc_val_vv"]
def foRValVV (op : UInt8) (ma pa mb pb : @& ByteArray) (n : USize) :
    Option (ByteArray × ByteArray) :=
  let ok := Column.nblk ma == Column.nblk mb && (List.range (Column.nblk ma)).all fun b =>
    let ba := (Column.baseAt ma b).toInt64.toInt
    let xa := (Column.maxvAt ma b).toInt64.toInt
    let bb := (Column.baseAt mb b).toInt64.toInt
    let xb := (Column.maxvAt mb b).toInt64.toInt
    ba != Int64.minValue.toInt && bb != Int64.minValue.toInt &&
      (if op == mul then [ba * bb, ba * xb, xa * bb, xa * xb].all inI64
       else if op == sub then inI64 (ba - xb) && inI64 (xa - bb)
       else inI64 (ba + bb) && inI64 (xa + xb))
  if ok then
    -- the answer is the dense engine's, re-encoded, byte for byte: the C computes each block's
    -- extremes and its width by the encoder's own rule, block by block
    some (Coc.encode 8 (val op i64 vv Int64.minValue
      (Coc.decode 8 ma pa n) (Coc.decode 8 mb pb n) n))
  else none

/-- `x <op> y` between two encoded vectors of the same count, answering the **dense** payload `val`
answers: one block of each side is restored into a buffer that stays in L1 and the same verb table
runs on it, so neither operand is decoded whole.

This is where the verbs `foRValVV` cannot answer encoded go — `&`, `|` and `^`, which have no rule
for the answer's own block extremes cheaper than computing them — and where `+`, `-` and `*` go on
the blocks it declines. `cls` is the integral class both operands and the result sit at; a pack holds
integers, so the float classes never reach here. -/
@[extern "qlean_coc_ew_val"]
def foRVal (op cls : UInt8) (nul : Int64) (ma pa mb pb : @& ByteArray) (n : USize) : ByteArray :=
  val op cls vv nul (Coc.decode (width cls).toUSize ma pa n)
    (Coc.decode (width cls).toUSize mb pb n) n

/-- `x <op> k` and `k <op> x` between an encoded vector and an atom, answering the dense payload
`val` answers: the vector is restored a block at a time into a buffer that stays in L1 and the atom
is a fixed pointer, so the operand is never decoded whole.

The two shapes are one kernel because only one side has blocks — `shape` says which side of the
engine the atom stands on, and the engine broadcasts it as it does for a dense atom. This is where
`&`, `|` and `^` against an atom go, and where `x+k` and `x*k` go on a column `foRShift` and
`foRScale` decline. -/
@[extern "qlean_coc_ew_val_atom"]
def foRValAtom (op cls shape : UInt8) (nul : Int64) (metadata pack : @& ByteArray) (n : USize)
    (atom : @& ByteArray) : ByteArray :=
  let dense := Coc.decode (width cls).toUSize metadata pack n
  if shape == va then val op cls shape nul dense atom n else val op cls shape nul atom dense n

/-- `x * k` at `long` on the encoded form. Scaling is monotone, so a block's extremes are its own
scaled — the order turning round for a negative `k` — and the residuals scale with them. That is a
pass over the pack, unlike `x + k`, which leaves the residuals where they are; it is still an eighth
of the bytes the dense payload is at a residual width of eight bits.

`none` is `foRShift`'s refusals again: `k` or a block minimum being `Int64.minValue` is q's `x*0N`
and `0N*0`, both `0N`, measured, and a scaled extreme that leaves `Int64` is the other. -/
@[extern "qlean_coc_scale"]
def foRScale (k : Int64) (metadata pack : @& ByteArray) (n : USize) :
    Option (ByteArray × ByteArray) :=
  let ok := k != Int64.minValue && (List.range (Column.nblk metadata)).all fun b =>
    let base := (Column.baseAt metadata b).toInt64.toInt
    let maxv := (Column.maxvAt metadata b).toInt64.toInt
    base != Int64.minValue.toInt && inI64 (base * k.toInt) && inI64 (maxv * k.toInt)
  if ok then
    some (Coc.encode 8 (val mul i64 va Int64.minValue (Coc.decode 8 metadata pack n)
      (Column.pushBits ByteArray.empty k.toUInt64 8) n))
  else none

/-- `&`, `|` and `^` over two boolean bitmaps — the one value result that is not a dense payload,
and the reason `x within (lo;hi)` no longer boxes: the two comparisons it is built from already
reach `cmp`, and it was this last `&` between their bitmaps that fell to atoms. Both operands are
already `Column.bits`, so nothing widens and the C runs a byte at a time. The bits above `n` in the
last byte stay `0` for `cmp`'s reason. -/
@[extern "qlean_ew_bit"]
def bit (op shape : UInt8) (a b : @& ByteArray) (n : USize) : ByteArray :=
  (List.range ((n.toNat + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte j =>
      let i := k * 8 + j
      let (ia, ib) := shapeIdx shape i
      if i < n.toNat && bitStep op (Column.bitAt a ia) (Column.bitAt b ib) then
        byte ||| (1 <<< j.toUInt8)
      else byte)

/-- `neg` and `abs`, at the class the argument already occupies. -/
@[extern "qlean_ew_mon"]
def mon (op cls : UInt8) (nul : Int64) (x : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (monStep op cls nul.toUInt64 (elem cls x i)) (width cls)

/-- Monadic `_` at a float width. -/
@[extern "qlean_ew_floor"]
def floor (cls : UInt8) (x : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (floorStep cls (elem cls x i)).toUInt64 8

/-- q's `$` over a dense payload, from one class to another. -/
@[extern "qlean_ew_cast"]
def castTo (src dst : UInt8) (nulIn : Int64) (x : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (castStep src dst nulIn (elem src x i)) (width dst)

/-- Nanoseconds in one unit of each temporal code `Kernel.tickCode` hands out, and the one table
`Kernel.tickOf` reads too. Code `5` is `month`, which has no fixed length and goes through the
calendar instead. -/
def tickNanos (k : UInt8) : Int :=
  if k == 0 then 1 else if k == 1 then 1000000 else if k == 2 then 1000000000
  else if k == 3 then 60000000000 else 86400000000000

/-- The month, counted from 2000.01, holding the day `days` counts from 2000.01.01 — `daysOfFirst`'s
inverse as far as a month needs it. Shifted to 0000-03-01, where a four-hundred-year cycle starts and
February's length stops being the special case every other formulation has to carry. -/
def monthOfDays (days : Int) : Int :=
  let z := days + 730425
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let mp := (5 * (doe - (365 * yoe + yoe / 4 - yoe / 100)) + 2) / 153
  let m := mp + (if mp < 10 then 3 else -9)
  (era * 400 + yoe + (if m ≤ 2 then 1 else 0)) * 12 - 24000 + m - 1

/-- One element of a temporal operand re-counted in its result's unit, which is `Eval.intIn` and
`Eval.floatIn` on a whole column and `Eval.castTemporal` on one: `op` is the source's code times 16
plus the target's. The source is read as nanoseconds — a month at the first of its month, a `datetime`
through `$`'s rounding of its float days — and then floored into an integral target, wrapping at its
width, or divided in float into `datetime`. A `month` target is the day floored and then the calendar,
`tickNanos 5` being a day. A null answers `nulOut` before any of it. -/
def tickStep (op src dst : UInt8) (nulIn nulOut : Int64) (v : UInt64) : UInt64 :=
  if castMissing src nulIn v then nulOut.toUInt64 else
  let su := op >>> 4
  let u := tickNanos (op &&& 15)
  let ns : Int :=
    if src == f64 then (castRound (Float.ofBits v * 86400000000000.0)).toInt
    else if su == 5 then
      let m := (signed src v).toInt
      daysOfFirst (2000 + m / 12) (1 + m % 12) * 86400000000000
    else (signed src v).toInt * tickNanos su
  if dst == f64 then (Float.ofInt ns / Float.ofInt u).toBits
  else if op &&& 15 == 5 then (Int64.ofInt (monthOfDays (Int.fdiv ns u))).toUInt64
  else (Int64.ofInt (Int.fdiv ns u)).toUInt64

/-- `tickStep` over a payload. Not an export of its own: it is a chain stage, and a one-element
operand runs it as a one-stage chain. -/
def tick (op src dst : UInt8) (nulIn nulOut : Int64) (x : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (tickStep op src dst nulIn nulOut (elem src x i)) (width dst)

/-- `=` and `<>` between two columns over **one** dictionary: it is distinct, so two ids name one
symbol exactly when they are equal, and the ids are compared as they lie with no rank read. -/
@[extern "qlean_ew_eq_ids"]
def eqIds (op shape : UInt8) (ia ib : @& ByteArray) (w n : USize) : ByteArray :=
  cmp op i64 vv
    ((List.range n.toNat).foldl (init := ByteArray.empty) fun acc j =>
      Column.pushBits acc (Column.idAt ia w.toNat (shapeIdx shape j).1).toUInt64 8)
    ((List.range n.toNat).foldl (init := ByteArray.empty) fun acc j =>
      Column.pushBits acc (Column.idAt ib w.toNat (shapeIdx shape j).2).toUInt64 8)
    n

/-- An operand brought to the class its verb's result is at. `real` to `float` is written out rather
than converted so that the sign bit, which is what makes q's null the *negative* NaN, cannot be lost
to a platform's NaN handling. -/
@[extern "qlean_ew_widen"]
def widen (src dst : UInt8) (nulIn nulOut : Int64) (x : @& ByteArray) (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    let v :=
      if src == f32 then
        let b := (elem f32 x i).toUInt32
        if Bits.f32IsNaN b then ((b >>> 31).toUInt64 <<< 63) ||| pnan64
        else (Float32.ofBits b).toFloat.toBits
      else if src == f64 then elem f64 x i
      else widenStep dst nulIn nulOut (widenRead src x i)
    Column.pushBits acc v (width dst)

/-- The engines a stage may name. Mirrored as an `enum` in `rust/src/ew.rs`; the two lists are one
interface and cannot be changed apart. -/
def eVal : UInt8 := 0
def eCmp : UInt8 := 1
def eMon : UInt8 := 2
def eWiden : UInt8 := 3
def eBit : UInt8 := 4
def eFloor : UInt8 := 5
def eCast : UInt8 := 6
def eDecode : UInt8 := 7
-- 9 and 10 are the encoder stages `rust/src/ew.rs` appends itself and a program never names
def eTick : UInt8 := 11
/-- An interned column's ids at the lane `shape` (any `Column.laneWidth`), written at `cls`. -/
def eIds : UInt8 := 12
/-- `eIds`' inverse: a `cls` payload's elements written as ids at the lane `shape` (any
`Column.laneWidth`), so a chain answers an id payload at the width its domain needs, below a byte too. -/
def ePack : UInt8 := 13

/-- Where a stage reads an operand: below this an input payload, at or above it the answer of the
stage that many places along. Every stage writes its own slot, so a slot index *is* a stage index and
nothing has to allocate them. -/
def slot0 : UInt8 := 128

/-- One pass of a chain. `cls` and `shape` carry the source and target classes for `widen` and `$`,
which have neither a verb nor an operand shape, so that one record serves every engine.

`c` is a **third** operand code, and only `eAlp` names one: an ALP column is three payloads —
metadata, pack and the float sections beside them — where a `.foR` column is two. It rides in the
first of the two bytes the record already padded for the nulls' alignment, so a third slot costs the
wire nothing and `stageBytes` is what it was; a decode is one stage and not two because the three
payloads are one *view* — the scale needs `exp` and the patch needs `exc_*`, so neither half of a
split would be a decode, and a stage answers a payload rather than a view. -/
structure Stage where
  engine : UInt8
  op : UInt8 := 0
  cls : UInt8 := 0
  shape : UInt8 := 0
  a : UInt8 := 0
  b : UInt8 := 0
  c : UInt8 := 0
  nul : Int64 := 0
  nulOut : Int64 := 0
deriving Inhabited

/-- Bytes a stage occupies in a program. -/
def stageBytes : Nat := 24

/-- A stage as the C reads it: seven codes, a pad byte so the nulls are aligned, and the two nulls
little-endian. -/
def Stage.bytes (s : Stage) : ByteArray :=
  let head := ((((((ByteArray.empty.push s.engine).push s.op).push s.cls).push s.shape).push
    s.a).push s.b).push s.c |>.push 0
  Column.pushBits (Column.pushBits head s.nul.toUInt64 8) s.nulOut.toUInt64 8

/-- The stage `k` places into a program. -/
def stageAt (prog : ByteArray) (k : Nat) : Stage :=
  let o := k * stageBytes
  { engine := (Column.bitsAt prog o 1).toUInt8, op := (Column.bitsAt prog (o + 1) 1).toUInt8,
    cls := (Column.bitsAt prog (o + 2) 1).toUInt8, shape := (Column.bitsAt prog (o + 3) 1).toUInt8,
    a := (Column.bitsAt prog (o + 4) 1).toUInt8, b := (Column.bitsAt prog (o + 5) 1).toUInt8,
    c := (Column.bitsAt prog (o + 6) 1).toUInt8,
    nul := (Column.bitsAt prog (o + 8) 8).toInt64,
    nulOut := (Column.bitsAt prog (o + 16) 8).toInt64 }

/-- A chain of element-wise passes over one column, answering the last stage's payload.

Spec: stage `k` is its engine applied to the payloads its two source codes name, at the whole count
`n`; `rust/src/ew.rs` answers the same list a tile at a time. -/
@[extern "qlean_ew_chain"]
def chain (prog : @& ByteArray) (inputs : @& Array ByteArray) (n : USize) : ByteArray :=
  let k := prog.size / stageBytes
  let outs := (List.range k).foldl (init := (#[] : Array ByteArray)) fun outs j =>
    let st := stageAt prog j
    let src (c : UInt8) : ByteArray :=
      if c < slot0 then inputs[c.toNat]! else outs[(c - slot0).toNat]!
    outs.push <|
      if st.engine == eVal then val st.op st.cls st.shape st.nul (src st.a) (src st.b) n
      else if st.engine == eCmp then cmp st.op st.cls st.shape (src st.a) (src st.b) n
      else if st.engine == eMon then mon st.op st.cls st.nul (src st.a) n
      else if st.engine == eWiden then widen st.cls st.shape st.nul st.nulOut (src st.a) n
      else if st.engine == eBit then bit st.op st.shape (src st.a) (src st.b) n
      else if st.engine == eFloor then floor st.cls (src st.a) n
      else if st.engine == eCast then castTo st.cls st.shape st.nul (src st.a) n
      else if st.engine == eTick then tick st.op st.cls st.shape st.nul st.nulOut (src st.a) n
      else if st.engine == eIds then
        Column.packIds (8 * width st.cls) n.toNat (Column.idAt (src st.a) st.shape.toNat)
      else if st.engine == ePack then
        Column.packIds st.shape.toNat n.toNat fun i => (elem st.cls (src st.a) i).toNat
      else if st.engine == eDecode then Coc.decode (width st.cls).toUSize (src st.a) (src st.b) n
      -- the blob's own flag and not `st.cls`, which is what `rust/src/coc.rs`'s `cocf_load_blk` reads; the
      -- two agree because `operandSource` refuses a column whose blob and type disagree
      else if Column.alpF32 (src st.c) then Coc.alpDecode32 (src st.a) (src st.b) (src st.c) n
      else Coc.alpDecode64 (src st.a) (src st.b) (src st.c) n
  outs[k - 1]!

/-- The same chain, and its answer in the Frame-of-Reference form `Coc.encode` puts it in. Stated as
that composition because it is the equation the pair has to satisfy; the C never materialises the
dense payload named in the middle of it.

`rust/src/c.rs`'s `QLEAN_TILE` is `BLK`, so a chain's tile is exactly one encoded block: the tile the last
stage wrote is the block the encoder wants, and the chain runs as the encoder's source rather than
into a column between them. What that saves, at 64M elements: every chain whose answer is an integral
type measured 52.7 ms and every one whose answer is a float 23.8 ms, whatever the verb — `floor xf`
and `` `long$xf `` to the microsecond — the difference being 512 MB of dense bytes written and then
read twice, to size the blocks and to pack them. The encoder's two passes stay two, so the chain runs
twice; its stages are element-wise maps and the arithmetic is free next to that traffic. -/
@[extern "qlean_ew_chain_enc"]
def chainEnc (prog : @& ByteArray) (inputs : @& Array ByteArray) (n : USize) (width : USize) :
    ByteArray × ByteArray :=
  Coc.encode width (chain prog inputs n)

/-- A chain under construction: the stages named so far and the payloads they read. -/
structure Build where
  stages : Array Stage := #[]
  inputs : Array ByteArray := #[]
deriving Inhabited

/-- The program a build describes, with `last` as the stage whose answer is the result. -/
def Build.prog (b : Build) (last : Stage) : ByteArray :=
  ((b.stages.push last).map Stage.bytes).foldl (init := ByteArray.empty) (· ++ ·)

/-- That program's answer as the dense payload it computes. -/
def Build.run (b : Build) (last : Stage) (n : USize) : ByteArray :=
  chain (b.prog last) b.inputs n

/-- And in the Frame-of-Reference form, which is what a result at a type `Column.encodes` becomes. -/
def Build.runEnc (b : Build) (last : Stage) (n : USize) (width : USize) : ByteArray × ByteArray :=
  chainEnc (b.prog last) b.inputs n width

end Rel.Kernel.Ew

namespace Rel.Kernel

/-- The raw bits q's null occupies, and the one table that says so. `none` at `byte` and `boolean`,
which have none, and at the two types with no dense payload. -/
def nullBits : QAtomicType → Option UInt64
  | .short => some 0x8000
  | .int | .month | .date | .minute | .second | .time => some 0x80000000
  | .long | .timestamp | .timespan => some 0x8000000000000000
  | .char => some 32
  | .real => some 0xffc00000
  | .float | .datetime => some 0xfff8000000000000
  | _ => none

/-- A one-element payload holding those bits at `cls`, which is how an atom operand reaches a
kernel and how `null` and `not` reach the comparison engine. -/
def atomBytes (cls : UInt8) (v : UInt64) : ByteArray :=
  Column.pushBits ByteArray.empty v (Ew.width cls)

end Rel.Kernel


namespace Rel.Kernel.Ew
def ge : UInt8 := 5
def eAlp : UInt8 := 8

/-- A payload the chain reads whole, and the source code a stage names it by. -/
def Build.input (b : Build) (x : ByteArray) : Build × UInt8 :=
  ({ b with inputs := b.inputs.push x }, b.inputs.size.toUInt8)

/-- A stage, and the source code the next stage names its answer by. -/
def Build.add (b : Build) (s : Stage) : Build × UInt8 :=
  ({ b with stages := b.stages.push s }, slot0 + b.stages.size.toUInt8)

end Rel.Kernel.Ew

namespace Rel.Kernel

/-- The storage class a type's dense payload is read at. `none` where there is no dense fixed-width
payload the kernels are instantiated over: `symbol` has no fixed width. -/
def clsOf : QAtomicType → Option UInt8
  | .boolean => some Ew.bits
  | .byte | .char => some Ew.u8
  | .short => some Ew.i16
  | .int | .month | .date | .minute | .second | .time => some Ew.i32
  | .long | .timestamp | .timespan => some Ew.i64
  | .real => some Ew.f32
  | .float | .datetime => some Ew.f64
  | .symbol | .general => none

/-- Whether `Ew.widen` can bring `t` to `cls`. It promotes upward only — nothing already a float
reaches an integer target, and nothing at all reaches `u8` or `i16` — and asking it for anything
else aborts rather than answering, so a dispatch has to test this instead of discovering it. These
four targets are the four cases `rust/src/ew.rs`'s `ew_widen_run` has. Written as the reachable
pairs rather than as a width comparison, `Ew.width` answering 8 for a bitmap. -/
def promotable (t : QAtomicType) (cls : UInt8) : Bool :=
  match clsOf t with
  | some src =>
    let integral := src == Ew.bits || src == Ew.u8 || src == Ew.i16 || src == Ew.i32 || src == Ew.i64
    if src == cls || cls == Ew.f64 then true
    else if cls == Ew.f32 || cls == Ew.i64 then integral
    else if cls == Ew.i32 then src == Ew.bits || src == Ew.u8 || src == Ew.i16
    else false
  | none => false

/-- An operand's dense payload at `dst`, decoding a `.foR` payload and unpacking a boolean bitmap on
the way. Two whole-vector C calls at worst, which is what section 3.1 permits.

Which of the two class engines runs is `promotable`: upward it is `Ew.widen`, which remaps the null
rather than converting it and is the one `-` hands a flipped NaN to; every other direction is
`Ew.castTo`, q's `$` and the rule `convertible` states. -/
def operandAt (t : QAtomicType) (m : USize) (e : Ext.Enc X) (dst : UInt8) (nulIn nulOut : Int64) (n : USize) :
    Option ByteArray := do
  let src ← clsOf t
  if src == dst then Enc.bytesOf t m e
  else
    let raw ← match e with
      | .bits bs => if src == Ew.bits then some bs else none
      | _ => Enc.bytesOf t m e
    some (if promotable t dst then Ew.widen src dst nulIn nulOut raw n
          else Ew.castTo src dst nulIn raw n)

/-- The same operand, as the **stages of a chain** that bring it to `dst`: the decode a `.foR`
column needs and the promotion a class that is not the engine's needs, each a tile at a time rather
than a pass over the column. `operandAt` above is what one of these stages does whole.

An operand whose own count is not the chain's is the atom side of `va`/`av`, and it is brought to
`dst` by `operandAt` before the chain instead. Every stage of a chain runs at the chain's count, and
promoting a one-element payload at the vector's count would read past the end of it — the same rule
`mapPass` and `zipPass` have always followed, now with a boundary to state it at. -/
def operandSource (b : Ew.Build) (t : QAtomicType) (m : USize) (e : Ext.Enc X) (dst : UInt8)
    (nulIn nulOut : Int64) (n : USize) (tk : Option UInt8 := none) : Option (Ew.Build × UInt8) := do
  let src ← clsOf t
  -- `tk` is a unit conversion (`tickIn`), which reads the source class itself and so stands in
  -- for the promotion rather than following it: a `datetime` is re-counted from its float days
  let tickAt (a : UInt8) (op : UInt8) : Ew.Stage :=
    { engine := Ew.eTick, op, cls := src, shape := dst, a, nul := nulIn, nulOut }
  if m != n then
    some (b.input (← match tk with
      | some op => (Enc.bytesOf t m e).map fun x =>
          let (one, a) := ({} : Ew.Build).input x
          one.run (tickAt a op) m
      | none => operandAt t m e dst nulIn nulOut m))
  else
    let (b, raw) ← match e with
      | .bytes x => some (b.input x)
      -- the decode is a stage, so the restored block is the tile the engine reads and is never
      -- written out; the width test is what makes `Ew.width src` the width `Enc.bytesOf` decodes at
      | .foR metadata pack =>
        if t.width == some (Ew.width src) then
          let (b, mi) := b.input metadata
          let (b, pi) := b.input pack
          some (b.add { engine := Ew.eDecode, cls := src, a := mi, b := pi })
        else none
      | .bits x => if src == Ew.bits && src != dst then some (b.input x) else none
      -- the float half of the same stage, and the blob's own width has to agree with the type's:
      -- the scale and the exceptions are read at `alpF32`, so a blob that disagrees is a malformed
      -- column and declines here rather than being decoded at one width and written at the other
      | .alp metadata pack a =>
        if t.width == some (Ew.width src) && Column.alpF32 a == (src == Ew.f32) then
          let (b, mi) := b.input metadata
          let (b, pi) := b.input pack
          let (b, ai) := b.input a
          some (b.add { engine := Ew.eAlp, cls := src, a := mi, b := pi, c := ai })
        else none
      | _ => none
    if let some op := tk then some (b.add (tickAt raw op))
    else if src == dst then some (b, raw)
    else if promotable t dst then
      some (b.add { engine := Ew.eWiden, cls := src, shape := dst, a := raw,
                    nul := nulIn, nulOut := nulOut })
    -- the narrowing half of the same stage, `operandAt`'s second branch as a tile at a time
    else some (b.add { engine := Ew.eCast, cls := src, shape := dst, a := raw, nul := nulIn })

end Rel.Kernel
