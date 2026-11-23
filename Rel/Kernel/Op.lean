module

public import Rel.Kernel.Cast

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The finite set of operations `scan` runs (design §4): a closed enumeration rather than a Lean closure, because the
Rust side can only execute a fixed set, and the Lean body of a kernel interprets it with `Op.eval`.

A word is raw 64-bit storage read the way `Rel.Kernel.Ew` reads it: the integer ops read it as a signed `Int64`
(`Ew.signed` at `i64`: two's complement), wrapping at 64 bits — the caller writes the result back at the class's own
width and that truncation is the narrower wrap; the `f…` ops read it as an IEEE `f64` (`Float.ofBits`) and write
`Float.toBits`. A boolean is the word `0` or `1`. `eval acc x` is one scan step: `acc` is the running value, `x` the
current element. -/

namespace Rel.Kernel

/-- One scan step. Integer: `add sub mul div mod min max neg abs`; boolean/compare: `eq ne lt le gt ge and or not`;
`first` keeps the accumulator and `last` replaces it (`Scan.Verb.fills`' step: the driver skips the nulls); float:
the `f` ops; `f32to64` widens an `f32` word to an `f64` word. `div`/`mod` floor, as q does (`Ew.intStep`). -/
inductive Op
  | add | sub | mul | div | mod | min | max | neg | abs
  | eq | ne | lt | le | gt | ge | and | or | not | first | last
  | fadd | fsub | fmul | fdiv | fpow | fmin | fmax | fneg | fabs
  | fsqrt | fexp | flog | fsin | fcos | ftan | fasin | facos | fatan | ffloor | fround
  | feq | fne | flt | fle | fgt | fge
  | f32to64
  /-- `div` and `mod` with the operands turned round, `eval a x = x / a`, `x % a`: a chain step `(rdiv, c)` of
      `kscan` is `x / c`, a constant divisor, which `div`'s step `c / x` cannot write (perf11). -/
  | rdiv | rmod
  /-- The random source (dataframe F8): `x` to splitmix64's output at the counter `x` (`mixWord`), a pure hash, so a
      program reading it stays a relation that answers the same at the same counter. -/
  | mix
  /-- q's `null` on a `1+atom` column (in band): `kscan` reads the seed's null flag of each row (`foRNuls`, the flagged
      block's all-ones residual) as the word, so a map is `1` at a null and `0` elsewhere; as a step it keeps the
      accumulator, like `first`. Placed after `mix` so `cast` and `fto` move up one tag (`crate/src/scan.rs` `CAST`). -/
  | null
  /-- `$` (S6/S7): the word of `t` holding the value of the word read at `s` (`QAtomicType.castWord`), `2^63` where
      none; one constructor for every pair, so `Op` reaches Rust as an object (`op_code`), not a byte. -/
  | cast (s t : QAtomicType)
  /-- The float verbs at a float atom `t` (S3): the `f64` answer as the canonical word of `t` nearest it
      (`ftoWord`: rounded to nearest, a zero as `+0`), `2^63` at a NaN, which no answer is. -/
  | fto (t : QAtomicType)
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- Whether the step reads the running value: a map's step does not, and `Rust` runs those in parallel blocks. The
unary ops and `last` look at the element alone. -/
def readsAcc : Op → Bool
  | neg | abs | not | last | fneg | fabs | fsqrt | fexp | flog | fsin | fcos | ftan | fasin | facos | fatan | ffloor
  | fround | f32to64 | mix | cast .. | fto _ => false
  | _ => true


def i (x : UInt64) : Int64 := x.toInt64
def f (x : UInt64) : Float := Float.ofBits x
def w (b : Bool) : UInt64 := if b then 1 else 0
def fw (x : Float) : UInt64 := x.toBits
/-- A NaN is the least value, as `Ew.ord64` orders the floats; so the `fmin`/`fmax` choice is total. -/
def fle' (x y : UInt64) : Bool := (f x).isNaN || (!(f y).isNaN && (f x ≤ f y))

/-- `fround`'s word: `x` rounded to the nearest integer, a tie to the even one (IEEE roundTiesToEven, C `rint`), from
    `floor` and the gap `d = x − ⌊x⌋` (exact below `2^52`, `0` above, where `x` is its own floor); a zero answer keeps
    `x`'s sign (`−0.5` to `−0`), as `rint` does; a NaN is itself. Lean's `Float.round` sends a tie away from zero. -/
def roundEven (x : UInt64) : UInt64 :=
  let y := (f x).floor
  let d := f x - y
  let r := if d < 0.5 then y else if 0.5 < d then y + 1 else if (y / 2).floor * 2 == y then y else y + 1
  if (f x).isNaN then x else if r == 0 then x &&& 0x8000000000000000 else fw r

/-- A NaN keeps the sign of the `f32` NaN it widens (q's null is the negative one). -/
def widen32 (x : UInt64) : UInt64 :=
  let b := x.toUInt32
  let v := Float32.ofBits b
  if v.isNaN then ((b >>> 31).toUInt64 <<< 63) ||| 0x7ff8000000000000 else v.toFloat.toBits

/-- `fto t`'s word: the `f64` word `x` as the word of the float atom `t` nearest it (IEEE round to nearest even, so
    an `f32` verb computed on widened words and rounded once is the `f32` verb: 53 ≥ 2·24 + 2), a zero as `+0`
    (decision G: no `-0` in a column); `2^63` at a NaN or at an atom holding no float. -/
def ftoWord (t : QAtomicType) (x : UInt64) : UInt64 :=
  let f := Float.ofBits x
  if f.isNaN then 0x8000000000000000 else match t with
  | .f64 => if f == 0 then 0 else x
  | .f32 => let g := f.toFloat32; if g == 0 then 0 else g.toBits.toUInt64
  | _ => 0x8000000000000000

/-- The step from an `f64` answer to the word of the atom `u`: `fto u` at a float atom (rounds, keeps `±∞`), else
    `cast .f64 u`, the exact value or `2^63` (NaN, `±∞`, a fraction, out of range). -/
def ofF64 : QAtomicType → Op
  | .f32 => .fto .f32
  | .f64 => .fto .f64
  | u => .cast .f64 u

/-- `mix`'s word: splitmix64 (Steele, Lea, Flood 2014) at the counter `x`, the finaliser of the state `(x + 1)·γ`
    (`γ = 0x9e3779b97f4a7c15`), shifted right by one so the answer is an `i64` in `[0, 2^63)`: `x = 0, 1, 2` are the
    first three outputs of the generator seeded `0` (`0xe220a8397b1dcdaf`, … ) halved. -/
def mixWord (x : UInt64) : UInt64 :=
  let z := (x + 1) * 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31)) >>> 1

/-- How `kscan` orders null for a binary op: null is below every value (`max(0N,5) = 5`, `min(0N,5) = 0N`), so a null
word is replaced by the op's identity (`i64` min for `max`, `i64` max for `min`) and the null flags fold with `and`
(`max`: null only where all are) or `or` (`min`: null where any is). `none`: the op refuses a null row. -/
def nulFold : Op → Option (Op × UInt64)
  | min => some (or, 0x7fffffffffffffff)
  | max => some (and, 0x8000000000000000)
  | _ => none

/-- Total, with the failure typed: integer `div`/`mod` by `0` is `.error`, not a null (`Ew.intStep` answers q's `0N`
there, a value the raw word cannot tell from an ordinary one). The unary ops ignore `acc`. -/
def eval : Op → UInt64 → UInt64 → Except String UInt64
  | add, a, x => .ok (a + x)
  | sub, a, x => .ok (a - x)
  | mul, a, x => .ok (a * x)
  | div, a, x =>
    if x == 0 then .error "Op.div: integer division by 0"
    else .ok (Int64.ofInt (Int.fdiv (i a).toInt (i x).toInt)).toUInt64
  | mod, a, x =>
    if x == 0 then .error "Op.mod: integer remainder by 0"
    else .ok (Int64.ofInt (Int.fmod (i a).toInt (i x).toInt)).toUInt64
  | rdiv, a, x =>
    if a == 0 then .error "Op.rdiv: integer division by 0"
    else .ok (Int64.ofInt (Int.fdiv (i x).toInt (i a).toInt)).toUInt64
  | rmod, a, x =>
    if a == 0 then .error "Op.rmod: integer remainder by 0"
    else .ok (Int64.ofInt (Int.fmod (i x).toInt (i a).toInt)).toUInt64
  | min, a, x => .ok (if i x < i a then x else a)
  | max, a, x => .ok (if i a < i x then x else a)
  | neg, _, x => .ok (0 - x)
  | abs, _, x => .ok (if i x < 0 then 0 - x else x)
  | eq, a, x => .ok (w (a == x))
  | ne, a, x => .ok (w (a != x))
  | lt, a, x => .ok (w (i a < i x))
  | le, a, x => .ok (w (i a ≤ i x))
  | gt, a, x => .ok (w (i x < i a))
  | ge, a, x => .ok (w (i x ≤ i a))
  | and, a, x => .ok (a &&& x)
  | or, a, x => .ok (a ||| x)
  | not, _, x => .ok (x ^^^ 1)
  | first, a, _ => .ok a
  | last, _, x => .ok x
  | fadd, a, x => .ok (fw (f a + f x))
  | fsub, a, x => .ok (fw (f a - f x))
  | fmul, a, x => .ok (fw (f a * f x))
  | fdiv, a, x => .ok (fw (f a / f x))
  | fpow, a, x => .ok (fw (f a ^ f x))
  | fmin, a, x => .ok (if fle' a x then a else x)
  | fmax, a, x => .ok (if fle' a x then x else a)
  | fneg, _, x => .ok (x ^^^ 0x8000000000000000)
  | fabs, _, x => .ok (x &&& 0x7fffffffffffffff)
  | fsqrt, _, x => .ok (fw (f x).sqrt)
  | fexp, _, x => .ok (fw (f x).exp)
  | flog, _, x => .ok (fw (f x).log)
  | fsin, _, x => .ok (fw (f x).sin)
  | fcos, _, x => .ok (fw (f x).cos)
  | ftan, _, x => .ok (fw (f x).tan)
  | fasin, _, x => .ok (fw (f x).asin)
  | facos, _, x => .ok (fw (f x).acos)
  | fatan, _, x => .ok (fw (f x).atan)
  | ffloor, _, x => .ok (fw (f x).floor)
  | fround, _, x => .ok (roundEven x)
  | feq, a, x => .ok (w (f a == f x))
  | fne, a, x => .ok (w (f a != f x))
  | flt, a, x => .ok (w (f a < f x))
  | fle, a, x => .ok (w (f a ≤ f x))
  | fgt, a, x => .ok (w (f x < f a))
  | fge, a, x => .ok (w (f x ≤ f a))
  | f32to64, _, x => .ok (widen32 x)
  | mix, _, x => .ok (mixWord x)
  | null, a, _ => .ok a
  | cast s t, _, x => .ok (QAtomicType.castWord s t x)
  | fto t, _, x => .ok (ftoWord t x)

/-- Whether `eval a x` can fail on the running value `a` (`rdiv`, `rmod`: `a` is their divisor). The kernels find a
failure from the elements before computing (`kscan`'s up-front test, `kscatter`'s first pass), which cannot see the
running value, so both refuse these as their op: they are chain steps, where `a` is a constant. -/
def readsDivisor : Op → Bool
  | rdiv | rmod => true
  | _ => false

/-- Whether the chain step `(o, c)`, `x ↦ o.eval c x`, fails at some word `x`: `div` and `mod` (at `x = 0`), and an op
reading its divisor from `c` at `c = 0`. `kscan` refuses such a step up front, so a chain never fails part way. -/
def stepFails (o : Op) (c : UInt64) : Bool := o == .div || o == .mod || (o.readsDivisor && c == 0)

def one (n : Float) : UInt64 := n.toBits
def neg1 : UInt64 := 0xffffffffffffffff

#guard Op.add.eval 3 4 matches .ok 7
#guard Op.sub.eval 3 4 matches .ok 0xffffffffffffffff
#guard Op.mul.eval 3 4 matches .ok 12
#guard Op.div.eval neg1 2 matches .ok 0xffffffffffffffff
#guard Op.div.eval 7 0 matches .error _
#guard Op.mod.eval 0xfffffffffffffff9 3 matches .ok 2
#guard Op.mod.eval 7 0 matches .error _
#guard Op.rdiv.eval 2 neg1 matches .ok 0xffffffffffffffff
#guard Op.rdiv.eval 0 7 matches .error _
#guard Op.rmod.eval 3 0xfffffffffffffff9 matches .ok 2
#guard Op.rmod.eval 0 7 matches .error _
#guard Op.min.eval neg1 1 matches .ok 0xffffffffffffffff
#guard Op.max.eval neg1 1 matches .ok 1
#guard Op.neg.eval 0 5 matches .ok 0xfffffffffffffffb
#guard Op.abs.eval 0 0xfffffffffffffffb matches .ok 5
#guard Op.eq.eval 2 2 matches .ok 1
#guard Op.ne.eval 2 2 matches .ok 0
#guard Op.lt.eval neg1 1 matches .ok 1
#guard Op.le.eval 2 2 matches .ok 1
#guard Op.gt.eval 2 neg1 matches .ok 1
#guard Op.ge.eval neg1 2 matches .ok 0
#guard Op.and.eval 1 0 matches .ok 0
#guard Op.or.eval 1 0 matches .ok 1
#guard Op.not.eval 0 1 matches .ok 0
#guard Op.first.eval 5 9 matches .ok 5
#guard Op.last.eval 5 9 matches .ok 9
#guard Op.null.eval 5 9 matches .ok 5
#guard Op.fadd.eval (one 1.5) (one 2.0) matches .ok 0x400c000000000000
#guard Op.fsub.eval (one 1.5) (one 2.0) matches .ok 0xbfe0000000000000
#guard Op.fmul.eval (one 1.5) (one 2.0) matches .ok 0x4008000000000000
#guard Op.fdiv.eval (one 1.0) (one 2.0) matches .ok 0x3fe0000000000000
#guard Op.fpow.eval (one 2.0) (one 3.0) matches .ok 0x4020000000000000
#guard Op.fmin.eval (one 1.0) (one 2.0) matches .ok 0x3ff0000000000000
#guard Op.fmax.eval (one 1.0) (one 2.0) matches .ok 0x4000000000000000
#guard Op.fneg.eval 0 (one 1.0) matches .ok 0xbff0000000000000
#guard Op.fabs.eval 0 (one (-1.0)) matches .ok 0x3ff0000000000000
#guard Op.fsqrt.eval 0 (one 4.0) matches .ok 0x4000000000000000
#guard Op.fexp.eval 0 0 matches .ok 0x3ff0000000000000
#guard Op.flog.eval 0 (one 1.0) matches .ok 0
#guard Op.fsin.eval 0 0 matches .ok 0
#guard Op.fcos.eval 0 0 matches .ok 0x3ff0000000000000
#guard Op.ftan.eval 0 0 matches .ok 0
#guard Op.fasin.eval 0 0 matches .ok 0
#guard Op.facos.eval 0 (one 1.0) matches .ok 0
#guard Op.fatan.eval 0 0 matches .ok 0
#guard Op.ffloor.eval 0 (one 2.5) matches .ok 0x4000000000000000
-- `fround` (crate/src/scan.rs `op_eval_floors_and_types_its_errors` checks the Rust on the same words): ties to even
-- `0.5 1.5 2.5 -0.5 -1.5` to `0 2 2 -0 -2`, `2.4 2.6 -0.3` to `2 3 -0`, `2^52 + 1` and `±∞` themselves, a NaN itself
#guard [0.5, 1.5, 2.5, -0.5, -1.5, 2.4, 2.6, -0.3, 4503599627370497.0, 1.0 / 0.0, -1.0 / 0.0].map
    (fun x => (Op.fround.eval 0 (one x)).toOption) ==
  [0, 0x4000000000000000, 0x4000000000000000, 0x8000000000000000, 0xc000000000000000, 0x4000000000000000,
   0x4008000000000000, 0x8000000000000000, 0x4330000000000001, 0x7ff0000000000000, 0xfff0000000000000].map some
#guard Op.fround.eval 0 0x7ff8000000000001 matches .ok 0x7ff8000000000001
#guard Op.feq.eval (one 1.0) (one 1.0) matches .ok 1
#guard Op.fne.eval (one 1.0) (one 1.0) matches .ok 0
#guard Op.flt.eval (one 1.0) (one 2.0) matches .ok 1
#guard Op.fle.eval (one 2.0) (one 2.0) matches .ok 1
#guard Op.fgt.eval (one 1.0) (one 2.0) matches .ok 0
#guard Op.fge.eval (one 2.0) (one 1.0) matches .ok 1
#guard Op.f32to64.eval 0 0x3fc00000 matches .ok 0x3ff8000000000000
#guard (Op.fto .f64).eval 0 (one 2.5) matches .ok 0x4004000000000000
#guard (Op.fto .f64).eval 0 0x8000000000000000 matches .ok 0
#guard (Op.fto .f64).eval 0 (one (0.0 / 0.0)) matches .ok 0x8000000000000000
#guard (Op.fto .f32).eval 0 (one 1.5) matches .ok 0x3fc00000
-- `0.1` rounded to the nearest `f32`; a tiny negative `f64` rounds to `-0` and is written `+0`
#guard (Op.fto .f32).eval 0 (one 0.1) matches .ok 0x3dcccccd
#guard (Op.fto .f32).eval 0 (one (-1e-50)) matches .ok 0
#guard (Op.fto .f32).eval 0 (one 1e300) matches .ok 0x7f800000
#guard (Op.fto .i64).eval 0 (one 1.0) matches .ok 0x8000000000000000
-- splitmix64 seeded `0`, its outputs `0xe220a8397b1dcdaf 0x6e789e6aa1b965f4 0x06c45d188009454f` halved (the Rust
-- `op_eval_floors_and_types_its_errors` checks the same words); the counter wraps: `2^64 − 1` is the state `0`
#guard [0, 1, 2, 0xffffffffffffffff].map (fun x => (Op.mix.eval 0 x).toOption) ==
  [0x7110541cbd8ee6d7, 0x373c4f3550dcb2fa, 0x03622e8c4004a2a7, 0].map some

end Op
end Rel.Kernel

/-! The value verb codes `Ew.intStep` (`Rel.Kernel.Elementwise`) reads; here, beside `Op`, because the run path names
a verb by its code (`Lang.Op.arith`, `stepCols`) and computes it with `Op` on the kernels, never with `Ew`. -/

namespace Rel.Kernel.Ew

/-- Value verbs: `+ - * % ^ & |`. -/
def add : UInt8 := 0
def sub : UInt8 := 1
def mul : UInt8 := 2
def fill : UInt8 := 4
def lesser : UInt8 := 5
def greater : UInt8 := 6
/-- `%`, q's `divide`: the quotient itself, at the float atoms only (`fverbBy`); `intStep` has no case for it, since the
    quotient of two integers is not an integer. -/
def divide : UInt8 := 3

/-- `div` and `mod`, numbered after the seven q spells as glyphs, because `Ew.intStep` runs them in the same loop over
the same two payloads; `~/q/q.k` line 4 defines `mod:{x-y*x div y}` and `Ew.intStep` says exactly that. -/
def idiv : UInt8 := 7
def imod : UInt8 := 8

end Rel.Kernel.Ew

/-! The value verbs at a float atom (typed base S3), on the `f64` words of their operands, as `Op`s compose them:
    the specification `stepAt` states and `fstepCols` runs. -/

namespace Rel.Kernel

/-- The `f64` word of a value of the float atom `t` (`Op.f32to64` widens an `f32`), none at an atom holding no float:
    the float verbs and orders read their operands at `f64`. -/
def fval : (t : QAtomicType) → Dep.Carrier t → Option UInt64
  | .f64, x => some x
  | .f32, x => some (Op.widen32 x.toUInt64)
  | _, _ => none

/-- The value verb `k` as one binary float `Op` and the unary `Op`s after it (a `kscan` chain), where it is that:
    `+ - * % max min` their `f` ops, `div` the floor of the quotient; none at `mod`, which reads `x` twice. -/
def fverbOne (k : UInt8) : Option (Op × List (Op × UInt64)) :=
  if k == Ew.add then some (.fadd, []) else if k == Ew.sub then some (.fsub, [])
  else if k == Ew.mul then some (.fmul, []) else if k == Ew.greater then some (.fmax, [])
  else if k == Ew.lesser then some (.fmin, []) else if k == Ew.divide then some (.fdiv, [])
  else if k == Ew.idiv then some (.fdiv, [(.ffloor, 0)]) else none

/-- The value verb `k` as a composition of float `Op`s, each applied by `ap` (to two words by `Op.eval`, to two
    columns by `colMap`), as q computes it on floats: `+ - * % max min` by their `f` ops, `div` the floor of the
    quotient (`ffloor` of `fdiv`), `mod` `x - y·(x div y)` (`q.k`: `mod:{x-y*x div y}`). A unary op reads its second
    operand. -/
def fverbBy {α : Type} (ap : Op → α → α → Except String α) (k : UInt8) (x y : α) : Except String α :=
  match fverbOne k with
  | some (o, c) => do c.foldlM (fun q p => ap p.1 q q) (← ap o x y)
  | none =>
    if k == Ew.imod then do let q ← ap .fdiv x y; let f ← ap .ffloor q q; ap .fsub x (← ap .fmul y f)
    else .error s!"arith: verb code {k} is none of + - * % div mod max min"

/-- `fverbBy` on two `f64` words. -/
abbrev fverb : UInt8 → UInt64 → UInt64 → Except String UInt64 := fverbBy Op.eval

/-- The value verb `k` at the float atom `t` on the `f64` words `x`, `y`: `fverb`, then `fto t`, which answers `2^63`
    where the IEEE answer is NaN. -/
def fstep (t : QAtomicType) (k : UInt8) (x y : UInt64) : Except String UInt64 := do
  (Op.fto t).eval 0 (← fverb k x y)

def bits (n : Float) : UInt64 := n.toBits
#guard fstep .f64 Ew.add (bits 1.5) (bits 2.0) matches .ok 0x400c000000000000
#guard fstep .f64 Ew.idiv (bits 7.5) (bits 2.0) matches .ok 0x4008000000000000
#guard fstep .f64 Ew.imod (bits 7.5) (bits 2.0) matches .ok 0x3ff8000000000000
#guard fstep .f64 Ew.sub (bits 0.0) (bits 0.0) matches .ok 0
#guard fstep .f64 Ew.idiv (bits 0.0) (bits 0.0) matches .ok 0x8000000000000000
#guard fstep .f32 Ew.add (bits 0.1) (bits 0.2) matches .ok 0x3e99999a
#guard fstep .f64 Ew.divide (bits 1.0) (bits 2.0) matches .ok 0x3fe0000000000000
#guard fstep .f64 Ew.divide (bits 1.0) (bits 0.0) matches .ok 0x7ff0000000000000
#guard fstep .f64 Ew.divide (bits 0.0) (bits 0.0) matches .ok 0x8000000000000000
#guard fstep .f32 Ew.divide (bits 1.0) (bits 3.0) matches .ok 0x3eaaaaab

end Rel.Kernel
