import Rel.Kernel.Cast

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
  | fsqrt | fexp | flog | fsin | fcos | ftan | fasin | facos | fatan | ffloor
  | feq | fne | flt | fle | fgt | fge
  | f32to64
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
  | f32to64 | cast .. | fto _ => false
  | _ => true

/-- Whether `eval (eval a b) c = eval a (eval b c)`, so a scan may be cut into blocks and the blocks' totals combined.
Float `+ *` round, so they are not; `min`/`max` are, as `fmin`/`fmax` are under a total order (a NaN is the least). -/
def assoc : Op → Bool
  | add | mul | min | max | and | or | first | last | fmin | fmax => true
  | _ => false

private def i (x : UInt64) : Int64 := x.toInt64
private def f (x : UInt64) : Float := Float.ofBits x
private def w (b : Bool) : UInt64 := if b then 1 else 0
private def fw (x : Float) : UInt64 := x.toBits
/-- A NaN is the least value, as `Ew.ord64` orders the floats; so the `fmin`/`fmax` choice is total. -/
private def fle' (x y : UInt64) : Bool := (f x).isNaN || (!(f y).isNaN && (f x ≤ f y))

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
  | feq, a, x => .ok (w (f a == f x))
  | fne, a, x => .ok (w (f a != f x))
  | flt, a, x => .ok (w (f a < f x))
  | fle, a, x => .ok (w (f a ≤ f x))
  | fgt, a, x => .ok (w (f x < f a))
  | fge, a, x => .ok (w (f x ≤ f a))
  | f32to64, _, x => .ok (widen32 x)
  | cast s t, _, x => .ok (QAtomicType.castWord s t x)
  | fto t, _, x => .ok (ftoWord t x)

private def one (n : Float) : UInt64 := n.toBits
private def neg1 : UInt64 := 0xffffffffffffffff

#guard Op.add.eval 3 4 matches .ok 7
#guard Op.sub.eval 3 4 matches .ok 0xffffffffffffffff
#guard Op.mul.eval 3 4 matches .ok 12
#guard Op.div.eval neg1 2 matches .ok 0xffffffffffffffff
#guard Op.div.eval 7 0 matches .error _
#guard Op.mod.eval 0xfffffffffffffff9 3 matches .ok 2
#guard Op.mod.eval 7 0 matches .error _
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

/-- The value verb `k` as a composition of float `Op`s, each applied by `ap` (to two words by `Op.eval`, to two
    columns by `colMap`), as q computes it on floats: `+ - * % max min` by their `f` ops, `div` the floor of the
    quotient (`ffloor` of `fdiv`), `mod` `x - y·(x div y)` (`q.k`: `mod:{x-y*x div y}`). A unary op reads its second
    operand. -/
def fverbBy {α : Type} (ap : Op → α → α → Except String α) (k : UInt8) (x y : α) : Except String α :=
  if k == Ew.add then ap .fadd x y else if k == Ew.sub then ap .fsub x y
  else if k == Ew.mul then ap .fmul x y else if k == Ew.greater then ap .fmax x y
  else if k == Ew.lesser then ap .fmin x y else if k == Ew.divide then ap .fdiv x y
  else if k == Ew.idiv then do let q ← ap .fdiv x y; ap .ffloor q q
  else if k == Ew.imod then do let q ← ap .fdiv x y; let f ← ap .ffloor q q; ap .fsub x (← ap .fmul y f)
  else .error s!"arith: verb code {k} is none of + - * % div mod max min"

/-- `fverbBy` on two `f64` words. -/
abbrev fverb : UInt8 → UInt64 → UInt64 → Except String UInt64 := fverbBy Op.eval

/-- The value verb `k` at the float atom `t` on the `f64` words `x`, `y`: `fverb`, then `fto t`, which answers `2^63`
    where the IEEE answer is NaN. -/
def fstep (t : QAtomicType) (k : UInt8) (x y : UInt64) : Except String UInt64 := do
  (Op.fto t).eval 0 (← fverb k x y)

private def bits (n : Float) : UInt64 := n.toBits
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
