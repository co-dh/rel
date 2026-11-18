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
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- Whether the step reads the running value: a map's step does not, and `Rust` runs those in parallel blocks. The
unary ops and `last` look at the element alone. -/
def readsAcc : Op → Bool
  | neg | abs | not | last | fneg | fabs | fsqrt | fexp | flog | fsin | fcos | ftan | fasin | facos | fatan | ffloor
  | f32to64 => false
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

/-- A NaN keeps the sign of the `f32` NaN it widens (q's null is the negative one), as `Ew.widen`. -/
private def widen32 (x : UInt64) : UInt64 :=
  let b := x.toUInt32
  let v := Float32.ofBits b
  if v.isNaN then ((b >>> 31).toUInt64 <<< 63) ||| 0x7ff8000000000000 else v.toFloat.toBits

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

end Op
end Rel.Kernel
