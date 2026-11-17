import Rel.Kernel.Value

/-! The part of `Rel.Kernel.TestChecks` the Rel kernels reach; `Rel.Kernel.TestChecks` imports it. -/


namespace Rel.Kernel.TestChecks

open Rel.Kernel

def nanF : Float := Float.ofBits Rel.nanBits

/-- `x + k` against the shift of its decimal integer, which is why `Kernel.Coc` declares no kernel
for `rust/src/coc.rs`'s `cocf_add_const`: the two are one ulp apart on ordinary prices, and it is the add
that q answers. Measured on q 4.1 — `0.56 + 7` is `7.5600000000000005` and `756 % 100` is
`7.5599999999999996` — and this is the same pair here.

Written as a pair of expressions rather than as a claim about the kernel because the kernel has no
Lean declaration to make a claim about: an element ALP stores as `d` at exponent `e` comes back from
the add as `d / 10 ^ e + k` and from the shift as `(d + k * 10 ^ e) / 10 ^ e`, and those two are
what is compared here. -/
def addShift (d e : Nat) (k : Float) : UInt64 × UInt64 :=
  let p := Rel.Column.pow10 e
  ((Float.ofNat d / p + k).toBits, ((Float.ofNat d + k * p) / p).toBits)

end Rel.Kernel.TestChecks
