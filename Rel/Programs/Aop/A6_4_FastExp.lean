/-! # Fast exponentiation and modulus of B&dM §6.4 (`AOP/A6_4_FastExp.lean`), in Rel: no row ported

Every row states a fusion condition or the program for `exp(a) = a^(−)` or `mod(b) = (−) mod b` over the binary
numbers `Bin = 1 + Bin×Bit`.  The prelude has no `pow` row, so `exp(a)` has no term, and the `mod` rows run on
fixed-width atoms (`Ew.imod`: `x mod 0` is null, where freyd's `a % 0 = a`, and `2n+d` wraps outside the object's
universe), so no statement agrees with freyd's on `Nat`. -/

-- not ported: exp_zero (Freyd.Alg.RelSet.FastExp.exp_zero, 06-recursive.typ:162): `zero exp(a) = one` is `a⁰ = 1`; the prelude has `plus`, `times`, `minus`, `div`, `mod`, `max`, `min` but no power, so `exp(a)` has no term (a parameter `E` for it would need the spec as a premise, which is the row's own content)
-- not ported: exp_shift (…exp_shift, 06-recursive.typ:164): `shift exp(a) = (exp(a)×𝟙)op(a)`: the same missing `exp(a)`; `a^(2n+d)` also needs the power laws `a^(m+n) = a^m a^n`, `a^(mn) = (a^m)^n`, none of which is a law of `times` over wrapping atoms
-- not ported: mod_zero (…mod_zero, 06-recursive.typ:174): `zero mod(b) = zero` is `0 mod b = 0`; the prelude `mod` is `Ew.imod`, which is null at `b = 0` (freyd: `a % 0 = a`), so the statement is false at `b = 0` and needs a premise `b > 0` with a constant `b : 1 ⟶ N`, and there is no law of `imod` over a bounded `obj` (only the unfolded `Ew.intStep`)
-- not ported: mod_shift (…mod_shift, 06-recursive.typ:176): `shift mod(b) = (mod(b)×𝟙)op(b)` needs `Bit = 1+1`, `2r+d` and `n−b` by `times`/`plus`/`minus` on wrapping atoms with an `n < 2b` bound inside the universe, and the same `imod` at `b = 0`; no arithmetic law of these rows exists in rel
-- not ported: convert_program, exp_program, mod_program (…, 06-recursive.typ:148, 159, 171): classified `语法缺`; they need `Bin = [Bit]` as a snoc-list datatype with `convert = ⦇[zero,shift]⦈`, and the two programs rest on the missing `exp`/`mod` rows above
