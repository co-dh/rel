import Rel.Run.Comp
import Rel.Run.SetOps

/-! The value verbs and `succ` of the language (`Tm.arith`, `Tm.succ`; their meanings `arithDen`, `succDen` in
`Rel/Lang/Den.lean`) as compositions of the five kernels on encoded columns (PLAN 6.14 W3). Each runs on the rows in
demand `D` and answers `D ≫ ⟦verb⟧`:

- `arithDen k U = (𝟙 ∩ (π₁ ≫ U)(π₁ ≫ U)°) ≫ (𝟙 ∩ (π₂ ≫ U)(π₂ ≫ U)°) ≫ step(k) ≫ U`: the two input tests are
  compositions with `dom U` (`Tab.comp`, `Tab.dom`), `step(k)` one `colMap` of the verb's `Op` and its exactness
  flags (`stepCols`), the kept rows selected by `Tab.keep`, then `≫ U` by `Tab.comp`.
- `succDen U = dom U ≫ (u ↦ u + 1) ≫ dom U`: `Tab.comp` with `dom U` on both sides of one `colMap .add`.

The step reads raw words as `Op.eval` does (two's complement `Int64`); `Ew.intStep`'s null (`Int64.minValue`) is the
word `2^63`. Laws in `Rel/RepTabArith.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `Ew.intStep`'s null `Int64.minValue` as a raw word. -/
def nulWord : UInt64 := 0x8000000000000000

/-- **One value verb `k` on the `n` operand rows `a`, `b`**: the answer column `w` and the keep flag (`0`/`1`) of
`stepDen k`: `w` is `Ew.intStep k` of the row, not the null, and for `+ - *` did not wrap. `+ - * div mod` answer the
null at a null operand, `div`/`mod` also at a zero divisor, which is replaced by `1` before `Op.div`/`Op.mod`
(they fail the whole scan at `0`) and the row dropped. A `+`/`-` wrapped where `0 ≤ b` disagrees with `a ≤ w`
(`w ≤ a`); a `*` where `w div a ≠ b` and `a ≠ 0` (`a = 0` replaced by `1` for the divide). `max`/`min` never wrap and
read no null. Any other code is the error naming it. -/
def stepCols (k : UInt8) (n : USize) (a b : Enc) : Except String (Arr .i64 n × Enc) := do
  let nul ← colConst n nulWord
  let z ← colConst n 0
  let ne (x : Enc) : Except String Enc := colMap .ne n x nul
  let both ← colMap .and n (← ne a) (← ne b)
  if k == Ew.add || k == Ew.sub then
    let w ← colArr (if k == Ew.add then .add else .sub) n a b
    let ord ← if k == Ew.add then colMap .le n a w.enc else colMap .le n w.enc a
    let ex ← colMap .eq n (← colMap .ge n b z) ord
    pure (w, ← colMap .and n (← colMap .and n both (← ne w.enc)) ex)
  else if k == Ew.mul then
    let w ← colArr .mul n a b
    let a0 ← colMap .eq n a z
    let ex ← colMap .or n (← colMap .eq n (← colMap .div n w.enc (← colMap .or n a a0)) b) a0
    pure (w, ← colMap .and n (← colMap .and n both (← ne w.enc)) ex)
  else if k == Ew.idiv || k == Ew.imod then
    let b0 ← colMap .eq n b z
    let w ← colArr (if k == Ew.idiv then .div else .mod) n a (← colMap .or n b b0)
    pure (w, ← colMap .and n (← colMap .and n both (← colMap .not n b0 b0)) (← ne w.enc))
  else if k == Ew.greater || k == Ew.lesser then
    let w ← colArr (if k == Ew.greater then .max else .min) n a b
    pure (w, ← ne w.enc)
  else throw s!"arith: verb code {k} is none of + - * div mod max min"

/-- The words the verbs and orders of the atom `t` compute on, of the `n` words `a`: an `f32` column read at `f32` and
    widened to `f64` (`Op.f32to64`, `fval`), any other as stored. -/
def wideCol (t : QAtomicType) (n : USize) (a : Enc) : Except String Enc :=
  match t with
  | .f32 => colMap .f32to64 n a a .i64 .f32
  | _ => pure a

/-- **The value verb `k` at the float atom `t`** on the `n` operand rows `a`, `b` (`stepAt`): `fverbBy` with `colMap`
    on their `f64` words, `Op.fto t` writing the word of `t`, kept where that is not `nulWord` (a NaN answer). -/
def fstepCols (t : QAtomicType) (k : UInt8) (n : USize) (a b : Enc) : Except String (Arr t n × Enc) := do
  let r ← fverbBy (fun o x y => colMap o n x y) k (← wideCol t n a) (← wideCol t n b)
  let w ← colArr (.fto t) n r r t
  pure (w, ← colMap .ne n w.enc (← colConst n nulWord))

/-- The value verb `k` at the atom `t`: `stepCols` at `i64`, `fstepCols` at a float atom, the error naming any other
    (`stepAt` has no row there). -/
def stepColsAt : (t : QAtomicType) → UInt8 → (n : USize) → Enc → Enc → Except String (Arr t n × Enc)
  | .i64, k, n, a, b => stepCols k n a b
  | .f32, k, n, a, b => fstepCols .f32 k n a b
  | .f64, k, n, a, b => fstepCols .f64 k n a b
  | t, _, _, _, _ => throw s!"arith on objects of {repr t}: no value verb"

namespace Tab
variable {K : Obj}

/-- **`D ≫ arithDen k U`**: `D`'s rows whose first operand is in `dom U` (`Tab.comp` of the rows keyed by
themselves with `dom U`), of those the ones whose second is, `stepCols` on their operands, the kept rows with their
answers (`Tab.keep`), `≫ U` (`Tab.comp`). `U X` is the universe at the values `X`: an infinite one (`𝟙`) is run
only where its values are known, so each test asks `U` at the column it tests. -/
def arith (t : QAtomicType) (k : UInt8) (D : Tab K (.prod (.atom t) (.atom t)))
    (U : {n : USize} → Vals (.atom t) n → Except String (Tab (.atom t) (.atom t))) :
    Except String (Tab K (.atom t)) := do
  let E₁ : Tab (.prod K (.prod (.atom t) (.atom t))) (.atom t) ←
    Tab.comp ⟨D.n, ((D.key, D.val) : Vals K D.n × Vals (.prod (.atom t) (.atom t)) D.n), D.val.1⟩
      (← (← U D.val.1).dom)
  let E : Tab (.prod K (.prod (.atom t) (.atom t))) (.atom t) ←
    Tab.comp ⟨E₁.n, E₁.key, E₁.key.2.2⟩ (← (← U E₁.key.2.2).dom)
  let (w, b) ← stepColsAt t k E.n E.key.2.1.enc E.key.2.2.enc
  let P ← Tab.keep ⟨E.n, E.key.1, w⟩ b
  Tab.comp P (← U P.val)

/-- **`D ≫ succDen U`**: `D ≫ dom U`, each value `u` to `u + [u ≠ null]` (`Ew.intStep`'s wrapping `u + 1`, the
null to itself) by two `colMap`s, `≫ dom U`; `U X` the universe at the values `X`, as in `arith`. -/
def succ (D : Tab K .long) (U : {n : USize} → Vals .long n → Except String (Tab .long .long)) :
    Except String (Tab K .long) := do
  let E ← D.comp (← (← U D.val).dom)
  let s ← colArr .add E.n E.val.enc (← colMap .ne E.n E.val.enc (← colConst E.n nulWord))
  Tab.comp ⟨E.n, E.key, s⟩ (← (← U s).dom)

end Tab

end Rel
