module

public import Rel.Run.Comp
public import Rel.Run.SetOps

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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
  let ne (x : Enc) : Except String Enc := colMap .first n x x .i64 .i64 [] [(.ne, nulWord)]
  let isZ (x : Enc) : Except String Enc := colMap .first n x x .i64 .i64 [] [(.eq, 0)]
  let both ← colMap .and n (← ne a) (← ne b)
  if k == Ew.add || k == Ew.sub then
    let w ← colArr (if k == Ew.add then .add else .sub) n a b
    let ord ← if k == Ew.add then colMap .le n a w.enc else colMap .le n w.enc a
    let ex ← colMap .eq n (← colMap .first n b b .i64 .i64 [] [(.le, 0)]) ord
    pure (w, ← colMap .and n (← colMap .and n both (← ne w.enc)) ex)
  else if k == Ew.mul then
    let w ← colArr .mul n a b
    let a0 ← isZ a
    let ex ← colMap .or n (← colMap .eq n (← colMap .div n w.enc (← colMap .or n a a0)) b) a0
    pure (w, ← colMap .and n (← colMap .and n both (← ne w.enc)) ex)
  else if k == Ew.idiv || k == Ew.imod then
    let b0 ← isZ b
    let w ← colArr (if k == Ew.idiv then .div else .mod) n a (← colMap .or n b b0)
    pure (w, ← colMap .and n (← colMap .and n both (← colMap .not n b0 b0)) (← ne w.enc))
  else if k == Ew.greater || k == Ew.lesser then
    if hN : hasNul a = false ∧ hasNul b = false then
      let w ← colArr (if k == Ew.greater then .max else .min) n a b (hF := Or.inr (by simp [hN.1, hN.2]))
      pure (w, ← ne w.enc)
    else throw "arith: max/min of a column holding an in-band null"
  else throw s!"arith: verb code {k} is none of + - * div mod max min"

/-- The `n` words of `a` read at `t` through `widen t`, as a column: `a` itself where the chain is empty. -/
def wideCol (t : QAtomicType) (n : USize) (a : Enc) : Except String Enc :=
  if widen t = [] then pure a else colMap .first n a a .i64 t (widen t)

/-- The keep flag of a float answer `w`: each word not `nulWord` (`Op.fto`'s NaN), one pass reading `w`'s words. -/
def nanFlag (n : USize) (w : Enc) : Except String Enc := colMap .first n w w .u1 .i64 [] [(.ne, nulWord)]

/-- The answer column of the value verb `k` at the float atom `t` on the `n` operand rows `a`, `b`: one pass of the
    verb's `fverbOne`, the operands through `widen t` and the answer through the verb's chain and `Op.fto t`; a verb
    with no `fverbOne` (`mod`, which reads `x` twice) by `fverbBy` with `colMap` on the widened columns, then
    `Op.fto t`. -/
def fstepArr (t : QAtomicType) (k : UInt8) (n : USize) (a b : Enc) : Except String (Arr t n) :=
  match fverbOne k with
  | some (o, c) =>
    if hF : o.nulFold = none then colArr o n a b t t (widen t) (c ++ [(.fto t, 0)]) (hF := Or.inl hF)
    else .error "fstep: the float op orders a null"
  | none => do
    let r ← fverbBy (fun o x y => colMap o n x y) k (← wideCol t n a) (← wideCol t n b)
    colArr (.fto t) n r r t

/-- **The value verb `k` at the float atom `t`** on the `n` operand rows `a`, `b` (`stepAt`): `fstepArr`, then
    `nanFlag`. -/
def fstepCols (t : QAtomicType) (k : UInt8) (n : USize) (a b : Enc) : Except String (Arr t n × Enc) := do
  let w ← fstepArr t k n a b
  pure (w, ← nanFlag n w.enc)

/-- **The float `Op` `o` from the float atom `t` to the atom `u`** on the `n` operand rows `a`, `b` (`floatDen`): one
    pass, each word through `widen t`, `o` (a unary `Op` reads `b` alone) and `Op.ofF64 u`; then `nanFlag`. -/
def fmapCols (t u : QAtomicType) (o : Op) (n : USize) (a b : Enc) : Except String (Arr u n × Enc) := do
  if hF : o.nulFold = none then
    let w ← colArr o n a b u t (widen t) [(.ofF64 u, 0)] (hF := Or.inl hF)
    pure (w, ← nanFlag n w.enc)
  else throw "fmap: the float op orders a null"

/-- The value verb `k` at the atom `t`: `stepCols` at `i64`, `fstepCols` at a float atom, the error naming any other
    (`stepAt` has no row there). -/
def stepColsAt : (t : QAtomicType) → UInt8 → (n : USize) → Enc → Enc → Except String (Arr t n × Enc)
  | .i64, k, n, a, b => stepCols k n a b
  | .f32, k, n, a, b => fstepCols .f32 k n a b
  | .f64, k, n, a, b => fstepCols .f64 k n a b
  | t, _, _, _, _ => throw s!"arith on objects of {repr t}: no value verb"

namespace Tab
variable {K : Obj}

/-- Each word `u` of the `i64` column `e` to `u + [u ≠ null]` (`Ew.intStep`'s wrapping `u + 1`, the null to itself) by
    two `colMap`s: the step of `succOp`. -/
def succCol (n : USize) (e : Enc) : Except String (Arr .i64 n) := do
  colArr .add n e (← colMap .first n e e .i64 .i64 [] [(.ne, nulWord)])

end Tab

/-- The value verbs, each a row of `prims` under its q name with its `Ew` code (`Tab.arithOp`), on pairs of one
    number atom and no universe (§3.5); `max` `min` are the fused rows of their definition `τ(≤)π₂ ∪ τ(>)π₁` at a
    value atom. -/
def arithOps : List (String × UInt8) :=
  [("plus", Kernel.Ew.add), ("minus", Kernel.Ew.sub), ("times", Kernel.Ew.mul), ("div", Kernel.Ew.idiv),
   ("mod", Kernel.Ew.imod), ("divide", Kernel.Ew.divide), ("max", Kernel.Ew.greater), ("min", Kernel.Ew.lesser)]

/-- The orders as tests on pairs, each a row of `prims` (`Tab.cmpOp`): `lt` is `<` (`ordOp true`), `le` is `≤`. `le`
    is a row, not `lt ∪ 𝟙`: at a float atom `-0.0 ≤ +0.0` holds, `-0.0 < +0.0` does not (`Rel.Lang.AtomOrderTest`). -/
def cmpOps : List (String × Bool) := [("lt", true), ("le", false)]

/-- The surface symbol of the order, strict or not: the row of an order's universe (`cmpRelRow`) is named by it, the
    test row (`cmpRow`) by its `cmpOps` key. -/
def ordSym (strict : Bool) : String := if strict then "<" else "≤"

namespace Tab

/-- The error `msg r` at the first row `r` of `X` flagged `1` in `f` (`Tab.keep` keeps row order), none if no row is. -/
def failAt {A : Obj} {n : USize} (X : Vals A n) (f : Enc) (msg : A.El → String) : Except String Unit := do
  let T ← Tab.keep (k := A) (v := A) ⟨n, X, X⟩ f
  if h : 0 < T.n.toNat then throw (msg (T.key.row ⟨0, h⟩)) else pure ()

/-- **An `i64` value verb never wraps** (owner decision): a row `stepCols` drops with both operands non-null and a
    divisor `≠ 0` is a `+ - *` whose answer left `i64` (or is the null word), and the run fails naming the row, the
    operands and the type; a null operand and a zero divisor still have no image. A float atom has no check (`±∞`). -/
def arithOvf (s : String) {t t' : QAtomicType} {n : USize} (X : Vals (.prod (.atom t) (.atom t')) n) (keep : Enc) :
    Except String Unit :=
  match t, t', X with
  | .i64, .i64, X => do
    let nn (x : Enc) := colMap .first n x x .i64 .i64 [] [(.ne, nulWord)]
    let z ← colMap .first n X.2.enc X.2.enc .i64 .i64 [] [(.eq, 0)]
    let f ← colMap .and n (← colMap .and n (← nn X.1.enc) (← nn X.2.enc))
      (← colMap .and n (← colMap .not n keep keep) (← colMap .not n z z))
    failAt (A := .prod .long .long) X f fun (a, b) => s!"{s}: i64 overflow at {s}({a.toInt}, {b.toInt})"
  | _, _, _ => pure ()

/-- **The row `s` of `arithOps` on the pairs `X`** (`rowDens`: `stepOn`): `stepColsAt` of the two components, the
    rows it keeps with their answers (`Tab.keep`, no `canon`), the run failing where an `i64` answer overflowed
    (`arithOvf`). The row is the first argument so `kernRows` names one constant for every name, as `Tab.floatOp`. -/
def arithOp (s : String) {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match arithOps.lookup s, A, B, X with
  | some k, .prod (.atom t) (.atom t'), .atom u, X =>
    if t = u ∧ t' = u then do
      let (w, b) ← stepColsAt u k n X.1.enc X.2.enc
      arithOvf s X b
      Tab.keep (k := .prod (.atom t) (.atom t')) (v := .atom u) ⟨n, X, w⟩ b
    else .error s!"{s} runs from a pair of one number object to it, found {repr t}×{repr t'} to {repr u}"
  | some _, _, _, _ => .error s!"{s} runs from a pair of one number object to it"
  | none, _, _, _ => .error s!"{s}: no value verb"

/-- **The row `succ` on the values `X`** (`rowDens`: `succOn`): `succCol`, `Tab.succ`'s step without its universe;
    the run fails at `Int64.maxValue`, whose `u + 1` would wrap to the null (owner decision, as `arithOvf`). -/
def succOp {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .atom .i64, .atom .i64, X => do
    let s ← succCol n X.enc
    failAt (A := .long) X (← colMap .first n X.enc X.enc .i64 .i64 [] [(.eq, 0x7FFFFFFFFFFFFFFF)])
      fun u => s!"succ: i64 overflow at succ({u.toInt})"
    pure ⟨n, X, s⟩
  | _, _, _ => .error "succ runs from an object of i64 to it"

/-- **The row `mix` on the values `X`** (`rowDens`: `mixOn`): one `kscan` map of `Op.mix`, each word to splitmix64 at
    that counter (`Op.mixWord`); every value has an image, so nothing is dropped. -/
def mixOp {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .atom .i64, .atom .i64, X => do
    let s ← colArr .mix n X.enc X.enc
    pure ⟨n, X, s⟩
  | _, _, _ => .error "mix runs from an object of i64 to it"

end Tab

/-! ### Checks: an `i64` overflow fails the run naming the row; a null operand and a zero divisor do not -/

private def ovBig : Arr .i64 3 := Arr.ofBytes .i64 (packLongs [1, 9223372036854775807, 5]) (by longs_lit)
private def ovOne : Arr .i64 3 := Arr.ofBytes .i64 (packLongs [1, 1, 1]) (by longs_lit)
private def ovTwo : Arr .i64 3 := Arr.ofBytes .i64 (packLongs [4, 2, 0]) (by longs_lit)
private def err {A B : Obj} (e : Except String (Tab A B)) : String := match e with | .error m => m | .ok _ => ""

#guard err (Tab.arithOp "plus" (A := .prod .long .long) (B := .long) (n := 3) (ovBig, ovOne)) ==
  "plus: i64 overflow at plus(9223372036854775807, 1)"
#guard err (Tab.arithOp "times" (A := .prod .long .long) (B := .long) (n := 3) (ovBig, ovTwo)) ==
  "times: i64 overflow at times(9223372036854775807, 2)"
#guard err (Tab.arithOp "minus" (A := .prod .long .long) (B := .long) (n := 3) (ovOne, ovBig)) == ""
#guard (Tab.arithOp "plus" (A := .prod .long .long) (B := .long) (n := 3) (ovOne, ovTwo)).toOption.map Tab.toList ==
  some [((1, 4), 5), ((1, 2), 3), ((1, 0), 1)]
#guard (Tab.arithOp "div" (A := .prod .long .long) (B := .long) (n := 3) (ovBig, ovTwo)).toOption.map Tab.toList ==
  some [((1, 4), 0), ((9223372036854775807, 2), 4611686018427387903)]
#guard err (Tab.succOp (A := .long) (B := .long) (n := 3) ovBig) ==
  "succ: i64 overflow at succ(9223372036854775807)"
#guard (Tab.succOp (A := .long) (B := .long) (n := 3) ovTwo).toOption.map Tab.toList == some [(4, 5), (2, 3), (0, 1)]

end Rel
