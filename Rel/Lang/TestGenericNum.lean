import Rel.Programs.Prelude

/-! Number verbs and `$` at an object variable of a generic definition (§e): the check that the verb runs on the
    variable's atom (`numObj`) or that the cast keeps every value (`castOK`) is left to each use. A body that builds
    only with those checks left open has no constant; each use builds its expansion at the call's objects, where the
    checks run (`Expand.once`, `ObjInfo.deferred`), and a refusal names the call, the variable and its object
    (`mkDef`). A constant built at `.long` for a variable serves only calls at `.long` objects; a call at another
    object builds the expansion (`build`'s `.call`). Expected rows worked by hand. -/

namespace Rel.Lang.TestGenericNum

open Rel.Programs.prelude in
rel_program genNumG where
    avg(a : 1 ⟶ φ, b : 1 ⟶ φ) : 1 ⟶ φ ≜ ⟨a, b⟩%
    half(a : 1 ⟶ φ) : 1 ⟶ φ ≜ ⟨a, {(∗,2)}⟩%
    root(a : 1 ⟶ φ) : 1 ⟶ φ ≜ a sqrt
    to(a : 1 ⟶ φ) : 1 ⟶ ψ ≜ a $ ψ
    daysBetween(a : ν ⟶ δ, b : ν ⟶ δ) : ν ⟶ ζ ≜ ⟨a $ ζ, b $ ζ⟩minus

-- the day count at an object the library declares, the variable `δ` only cast from: its constant is built with `δ`
-- at `.long`, and a call at a date object builds the expansion
open Rel.Programs.prelude in
rel_program genNumZ where
    obj Z
    daysZ(a : ν ⟶ δ, b : ν ⟶ δ) : ν ⟶ Z ≜ ⟨a $ Z, b $ Z⟩minus

open Rel.Programs.prelude genNumG genNumZ in
rel_program genNumT where
    obj F : f64
    obj N
    obj D : date
    x : 1 ⟶ F ≜ {(∗,3.0)}
    y : 1 ⟶ F ≜ {(∗,4.0)}
    k : 1 ⟶ N ≜ {(∗,3)}
    check avg(x, y) = {(∗,0.75)}
    check half(y) = {(∗,2.0)}
    check root(y) = {(∗,2.0)}
    kf : 1 ⟶ F ≜ to(k)
    check kf = {(∗,3.0)}
    a : N ⟶ D ≜ {(0,2024.01.05),(1,2024.03.01)}
    b : N ⟶ D ≜ {(0,2024.01.01),(1,2024.02.28)}
    dn : N ⟶ N ≜ daysBetween(a, b)
    check dn = {(0,4),(1,2)}
    check daysZ(a, b) = {(0,4),(1,2)}

-- by hand: 3/4 = 0.75, 4/2 = 2, √4 = 2; 3 as f64 is 3.0; 2024-01-05 − 2024-01-01 = 4 days, 2024-03-01 −
-- 2024-02-28 = 2 days (2024 is a leap year)
#guard genNumT.failures.map toString == []

-- `%` at the integer object `N`: refused at the call, naming the variable and its object
/-- error: line 57, col 11: `avg` at this call, where φ is N: divide on N: N is an object of i64, and divide runs on objects of f32, f64 only; cast first, `x $ F` with `F` an object of f32, f64 -/
#guard_msgs in
open Rel.Programs.prelude genNumG in
rel_program genNumNT where
    obj N
    k : 1 ⟶ N ≜ {(∗,3)}
    check avg(k, k) = {(∗,1)}

-- an object the body leaves open and its type does not show (dataframe request 9): `length`'s ℕ in `lenF`, the ℕ
-- of `positions` and `sum` in the generic `wsum`, each the definition's implicit object variable at `.long`
-- (`Elab.generalise`)
open Rel.Programs.prelude in
rel_program lenT where
    obj K = {A,B,C}
    obj N
    obj F : f64
    lenF : [K] ⟶ F ≜ length $ F
    x : N ⟶ [K] ≜ {(0,[A B C]),(1,[A])}
    check x lenF = {(0,3.0),(1,1.0)}

open Rel.Programs.prelude in
rel_program wsumG where
    wsum(p : β ⟶ β) : [β] ⟶ ψ ≜ positions(p) sum $ ψ

open Rel.Programs.prelude wsumG in
rel_program wsumT where
    obj K = {A,B,C}
    obj N
    obj F : f64
    sel : K ⟶ K ≜ {(B,B),(C,C)}
    x : N ⟶ [K] ≜ {(0,[A B C]),(1,[C A C])}
    w : N ⟶ F ≜ x wsum(sel)
    check w = {(0,3.0),(1,2.0)}

-- by hand: [A B C] has 3 elements, [A] one; the B and C of [A B C] are at 1, 2 (sum 3), of [C A C] at 0, 2 (sum 2)
#guard lenT.failures.map toString == []
#guard wsumT.failures.map toString == []

-- a `check` is no definition: an object open in it is still refused
/-- error: line 97, col 5: an object is not determined; write the constant's objects, as in ⊤(A,B) or 𝟙(A) -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program openCheckT where
    obj K = {A,B,C}
    obj F : f64
    x : 1 ⟶ [K] ≜ {(∗,[A B C])}
    check x length $ F = {(∗,3.0)}

end Rel.Lang.TestGenericNum
