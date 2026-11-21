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

end Rel.Lang.TestGenericNum
