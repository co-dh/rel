import Rel.Programs.Frame

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
/-- error: line 12, col 30: `dom` at this use: nothing here fixes its object variable 'α' (`dom` : α ⟶ α); give the use an expected type: a typed definition, a check against a typed term, or a composition that fixes α -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program openCheckT where
    obj K = {A,B,C}
    obj F : f64
    x : 1 ⟶ [K] ≜ {(∗,[A B C])}
    check x length $ F = {(∗,3.0)}

-- an object variable only the result names (dataframe request 10): each use's expected type puts an object at it,
-- a typed definition's or a check's other side, and the number checks run there (`Elab.settleUses`)
open Rel.Programs.prelude in
rel_program avgGG where
    obj Z
    avgG : [Z] ⟶ φ ≜ ⟨sum $ φ, length $ φ⟩%

open Rel.Programs.prelude avgGG in
rel_program avgGT where
    obj N
    obj F : f64
    obj G : f64
    x : N ⟶ [Z] ≜ {(0,[1 2 3 4]),(1,[5])}
    m : N ⟶ F ≜ x avgG
    check m = {(0,2.5),(1,5.0)}
    check x avgG = m
    g : N ⟶ G ≜ x avgG
    check g = {(0,2.5),(1,5.0)}

-- by hand: (1+2+3+4)/4 = 2.5, 5/1 = 5
#guard avgGT.failures.map toString == []

-- a use nothing fixes the variable at is refused, naming the variable, the definition and the use
/-- error: line 128, col 13: `avgG` at this use: nothing here fixes its object variable 'φ' (`avgG` : [Z] ⟶ φ); give the use an expected type: a typed definition, a check against a typed term, or a composition that fixes φ -/
#guard_msgs in
open Rel.Programs.prelude avgGG in
rel_program avgGOpen where
    obj N
    x : N ⟶ [Z] ≜ {(0,[1 2 3 4])}
    print x avgG

-- `sum` at the object variable itself: the constant is built with φ at `.long` (`dfns` has no form at a
-- placeholder, `Expand.once`), so a use at f64 or at a universe builds the expansion there (`Pre.call`'s `alt`),
-- where `build` chooses the row: the fused f64 fold, the i64 one, the fold cut to `0…5`; through a second generic
-- definition (`g`) likewise
open Rel.Programs.prelude in
rel_program sumGG where
    sumT(x : ν ⟶ [φ]) : ν ⟶ φ ≜ x sum
    sumN(x : ν ⟶ [ψ]) : ν ⟶ ψ ≜ sumT(x)
    avgS : [φ] ⟶ φ ≜ ⟨sum, length $ φ⟩%

open Rel.Programs.prelude sumGG in
rel_program sumGT where
    obj N
    obj F : f64
    obj I
    obj P = 0…5
    x : N ⟶ [F] ≜ {(0,[1.5 2.5]),(1,[0.25])}
    y : N ⟶ [I] ≜ {(0,[1 2 3]),(1,[5 -7])}
    z : N ⟶ [P] ≜ {(0,[1 2]),(1,[4 3])}
    check sumT(x) = {(0,4.0),(1,0.25)}
    check sumN(x) = {(0,4.0),(1,0.25)}
    check x avgS = {(0,2.0),(1,0.25)}
    check sumT(y) = {(0,6),(1,-2)}
    check sumN(y) = {(0,6),(1,-2)}
    check sumN(z) = {(0,3)}

-- by hand: 1.5+2.5 = 4, 4/2 = 2; 1+2+3 = 6, 5−7 = −2; at P = 0…5, 1+2 = 3 and 4+3 = 7 ∉ P, so row 1 has no sum
#guard sumGT.failures.map toString == []

-- a number literal in a generic body is open (`Elab.litTy`), a float one too: `{(∗,0.5)}` beside `a` is at φ, and
-- each use reads its words at the object the use puts there (`numCheck`); a word that object does not hold is
-- refused at that use, naming it (dataframe request 12)
open Rel.Programs.prelude in
rel_program litGG where
    inc(a : 1 ⟶ φ) : 1 ⟶ φ ≜ ⟨a, {(∗,0.5)}⟩plus

open Rel.Programs.prelude litGG in
rel_program litGT where
    obj F : f64
    obj E : f32
    x : 1 ⟶ F ≜ {(∗,1.5)}
    y : 1 ⟶ E ≜ {(∗,2.25)}
    check inc(x) = {(∗,2.0)}
    check inc(y) = {(∗,2.75)}

-- by hand: 1.5 + 0.5 = 2, 2.25 + 0.5 = 2.75, both exact in f32
#guard litGT.failures.map toString == []

/-- error: line 184, col 11: `inc` at this call, where φ is N: '0.5' is not an element of N, an object of i64 -/
#guard_msgs in
open Rel.Programs.prelude litGG in
rel_program litGN where
    obj N
    k : 1 ⟶ N ≜ {(∗,3)}
    check inc(k) = {(∗,3)}

-- a call's argument holding a literal whose object `settleOpen` settles last (`{(∗,0)}`, open in a generic body)
-- has no form until it is settled: the use is the expansion (`Expand.callDef`); the literal no use reaches is read
-- against the objects the definition sees, `Z` (`mkDef`), so the caller's `F`, `N` do not make it ambiguous
-- (dataframe request 13)
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumLitG where
    obj Z : i64
    s(p : 1 ⟶ φ, c : ν ⟶ γ) : 1 ⟶ φ ≜ summarize(F(q) sum, q) where h ≜ dom(⟨{(∗,0)} $ φ, p⟩ cor(≤)) p, q ≜ ⟨c $ φ, ⊤ h⟩minus

open Rel.Programs.prelude Rel.Programs.frame sumLitG in
rel_program sumLitT where
    obj N
    obj F : f64
    p : 1 ⟶ F ≜ {(∗,1.5)}
    z : 1 ⟶ F ≜ {(∗,0.0)}
    c : N ⟶ F ≜ {(0,1.0),(1,2.0),(2,4.0)}
    check s(p, c) = {(∗,2.5)}
    check s(z, c) = {(∗,7.0)}

-- by hand: 0 ≤ 1.5, so h = 1.5 and q = {−0.5, 0.5, 2.5}, sum 2.5; 0 ≤ 0, so h = 0 and q = c, sum 7
#guard sumLitT.failures.map toString == []

end Rel.Lang.TestGenericNum
