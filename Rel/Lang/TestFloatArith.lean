import Rel.Programs.Prelude

/-! The value verbs and the orders at the float atoms (typed base S3): `plus minus times div mod max min` and `< ≤` on
    objects of `f64` and `f32`, each the `Op` composition `stepAt` / `ltAt` states (`fverbBy`, then `Op.fto`), computed
    on the operands' `f64` words. `div` and `mod` are q's: the floor of the quotient, `x - y·(x div y)`. A row whose
    IEEE answer is NaN has no image; an infinity is a value; `-0` is written `+0`. Expected rows worked by hand. -/

namespace Rel.Lang.TestFloatArith

rel_program arithD where
    obj N
    obj F : f64
    a : N ⟶ F ≜ {(0,1.5),(1,0.0),(2,7.5),(3,1.0),(4,-2.0)}
    b : N ⟶ F ≜ {(0,2.0),(1,0.0),(2,2.0),(3,0.0),(4,0.0)}
    p : N ⟶ F ≜ {(0,0.1)}
    q : N ⟶ F ≜ {(0,0.2)}
    big : N ⟶ F ≜ {(0,1e308)}
    ten : N ⟶ F ≜ {(0,10.0)}
    check ⟨a, b⟩ plus = {(0,3.5),(1,0),(2,9.5),(3,1),(4,-2)}
    check ⟨a, b⟩ minus = {(0,-0.5),(1,0),(2,5.5),(3,1),(4,-2)}
    check ⟨a, b⟩ times = {(0,3),(1,0),(2,15),(3,0),(4,0)}
    check ⟨a, a⟩ div = {(0,1),(2,1),(3,1),(4,1)}

    check dom(⟨a, b⟩ div) = {(0,0),(2,2),(3,3),(4,4)}
    check ⟨a, b⟩ mod = {(0,1.5),(2,1.5)}
    check ⟨a, b⟩ max = {(0,2),(1,0),(2,7.5),(3,1),(4,0)}
    check ⟨a, b⟩ min = {(0,1.5),(1,0),(2,2),(3,0),(4,-2)}
    check ⟨p, q⟩ plus = {(0,0.30000000000000004)}
    check dom(⟨big, ten⟩ times) = {(0,0)}

-- by hand: `(-2.0)·0.0 = -0` is written `0`; `0/0` is NaN, so row 1 of `div` and of `mod` has no image; `1/0 = ∞`
-- is a value, so rows 3, 4 of `div` are kept, and `mod` there is `1 - 0·∞` = NaN, none; `7.5 div 2 = 3`,
-- `7.5 mod 2 = 1.5`; `1e308·10` overflows to `∞`, a value
#guard arithD.failures.map toString == []

rel_program arithS where
    obj N
    obj G : f32
    a : N ⟶ G ≜ {(0,1.5),(1,0.0),(2,7.5),(3,1.0),(4,-2.0)}
    b : N ⟶ G ≜ {(0,2.0),(1,0.0),(2,2.0),(3,0.0),(4,0.0)}
    p : N ⟶ G ≜ {(0,0.1)}
    q : N ⟶ G ≜ {(0,0.2)}
    big : N ⟶ G ≜ {(0,3e38)}
    ten : N ⟶ G ≜ {(0,10.0)}
    check ⟨a, b⟩ plus = {(0,3.5),(1,0),(2,9.5),(3,1),(4,-2)}
    check ⟨a, b⟩ minus = {(0,-0.5),(1,0),(2,5.5),(3,1),(4,-2)}
    check ⟨a, b⟩ times = {(0,3),(1,0),(2,15),(3,0),(4,0)}
    check ⟨a, a⟩ div = {(0,1),(2,1),(3,1),(4,1)}
    check dom(⟨a, b⟩ div) = {(0,0),(2,2),(3,3),(4,4)}
    check ⟨a, b⟩ mod = {(0,1.5),(2,1.5)}
    check ⟨a, b⟩ max = {(0,2),(1,0),(2,7.5),(3,1),(4,0)}
    check ⟨a, b⟩ min = {(0,1.5),(1,0),(2,2),(3,0),(4,-2)}
    check ⟨p, q⟩ plus = {(0,0.3)}
    check dom(⟨big, ten⟩ times) = {(0,0)}

-- by hand: as `arithD`, and at `f32` `0.1 + 0.2` rounds to the `f32` nearest `0.3`, the word `0.3` reads as;
-- `3e38·10` overflows the `f32` range to `∞`, a value
#guard arithS.failures.map toString == []

rel_program orderT where
    obj N
    obj F : f64
    obj G : f32
    x : N ⟶ F ≜ {(0,1.5),(1,-2.0),(2,0.0)}
    y : N ⟶ F ≜ {(0,1.5),(1,0.0)}
    g : N ⟶ G ≜ {(0,1.5),(1,-2.0),(2,0.0)}
    h : N ⟶ G ≜ {(0,1.5),(1,0.0)}
    check x < y° = {(1,0),(1,1),(2,0)}
    check x ≤ y° = {(0,0),(1,0),(1,1),(2,0),(2,1)}
    check g < h° = {(1,0),(1,1),(2,0)}
    check g ≤ h° = {(0,0),(1,0),(1,1),(2,0),(2,1)}

#guard orderT.failures.map toString == []

-- an `i64` and an `f64` operand: refused naming both objects; the program casts one with `$` first
/-- error: line 83, col 24: the source of the right factor of a composition: found N×N, expected N×F -/
#guard_msgs in
rel_program mixedT where
    obj N
    obj F : f64
    a : N ⟶ N ≜ {(0,1)}
    b : N ⟶ F ≜ {(0,1.5)}
    c : N ⟶ F ≜ ⟨a, b⟩ plus

-- an atom with no value step (`valueAtom`): refused, the error listing the atoms that have one
/-- error: line 92, col 24: plus on I: I is an object of i32, and plus runs on objects of i64, f32, f64 only -/
#guard_msgs in
rel_program narrowT where
    obj N
    obj I : i32
    a : N ⟶ I ≜ {(0,1)}
    c : N ⟶ I ≜ ⟨a, a⟩ plus

-- `succ` stays on `i64`: a float has no successor
/-- error: line 101, col 19: succ on F: F is an object of f64, and succ runs on objects of i64 only -/
#guard_msgs in
rel_program succFT where
    obj N
    obj F : f64
    a : N ⟶ F ≜ {(0,1.5)}
    c : N ⟶ F ≜ a succ

end Rel.Lang.TestFloatArith
