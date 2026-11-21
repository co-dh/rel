import Rel.Programs.Prelude

/-! The row `$` (typed base S6): `x $ F` gives each value of `x` the same number at `F`'s atom (`QAtomicType.embed`),
    no row where `F` holds no such word, and refuses at elaboration a pair whose values are not all kept
    (`QAtomicType.castOK`). Expected rows worked by hand. -/

namespace Rel.Lang.TestCast

rel_program castT where
    obj N
    obj F : f64
    obj I : i32
    a : N ⟶ N ≜ {(0,0),(1,-7),(2,3),(3,9007199254740992),(4,9007199254740993)}
    i : N ⟶ I ≜ {(0,-5),(1,0),(2,7)}
    af : N ⟶ F ≜ a $ F
    check a $ F = {(0,0),(1,-7),(2,3),(3,9007199254740992)}
    check i $ N = {(0,-5),(1,0),(2,7)}
    check (a $ F) ∩ (a $ F) = af
    print af

-- by hand: `2^53 + 1` is no `f64` value (53 bits of mantissa), so row 4 has no image; `-7`, `0` are exact
#guard castT.failures.map toString == []
#guard castT.prints == ["af = {(0, 0.0), (1, -7.0), (2, 3.0), (3, 9007199254740992.0)}"]

/-- error: line 31, col 5: $ from F (f64) to N (i64): not every f64 value is a i64 value, and $ keeps a number's value -/
#guard_msgs in
rel_program floatToIntT where
    obj N
    obj F : f64
    x : F ⟶ F ≜ {(1.5,2.5)}
    y : F ⟶ N ≜ x $ N

/-- error: line 39, col 5: $ from N (i64) to I (i32): not every i64 value is a i32 value, and $ keeps a number's value -/
#guard_msgs in
rel_program narrowT where
    obj N
    obj I : i32
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ I ≜ x $ I

/-- error: line 47, col 5: $ from N (i64) to D (date): not every i64 value is a date value, and $ keeps a number's value -/
#guard_msgs in
rel_program dateT where
    obj N
    obj D : date
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ D ≜ x $ D

/-- error: line 54, col 5: $ from N (i64) to N×N (no atom): not every i64 value is a no atom value, and $ keeps a number's value -/
#guard_msgs in
rel_program prodT where
    obj N
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ N × N ≜ x $ (N × N)

-- a date is its `i32` count of days since 1970-01-01, a datetime its `i64` count: `$` reads and writes that count
rel_program dateCastT where
    obj N
    obj I : i32
    obj D : date
    obj T : datetime
    obj G : f32
    d : N ⟶ D ≜ {(0,19000),(1,-5),(2,16777217)}
    i : N ⟶ I ≜ {(0,19000),(1,-5)}
    m : N ⟶ N ≜ {(0,86400000000000),(1,-1)}
    t : N ⟶ T ≜ {(0,86400000000000),(1,-1)}
    check d $ N = {(0,19000),(1,-5),(2,16777217)}
    check d $ I = {(0,19000),(1,-5),(2,16777217)}
    check i $ D = {(0,19000),(1,-5)}
    check t $ N = {(0,86400000000000),(1,-1)}
    check m $ T = {(0,86400000000000),(1,-1)}
    check (i $ D) $ I = i
    -- by hand: `2^24 + 1` is no `f32` value (24 bits of mantissa), so day 16777217 has no image
    check d $ G = {(0,19000),(1,-5)}

#guard dateCastT.failures.map toString == []

-- a date and a datetime count in different units, so neither casts to the other
/-- error: line 86, col 5: $ from D (date) to T (datetime): not every date value is a datetime value, and $ keeps a number's value -/
#guard_msgs in
rel_program dateTimeT where
    obj N
    obj D : date
    obj T : datetime
    x : N ⟶ D ≜ {(1,2)}
    y : N ⟶ T ≜ x $ T

end Rel.Lang.TestCast
