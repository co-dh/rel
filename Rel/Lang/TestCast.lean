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

/-- error: -/
#guard_msgs in
rel_program floatToIntT where
    obj N
    obj F : f64
    x : F ⟶ F ≜ {(1.5,2.5)}
    y : F ⟶ N ≜ x $ N

/-- error: -/
#guard_msgs in
rel_program narrowT where
    obj N
    obj I : i32
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ I ≜ x $ I

/-- error: -/
#guard_msgs in
rel_program dateT where
    obj N
    obj D : date
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ D ≜ x $ D

/-- error: -/
#guard_msgs in
rel_program prodT where
    obj N
    x : N ⟶ N ≜ {(1,2)}
    y : N ⟶ N × N ≜ x $ (N × N)

end Rel.Lang.TestCast
