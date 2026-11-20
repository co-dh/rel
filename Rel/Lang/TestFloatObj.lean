import Rel.Programs.Prelude

/-! An object declared at an atom (`obj F : f64`, design S1) and float words (S2): a literal read at the object it is
    used at (`Elab.wordAt`, `-0.0` normalised to `0.0`), printed back by the shortest decimal that reads back to the
    same bits (`Elab.floatText`), and the algebra on the stored words. Expected rows worked by hand. -/

namespace Rel.Lang.TestFloatObj

rel_program floatG where
    sw(R : α ⟶ β) : β ⟶ α ≜ R°
    both(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ R ∩ S

open floatG in
rel_program floatT where
    obj F : f64
    a : F ⟶ F ≜ {(2.5,1),(-0.0,0.0),(1e-3,1.5e10),(-2.5,3)}
    b : F ⟶ F ≜ {(2.5,1.0),(0.0,0.0),(3,7)}
    c : F ⟶ F ≜ {(1e-8,1e21),(0.1,123.456),(0.3333333333333333,-1.5E-7)}
    check a 𝟙 = a
    check dom(a) = {(2.5,2.5),(0,0),(0.001,0.001),(-2.5,-2.5)}
    check a° = {(1,2.5),(0,0),(1.5e10,0.001),(3,-2.5)}
    check a b = {(0,0),(-2.5,7)}
    check a ∩ b = {(2.5,1),(0,0)}
    check a ∪ b = {(2.5,1),(0,0),(0.001,1.5e10),(-2.5,3),(3,7)}
    check sw(a) = a°
    check both(a, b) = a ∩ b
    print a
    print c

-- by hand: `-0.0` is read as `0.0` (one zero), so `a ∩ b` keeps `(0,0)`; `a b` joins `a`'s targets `0` and `3` to
-- `b`'s sources; `sw`, `both` are generic definitions instantiated at `F` (placeholders other than `f64`)
#guard floatT.failures.map toString == []
#guard floatT.prints == ["a = {(-2.5, 3.0), (0.0, 0.0), (0.001, 15000000000.0), (2.5, 1.0)}",
  "c = {(1e-8, 1e21), (0.1, 123.456), (0.3333333333333333, -0.00000015)}"]

/-- error: line 39, col 13: an object of sym is not declared: no literal of sym is stored; the atoms are [u8, i16, i32, i64, f32, f64, char, i8, date, datetime] -/
#guard_msgs in
rel_program symT where
    obj S : sym

/-- error: line 44, col 13: an object of general is not declared: no literal of general is stored; the atoms are [u8, i16, i32, i64, f32, f64, char, i8, date, datetime] -/
#guard_msgs in
rel_program generalT where
    obj G : general

/-- error: line 49, col 13: unknown atom 'float'; the atoms are [u8, i16, i32, i64, f32, f64, char, i8, date, datetime] -/
#guard_msgs in
rel_program unknownT where
    obj U : float

/-- error: line 55, col 17: no declared object has the elements [2.5] ('2.5' is not an element of N, an object of i64) -/
#guard_msgs in
rel_program floatAtLongT where
    obj N
    x : N ⟶ N ≜ {(2.5,1)}

/-- error: line 61, col 17: no declared object has the elements [nan] ('nan' is not an element of F, an object of f64) -/
#guard_msgs in
rel_program nanT where
    obj F : f64
    x : F ⟶ F ≜ {(nan,1)}

/-- error: line 67, col 17: no declared object has the elements [1e400] ('1e400' is not an element of F, an object of f64: it is beyond the range of f64) -/
#guard_msgs in
rel_program hugeT where
    obj F : f64
    x : F ⟶ F ≜ {(1e400,1)}

/-- error: line 74, col 24: plus on F: F is an object of f64, and plus runs on objects of i64 only -/
#guard_msgs in
rel_program plusT where
    obj F : f64
    x : F ⟶ F ≜ {(2.5,1)}
    d : F ⟶ F ≜ x ⟨𝟙,𝟙⟩plus

/-- error: line 81, col 24: < on F: F is an object of f64, and < runs on objects of i64 only -/
#guard_msgs in
rel_program ltT where
    obj F : f64
    x : F ⟶ F ≜ {(2.5,1)}
    l : F ⟶ F ≜ dom(x) < dom(x)

-- objects at nine atoms leave three placeholders (`general`, `u1`, `sym`), too few for four object variables: the
-- call reports it (`Expand.placeholdersFor`), not the expansion it would otherwise fall back to
/-- error: line 97, col 5: `g` has 4 object variables, and only 3 atoms no object in scope is stored at stand for them ([general, u1, sym]) -/
#guard_msgs in
rel_program fewPlaceholdersT where
    obj A : u8
    obj B : i16
    obj C : i32
    obj D : f32
    obj F : f64
    obj H : char
    obj I : i8
    obj J : date
    obj K : datetime
    g(R : α ⟶ β, S : γ ⟶ δ) : α ⟶ β ≜ R
    x : F ⟶ F ≜ {(2.5,1)}
    y : F ⟶ F ≜ g(x, x)

end Rel.Lang.TestFloatObj
