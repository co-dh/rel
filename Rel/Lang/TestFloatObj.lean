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
  "c = {(1e-8, 1e21), (0.1, 123.456), (0.3333333333333333, -1.5e-7)}"]

/-- error: -/
#guard_msgs in
rel_program symT where
    obj S : sym

/-- error: -/
#guard_msgs in
rel_program generalT where
    obj G : general

/-- error: -/
#guard_msgs in
rel_program unknownT where
    obj U : float

/-- error: -/
#guard_msgs in
rel_program floatAtLongT where
    obj N
    x : N ⟶ N ≜ {(2.5,1)}

/-- error: -/
#guard_msgs in
rel_program nanT where
    obj F : f64
    x : F ⟶ F ≜ {(nan,1)}

/-- error: -/
#guard_msgs in
rel_program hugeT where
    obj F : f64
    x : F ⟶ F ≜ {(1e400,1)}

/-- error: -/
#guard_msgs in
rel_program plusT where
    obj F : f64
    x : F ⟶ F ≜ {(2.5,1)}
    d : F ⟶ F ≜ x ⟨𝟙,𝟙⟩plus

/-- error: -/
#guard_msgs in
rel_program ltT where
    obj F : f64
    x : F ⟶ F ≜ {(2.5,1)}
    l : F ⟶ F ≜ dom(x) < dom(x)

end Rel.Lang.TestFloatObj
