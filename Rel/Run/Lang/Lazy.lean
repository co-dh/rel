import Rel.Run.CRelDef

/-! A relation computed now (`tab`) or on what its context already knows of its two sides (`lazy`): the
    replacement for the demand bit of `Gen.Fn`. `none` in a `tab` is a run past capacity. -/

namespace Rel

/-- What a context knows of a relation's two sides: the values its domain and its range are confined to,
    `none` where a side is unconstrained. -/
structure Known (A B : Obj) where
  dom : Option ((n : USize) × Vals A n) := none
  ran : Option ((n : USize) × Vals B n) := none

/-- A relation as a table, or as a function of what is `Known` of its sides; a function, not a demand bit,
    so a lazy term reads its keys from the context it runs in. -/
inductive Rel (A B : Obj) where
  | tab (t : Option (Tab A B))
  | lazy (f : Known A B → Rel A B)

/-- The table `r` computes in the context `K`: a `lazy` one is run on `K` until it is a table. -/
def Rel.run {A B : Obj} : Rel A B → Known A B → Option (Tab A B)
  | .tab t, _ => t
  | .lazy f, K => (f K).run K

end Rel
