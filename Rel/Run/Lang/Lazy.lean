import Rel.Run.CRelDef
import Rel.Run.Cols

/-! A relation computed now (`tab`) or on what its context already knows of its two sides (`lazy`): the
    replacement for the demand bit of `Gen.Fn`. A `tab` holds its table or the message of the op that could not
    compute it, so a kernel composition's error reaches `check` and `print`. -/

namespace Rel

/-- What a context knows of a relation's two sides: the values its domain and its range are confined to,
    `none` where a side is unconstrained. -/
structure Known (A B : Obj) where
  dom : Option ((n : USize) × Vals A n) := none
  ran : Option ((n : USize) × Vals B n) := none

/-- A relation as a table, or as a function of what is `Known` of its sides; a function, not a demand bit,
    so a lazy term reads its keys from the context it runs in. -/
inductive Rel (A B : Obj) where
  | tab (t : Except String (Tab A B))
  | lazy (f : Known A B → Rel A B)
  /-- `Tab.ofBits g w o x ra y rc` not yet read back as rows: an op with a rule for a bit matrix (`GenK.meet`, `≫`)
      reads `o` as bits; any other reads the rows (`runE`). The one form a result flows up in that is not rows:
      `Known` flows down, and `tab` holds rows. -/
  | bits {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals B m) (rc : Enc)

/-- An old-layer table as a `tab`'s: its one failure, a run past capacity, named. Goes with the old layer (W5). -/
@[coe] def CRel.toE {A B : Obj} : CRel A B → Except String (Tab A B)
  | some t => .ok t
  | none => .error "an op of the old layer ran past capacity"

instance {A B : Obj} : Coe (CRel A B) (Except String (Tab A B)) := ⟨CRel.toE⟩

@[simp] theorem CRel.toE_some {A B : Obj} (t : Tab A B) : CRel.toE (some t) = .ok t := rfl
@[simp] theorem CRel.toE_none {A B : Obj} : CRel.toE (none : CRel A B) = .error "an op of the old layer ran past capacity" := rfl
@[simp] theorem CRel.toE_toOption {A B : Obj} (c : CRel A B) : c.toE.toOption = c := by cases c <;> rfl

/-- The table `r` computes in the context `K`, or the message of the op that could not: a `lazy` one is run on
    `K` until it is a table. -/
def Rel.runE {A B : Obj} : Rel A B → Known A B → Except String (Tab A B)
  | .tab t, _ => t
  | .lazy f, K => (f K).runE K
  | .bits g w o x ra y rc, _ => Tab.ofBits g w o x ra y rc

/-- `r` run on `K` until it is no `lazy`: a `bits` kept as bits. -/
def Rel.force {A B : Obj} : Rel A B → Known A B → Rel A B
  | .lazy f, K => (f K).force K
  | r, _ => r

/-- `runE` as the old layer reads it, a run past capacity as `none`. Goes with the old layer (W5). -/
def Rel.run {A B : Obj} : Rel A B → Known A B → CRel A B
  | .tab t, _ => t.toOption
  | .lazy f, K => (f K).run K
  | .bits g w o x ra y rc, _ => (Tab.ofBits g w o x ra y rc).toOption

/-- The message of the op that could not compute `r` closed; none where it computed. -/
def Rel.err {A B : Obj} (r : Rel A B) : Option String := match r.runE {} with
  | .error e => some e
  | .ok _ => none

end Rel
