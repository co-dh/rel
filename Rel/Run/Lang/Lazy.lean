module

public import Rel.Run.Gather

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! A relation computed now (`tab`) or on what its context already knows of its two sides (`lazy`): the
    replacement for the demand bit of `Gen.Fn`. A `tab` holds its table or the message of the op that could not
    compute it, so a kernel composition's error reaches `check` and `print`. -/

namespace Rel

/-- What a context knows of a relation's two sides: the values its domain and its range are confined to,
    `none` where a side is unconstrained. -/
structure Known (A B : Obj) where
  dom : Option ((n : USize) × Vals A n) := none
  ran : Option ((n : USize) × Vals B n) := none
  /-- The pairs the context meets the result with (`GenK.meetOn`): off them the result is never read, so a relation
      that tests a pair at a time (a comparison) tests these instead of building `dom × ran`. -/
  pairs : Option (Tab A B) := none

/-- A relation as a table, or as a function of what is `Known` of its sides; a function, not a demand bit,
    so a lazy term reads its keys from the context it runs in. -/
inductive Rel (A B : Obj) where
  | tab (t : Except String (Tab A B))
  | lazy (f : Known A B → Rel A B)
  /-- `Tab.ofBits g w o x ra y rc` not yet read back as rows: an op with a rule for a bit matrix (`GenK.meet`, `≫`)
      reads `o` as bits; any other reads the rows (`runE`). The one form a result flows up in that is not rows:
      `Known` flows down, and `tab` holds rows. -/
  | bits {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals B m) (rc : Enc)

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

/-- `t`, computed in the order tried second after the first failed with `e`: its failure names both, since its
    own message alone hides why the first order could not run (a bound it passed, `crossMax`). -/
def retryE {α : Type} (e : String) (t : Except String α) : Except String α :=
  t.mapError fun e' => s!"{e}; run the other operand first: {e'}"

/-- `r` as `retryE` makes a table: run in the order tried second after the first failed with `e`. -/
def Rel.retried {A B : Obj} (e : String) : Rel A B → Rel A B
  | .tab t => .tab (retryE e t)
  | .lazy f => .lazy fun K => (f K).retried e
  | .bits g w o x ra y rc => .bits g w o x ra y rc

/-- The message of the op that could not compute `r` closed; none where it computed. -/
def Rel.err {A B : Obj} (r : Rel A B) : Option String := match r.runE {} with
  | .error e => some e
  | .ok _ => none

end Rel
