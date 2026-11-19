import Rel.Run.Lang.Gen
import Rel.Run.SetOps
import Rel.Run.Comp
import Rel.Run.Struct

/-! The kernel path: the `Gen` bodies a program runs when every node of its terms has one here (`Tm.onKernel`),
    each a composition of the `Tab` operators over the five kernels, with `Gen`'s signature so `Expand` emits
    either namespace by the same rule. A `tab` holds the message of the op that could not run, never a dropped
    error. No bit-matrix path: a closed `≫ ∩ −` is the table operator (W4). -/

namespace Rel.Lang

namespace GenK

open Rel Gen

/-- A closed leaf: the table `t` computes, or its message. -/
def const (A B : Obj) (t : Except String (Tab A B)) : Fn false A B := .tab t

/-- A literal: its `foR` columns as `Gen.atom` rebuilt them, in canonical order (`Tab.canon`); a column whose
    payload does not fit its length is an error. -/
def val (A B : Obj) (R : Tab A B × Bool) : Fn false A B :=
  const A B (if R.2 then Tab.canon R.1 else .error s!"val: a literal column of {R.1.n} rows does not fit its payload")
def uni (A : Obj) (m : USize) (U : Vals A m × Bool) : Fn false A A :=
  const A A (if U.2 then Tab.idU U.1 else .error s!"uni: a universe column of {m} rows does not fit its payload")
def zero (A B : Obj) : Fn false A B := const A B Tab.zero

/-- A leaf on demand: `f` on the values its context knows its domain to hold; an error where it is unknown. -/
def ofVals (A B : Obj) (f : {n : USize} → Vals A n → Except String (Tab A B)) : Fn true A B :=
  .lazy fun K => K.dom.elim (.tab (.error "a leaf on demand ran with its domain unknown")) fun c => .tab (f c.2)

def id (A : Obj) : Fn true A A := ofVals A A fun X => Tab.idU X

/-- `r S`, `r` the table of `R`: a table `S` is composed now; a lazy one runs knowing its domain is `ran(r)`,
    and not at all where `r` has no row. -/
def compT {A B C : Obj} : Except String (Tab A B) → Rel B C → Rel A C
  | .error e, _ => .tab (.error e)
  | .ok r, .tab s => .tab (s >>= Tab.comp r)
  | .ok r, .lazy g => if r.n == 0 then .tab Tab.zero else
    .lazy fun K => .tab do
      let d ← Tab.ran r; Tab.comp r (← (Rel.lazy g).runE ⟨some ⟨d.n, d.key⟩, K.ran⟩)

/-- `R s`, `s` the table of `S`: the mirror of `compT`, `R` run knowing its range is `s`'s key column. -/
def compS {A B C : Obj} (R : Rel A B) : Except String (Tab B C) → Rel A C
  | .error e => .tab (.error e)
  | .ok s => .tab do Tab.comp (← R.runE ⟨none, some ⟨s.n, s.key⟩⟩) s

/-- `R S`: a lazy `R` starts from the side its context knows (`Gen.comp`'s rule); also a closed `R`, which has no
    bit-matrix form here. -/
def comp (A B C : Obj) (e : Bool) (R : Fn true A B) (S : Fn e B C) : Fn true A C := match R with
  | .tab r => compT r S
  | .lazy f => .lazy fun
    | ⟨none, some L⟩ => compS (.lazy f) (S.runE ⟨none, some L⟩)
    | K => compT ((Rel.lazy f).runE ⟨K.dom, none⟩) S

/-- An op on one table: a table now, or lazy, its argument run on what `k` makes of the context. -/
def lift1 {A B C D : Obj} (f : Tab A B → Except String (Tab C D)) (k : Known C D → Known A B) : Rel A B → Rel C D
  | .tab r => .tab (r >>= f)
  | R => .lazy fun K => .tab (R.runE (k K) >>= f)

/-- An op on two tables: a table where both are, else lazy, each run on what `kl`, `kr` make of the context. -/
def lift2 {A B C D E F : Obj} (f : Tab A B → Tab C D → Except String (Tab E F)) (kl : Known E F → Known A B)
    (kr : Known E F → Known C D) : Rel A B → Rel C D → Rel E F
  | .tab r, .tab s => .tab do f (← r) (← s)
  | R, S => .lazy fun K => .tab do f (← R.runE (kl K)) (← S.runE (kr K))

def conv (A B : Obj) (R : Fn false A B) : Fn false B A := lift1 Tab.conv (fun K => ⟨K.ran, K.dom⟩) R
def meet (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 Tab.inter (fun K => K) (fun K => K) R S
def join (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 Tab.union (fun K => K) (fun K => K) R S
def diff (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 Tab.diff (fun K => K) (fun K => K) R S
def dom (A B : Obj) (d : Bool) (R : Fn d A B) : Fn d A A := lift1 Tab.dom (fun K => ⟨K.dom, none⟩) R
def ran (A B : Obj) (R : Fn false A B) : Fn false B B := lift1 Tab.ran (fun K => ⟨none, K.dom⟩) R

end GenK

/-- `t`'s own node has a kernel body (`GenK`): T2's `val uni 𝟘 𝟙 ° ≫ ∩ ∪ − dom ran`, and `own`, which runs its
    part. -/
def Tm.kernelNode {A B : Obj} : Tm A B → Bool
  | .val _ | .uni _ | .zero | .id | .comp .. | .conv _ | .meet .. | .join .. | .diff .. | .dom _ | .ran _
  | .own _ => true
  | _ => false

/-- Every node of `t` has a kernel body: the test that puts a program on the kernel path. A `share` is entered
    here, though `Tm.parts` does not enter it. -/
partial def Tm.onKernel {A B : Obj} (t : Tm A B) : Bool := match t with
  | .share _ R => R.onKernel
  | t => t.kernelNode && t.parts.all fun ⟨_, _, u⟩ => u.onKernel

end Rel.Lang
