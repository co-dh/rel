import Rel.Run.Lang.Gen
import Rel.Run.SetOps
import Rel.Run.Comp
import Rel.Run.Struct
import Rel.Run.Power
import Rel.Run.List

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

/-- The rows of `prims` with a kernel body: each row's `Tab` operator, run under the `GenK` twin of the wrapper its
    old constant runs under (`Expand.primE`), as `RowCode` gives the old ones; a row not here keeps a program off
    the kernel path (`Tm.kernelNode`). -/
def kernRows : List (String × Lean.Name) :=
  [("∋", ``Tab.mem), ("τ", ``Tab.tau), ("length", ``Tab.length), ("setify", ``Tab.setify),
   ("snoc", ``Tab.snoc), ("cons", ``Tab.cons), ("cat", ``Tab.cat), ("zip", ``Tab.zip), ("sum", ``Tab.sum),
   ("uncons", ``Tab.uncons), ("unsnoc", ``Tab.unsnoc), ("uncat", ``Tab.uncat)]

-- every kernel row is a row of `prims`
#guard kernRows.all fun (s, _) => prims.any (·.sym == s)

/-- `t`'s own node has a kernel body (`GenK`): T2's `val uni 𝟘 𝟙 ° ≫ ∩ ∪ − dom ran`, and `own`, which runs its
    part. -/
def Tm.kernelNode {A B : Obj} : Tm A B → Bool
  | .val _ | .uni _ | .zero | .id | .comp .. | .conv _ | .meet .. | .join .. | .diff .. | .dom _ | .ran _
  | .own _ => true
  | .leq _ => true
  | .lt _ => true
  | .succ _ => true
  | .arith .. => true
  | .lam _ => true
  | .E _ => true
  | .nil => true
  | .est _ => true
  | .thin _ => true
  | .atPos _ => true
  | .prim r => (kernRows.lookup r.sym).isSome
  | _ => false

/-- Every node of `t` has a kernel body: the test that puts a program on the kernel path. A `share` is entered
    here, though `Tm.parts` does not enter it. -/
partial def Tm.onKernel {A B : Obj} (t : Tm A B) : Bool := match t with
  | .share _ R => R.onKernel
  | t => t.kernelNode && t.parts.all fun ⟨_, _, u⟩ => u.onKernel

/-! ### T4, T5: `≤ < succ`, the value verbs, `Λ E nil est thin at`, and the wrapper `after` of the rows -/

namespace GenK

open Rel Gen

/-- A row composed after the keys: `f` on the coreflexive of the values the context knows (`Gen.after`'s rule). -/
def after (A B : Obj) (f : {K : Obj} → Tab K A → Except String (Tab K B)) : Fn true A B :=
  ofVals A B fun X => do f (← Tab.idU X)

/-- `succ`, a value verb on `U`'s universe: the keys' coreflexive `D`, then `D ≫ succDen U` (`Tab.succ`),
    `D ≫ arithDen k U` (`Tab.arith`). -/
def succ (U : Fn false .long .long) : Fn true .long .long := after _ _ fun D => do Tab.succ D (← U.runE {})
def arith (k : UInt8) (U : Fn false .long .long) : Fn true (.prod .long .long) .long :=
  after _ _ fun D => do Tab.arith k D (← U.runE {})

/-- `K ≫ op ≫ L` on `U`'s universe (`Tab.leq`, `Tab.lt`, CROSS of the two sides): each side the values the context
    knows of it cut to `dom U` (`idU ≫ dom U`), `dom U` where it knows none (§0, `Known`). -/
def cmp (f : {n m : USize} → Vals .long n → Vals .long m → Except String (Tab .long .long))
    (U : Fn false .long .long) : Fn false .long .long := .lazy fun K => .tab do
  let d ← (← U.runE {}).dom
  let side (s : Option ((n : USize) × Vals .long n)) : Except String ((n : USize) × Vals .long n) :=
    s.elim (pure ⟨d.n, d.key⟩) fun c => do let t ← (← Tab.idU c.2).comp d; pure ⟨t.n, t.key⟩
  let k ← side K.dom; let l ← side K.ran
  f k.2 l.2
def leq (U : Fn false .long .long) : Fn false .long .long := cmp Tab.leq U
def lt (U : Fn false .long .long) : Fn false .long .long := cmp Tab.lt U

/-- `Λ(R)` on the keys `X` (`Tab.lam`), `R` run knowing its domain is `X`. -/
def lam (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true A (.arr B) :=
  ofVals _ _ fun X => do Tab.lam X (← R.runE ⟨some ⟨_, X⟩, none⟩)
/-- `E(R) = Λ(∋ ≫ R)` (`Tab.E`'s composition): `R` runs knowing its domain is `ran(∋)` at the arrays in demand. -/
def E (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true (.arr A) (.arr B) :=
  lam _ _ true (comp _ _ _ d (ofVals _ _ fun X => Tab.mem X) R)
def nil (A B : Obj) : Fn true A (.arr B) := ofVals _ _ fun X => Tab.nil X

/-- `est(Q)`, `thin(Q)` on the arrays in demand, the pair test `Q` run knowing its domain is the pairs `D` it is
    asked about (`Gen.est`'s `Q.at`). -/
def est (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) B :=
  ofVals _ _ fun X => Tab.est (fun D => Q.runE ⟨some ⟨D.n, D.val⟩, none⟩) X
def thin (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) (.arr B) :=
  ofVals _ _ fun X => Tab.thin (fun D => Q.runE ⟨some ⟨D.n, D.val⟩, none⟩) X
def atPos (B : Obj) (k : Nat) : Fn true (.arr B) B := ofVals _ _ fun X => Tab.atPos k X

end GenK

end Rel.Lang
