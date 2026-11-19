import Rel.Run.Lang.Gen
import Rel.Run.SetOps
import Rel.Run.Comp
import Rel.Run.Struct
import Rel.Run.Power
import Rel.Run.List
import Rel.Run.Div
import Rel.Run.Fix

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

/-- `R S`, also for a closed `R` (no bit-matrix form here): `S` runs first, on the range, only where the context
    knows only the range and `S` is closed; else `R` runs first and hands its range to `S` as its domain (§0). -/
def comp (A B C : Obj) (e : Bool) (R : Fn true A B) (S : Fn e B C) : Fn true A C := match R with
  | .tab r => compT r S
  | .lazy f => .lazy fun
    | ⟨none, some L⟩ => if e then compT ((Rel.lazy f).runE {}) S else compS (.lazy f) (S.runE ⟨none, some L⟩)
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

/-! ### T3: `⊤ π₁ π₂ ⟨R,S⟩ × \ /`, `ν`, `μ` -/

/-- `r` cut to the values `K` knows of its sides, `idU X ≫ r ≫ idU L`, a side left whole where it is unknown. -/
def cut {A B : Obj} (K : Known A B) (r : Tab A B) : Except String (Tab A B) := do
  let l ← match K.dom with | some c => do (← Tab.idU c.2).comp r | none => pure r
  match K.ran with | some c => do l.comp (← Tab.idU c.2) | none => pure l

/-- `X × L`: the known domain values by `V`'s values cut to the known range. -/
def top (A B : Obj) (V : Fn false B B) : Fn true A B := .lazy fun K => match K.dom with
  | none => .tab (.error "⊤ ran with its domain unknown")
  | some c => .tab do Tab.top c.2 (← cut ⟨none, K.ran⟩ (← V.runE {})).val
def outl (A B : Obj) : Fn true (.prod A B) A := ofVals _ _ fun X => Tab.outl X
def outr (A B : Obj) : Fn true (.prod A B) B := ofVals _ _ fun X => Tab.outr X
def pair (A B C : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A C) : Fn (d || e) A (.prod B C) :=
  lift2 Tab.pair (fun K => ⟨K.dom, none⟩) (fun K => ⟨K.dom, none⟩) R S
def prod (A B C D : Obj) (R : Fn false A B) (S : Fn false C D) : Fn false (.prod A C) (.prod B D) :=
  lift2 Tab.prod (fun _ => {}) (fun _ => {}) R S
/-- `R/S` and `R\S` read both sides whole, with the universes `UA`, `UB` (`UB`, `UC`); `ldiv` takes tables where
    `Gen.ldivB` takes plans, since the kernel path has no bit matrix. -/
def rdiv (A B C : Obj) (R : Fn false A C) (S : Fn false B C) (UA : Fn false A A) (UB : Fn false B B) :
    Fn false A B :=
  lift2 (fun r s => do Tab.rdiv r s (← UA.runE {}) (← UB.runE {})) (fun _ => {}) (fun _ => {}) R S
def ldiv (A B C : Obj) (R : Fn false A B) (S : Fn false A C) (UB : Fn false B B) (UC : Fn false C C) :
    Fn false B C :=
  lift2 (fun r s => do Tab.ldiv r s (← UB.runE {}) (← UC.runE {})) (fun _ => {}) (fun _ => {}) R S

/-- `νX : S ∩ φ` by plain rounds (`Tab.nu`), no AC-3 delta rounds; `μX : φ` (`Tab.mu`), at most `cap` rounds. -/
def nu (A B : Obj) (S : Fn false A B) (φ : Tab A B → Fn false A B) : Fn false A B :=
  .tab do Tab.nu (fun X => (φ X).runE {}) (← S.runE {})
def mu (A B : Obj) (cap : Nat) (φ : Tab A B → Fn false A B) : Fn false A B :=
  .tab (Tab.mu cap fun X => (φ X).runE {})

end GenK

/-- The rows of `prims` with a kernel body: each row's `Tab` operator, run under the `GenK` twin of the wrapper its
    old constant runs under (`Expand.primE`), as `RowCode` gives the old ones; a row not here keeps a program off
    the kernel path (`Tm.kernelNode`). -/
def kernRows : List (String × Lean.Name) :=
  [("∋", ``Tab.mem), ("τ", ``Tab.tau), ("length", ``Tab.length), ("setify", ``Tab.setify),
   ("snoc", ``Tab.snoc), ("cons", ``Tab.cons), ("cat", ``Tab.cat), ("zip", ``Tab.zip), ("sum", ``Tab.sum),
   ("uncons", ``Tab.uncons), ("unsnoc", ``Tab.unsnoc), ("uncat", ``Tab.uncat), ("inl", ``Tab.inl),
   ("inr", ``Tab.inr)]

-- every kernel row is a row of `prims`
#guard kernRows.all fun (s, _) => prims.any (·.sym == s)

/-- `t`'s own node has a kernel body (`GenK`): T2's `val uni 𝟘 𝟙 ° ≫ ∩ ∪ − dom ran`, and `own`, which runs its
    part; a `var`, bound to a table or a parameter's code; an `arg`, whose head decides (a `call` or a row). -/
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
  | .junc .. | .juncD .. | .fold .. | .foldr .. | .foldI .. | .flat _ => true
  | .prim r => (kernRows.lookup r.sym).isSome
  | .top _ => true
  | .outl => true
  | .outr => true
  | .pair .. => true
  | .prod .. => true
  | .ldiv .. => true
  | .rdiv .. => true
  | .nu .. => true
  | .mu .. => true
  | .var .. => true
  | .arg .. => true
  | _ => false

/-- The nodes of `t` with no kernel body, each as its constructor's index (`Tm.ctorIdx`) and, for a `call`, its
    constant: a call has one where `twin` says its constant has a kernel twin (`Expand.emit` builds one for a
    definition whose body is on the kernel path). A `share` is entered here, though `Tm.parts` does not enter it. -/
partial def Tm.offKernel (twin : Lean.Name → Bool) {A B : Obj} (t : Tm A B) : List (Nat × Lean.Name) :=
  match t with
  | .share _ R => R.offKernel twin
  | .call _ c .. => if twin c then [] else [(t.ctorIdx, c)]
  | t => (if t.kernelNode then [] else [(t.ctorIdx, .anonymous)]) ++ t.parts.flatMap fun ⟨_, _, u⟩ => u.offKernel twin

/-- Every node of `t` has a kernel body: the test that puts a program on the kernel path. -/
def Tm.onKernel (twin : Lean.Name → Bool) {A B : Obj} (t : Tm A B) : Bool := (t.offKernel twin).isEmpty

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

/-! ### T6: `[R,S]`; T8: `⦇e,S⦈`, `⦇e,S⦈ʳ`, `⦇e,S⦈` given a family, `Rᴵ` -/

/-- `[R,S]` = `inl° ≫ R ∪ inr° ≫ S` (`Tab.junc`), both parts read whole. -/
def junc (A B C : Obj) (R : Fn false A C) (S : Fn false B C) : Fn false (.sum A B) C :=
  lift2 Tab.junc (fun _ => {}) (fun _ => {}) R S
/-- `[R,S]` on the sum values `X` in demand: `R` run on the left values `X` holds, `S` on the right, then `idU X ≫`. -/
def juncD (A B C : Obj) (d e : Bool) (R : Fn d A C) (S : Fn e B C) : Fn true (.sum A B) C :=
  ofVals _ _ fun X => do
    let ⟨l, r, _, _, x, y⟩ := X
    (← Tab.idU X).comp (← Tab.junc (← R.runE ⟨some ⟨l, x⟩, none⟩) (← S.runE ⟨some ⟨r, y⟩, none⟩))

/-- Round `k` of a left fold: `cons°` of what is left of each array, its head read now (index `k` from the start). -/
def peelL {K E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← Tab.uncons rest.val)
  pure (← c.comp (← Tab.outl c.val), ← c.comp (← Tab.outr c.val))
/-- Round `k` of a right fold: `snoc°`, its last element read now (index `k` from the end). -/
def peelR {K E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← Tab.unsnoc rest.val)
  pure (← c.comp (← Tab.outr c.val), ← c.comp (← Tab.outl c.val))

/-- `⦇e,S⦈` on the arrays `X` in demand (§4 `fold`: a Lean loop of rounds, `Tab.foldRounds`): each array from every
    value of `e`, round `k` the pairs `(acc, x)` (`⟨P, el⟩`), `S` run on them (`compT`). -/
def fold (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod V E) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => do
    Tab.foldRounds peelL (fun P el => do (compT (P.pair el) S).runE {}) (X.1.toNat + 2) (← Tab.idU X)
      (← Tab.top X (← e.runE {}).val) (← Tab.zero)
/-- `⦇e,S⦈ʳ`: the mirror, each array from its end, `S` on `(x, acc)` (`⟨el, P⟩`). -/
def foldr (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod E V) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => do
    Tab.foldRounds peelR (fun P el => do (compT (el.pair P) S).runE {}) (X.1.toNat + 2) (← Tab.idU X)
      (← Tab.top X (← e.runE {}).val) (← Tab.zero)

/-- `⦇e,S⦈` given a family on the pairs `X = (i, xs)` in demand (`foldIDen_eq`): one left fold on the carrier `I×V`
    from `(i, b)`, `b` from `e` at `i`; each round's step `S` met with `⟨π₁, S ≫ π₂⟩`, so it keeps the key's `i`. -/
def foldI (I E V : Obj) (d d' : Bool) (e : Fn d I (.prod V V)) (S : Fn d' (.prod (.prod I V) E) (.prod I V)) :
    Fn true (.prod I (.arr E)) V := ofVals _ _ fun X => do
  let i ← Tab.outl X
  let es ← (compT (.ok i) e).runE {}
  let step (P : Tab _ (.prod I V)) (el : Tab _ E) : Except String (Tab _ (.prod I V)) := do
    let s ← (compT (P.pair el) S).runE {}
    s.inter (← i.pair (← s.comp (← Tab.outr s.val)))
  let out ← Tab.foldRounds peelL step (X.2.1.toNat + 2) (← Tab.outr X) (← i.pair (← es.comp (← Tab.outr es.val)))
    (← Tab.zero)
  out.comp (← Tab.outr out.val)

/-- `Rᴵ` on the pairs `X = (i, a)` in demand (`Tab.flat`), `R` run on their keys `i`. -/
def flat (I A B : Obj) (d : Bool) (R : Fn d I (.prod A B)) : Fn true (.prod I A) B :=
  ofVals _ _ fun X => do Tab.flat X (← R.runE ⟨some ⟨_, X.1⟩, none⟩)

end GenK

end Rel.Lang
