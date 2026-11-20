import Rel.Run.Lang.Gen
import Rel.Run.Lang.Tm
import Rel.Run.SetOps
import Rel.Run.Comp
import Rel.Run.Struct
import Rel.Run.Power
import Rel.Run.List
import Rel.Run.Div
import Rel.Run.Bits
import Rel.Run.Fix
import Rel.Run.Where

/-! The code a program runs: one body per node of its terms (`Tm.onKernel`), each a composition of the `Tab`
    operators over the five kernels. A `tab` holds the message of the op that could not run, never a dropped
    error. `≫` and `\` take a bit matrix by `Tab.bitsWin` (`Tab.compSel`, `Tab.ldivSel`). -/

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

/-- `r ≫ s` (`Tab.compSelM`): its bit matrix kept as `bits` where `Tab.bitsWin` takes it, else its table. -/
def compR {A B C : Obj} (r : Tab A B) (s : Tab B C) : Rel A C := match Tab.compSelM Tab.bitsMax r s with
  | .ok (.inr (g, w, o, ra, rc)) => .bits g w o r.key ra s.val rc
  | .ok (.inl t) => .tab (.ok t)
  | .error e => .tab (.error e)

/-- `r ≫ S`, `S` a table or a bit matrix: a matrix within `Tab.bitsMax` is composed on its bits
    (`Tab.compTabMat`), so it is never read back as rows; else as `compR`. -/
def compV {A B C : Obj} (r : Tab A B) : Rel B C → Rel A C
  | .bits g w o x ra y rc => match Tab.compTabMat r g w o x ra with
    | .ok (ka, o', ⟨_, key⟩, ra') =>
      if ka.toNat * w.toNat ≤ Tab.bitsMax then .bits ka w o' key ra' y rc
      else match Tab.ofBits g w o x ra y rc with | .ok s => compR r s | .error e => .tab (.error e)
    | .error e => .tab (.error e)
  | S => match S.runE {} with | .ok s => compR r s | .error e => .tab (.error e)

/-- `r S`, `r` the table of `R`: a table or a bit matrix `S` is composed now; a lazy one runs knowing its domain is
    `ran(r)`, and not at all where `r` has no row. -/
def compT {A B C : Obj} : Except String (Tab A B) → Rel B C → Rel A C
  | .error e, _ => .tab (.error e)
  | .ok r, .lazy g => if r.n == 0 then .tab Tab.zero else
    .lazy fun K => match Tab.ran r with
      | .ok d => compV r ((Rel.lazy g).force ⟨some ⟨d.n, d.key⟩, K.ran⟩)
      | .error e => .tab (.error e)
  | .ok r, S => compV r S

/-- `R s`, `s` the table of `S`: the mirror of `compT`, `R` run knowing its domain is `D` (what the context knows)
    and its range is `s`'s key column. -/
def compS {A B C : Obj} (R : Rel A B) (D : Option ((n : USize) × Vals A n)) : Except String (Tab B C) → Rel A C
  | .error e => .tab (.error e)
  | .ok s => match R.runE ⟨D, some ⟨s.n, s.key⟩⟩ with | .ok r => compR r s | .error e => .tab (.error e)

/-- `R S` (`Tab.compSel`: a bit matrix where `Tab.bitsWin` holds), `R` lazy: one operand runs first on the side of
    the context it touches and hands its other side to the second as a bound (§0) — `S` where it is a table or the
    context bounds only the range, else `R`; where the first cannot run, the other goes first. -/
def comp (A B C : Obj) (e : Bool) (R : Fn true A B) (S : Fn e B C) : Fn true A C := match R with
  | .tab r => compT r S
  | R@(.bits ..) => compT (R.runE {}) S
  | .lazy f => .lazy fun K => match S with
    | .tab s => compS (.lazy f) K.dom s
    | S => if K.dom.isNone && K.ran.isSome then
        match S.runE ⟨none, K.ran⟩ with
        | .ok s => compS (.lazy f) K.dom (.ok s)
        | .error _ => compT ((Rel.lazy f).runE ⟨K.dom, none⟩) S
      else match (Rel.lazy f).runE ⟨K.dom, none⟩ with
        | .ok r => compT (.ok r) S
        | .error _ => compS (.lazy f) K.dom (S.runE ⟨none, K.ran⟩)

/-- The code of a closed term with `dem = false` as its table, computed once: such a term has one table whatever
    the context, so this changes no result and saves re-running it at each use (a fold reading it in every round). -/
def memo (A B : Obj) : Rel A B → Rel A B
  | .tab t => .tab t
  -- a lazy one that cannot run closed (`<` on an infinite universe) needs its context: kept lazy, never frozen
  | .lazy f => match (Rel.lazy f).runE {} with | .ok t => .tab (.ok t) | .error _ => .lazy f
  | R => .tab (R.runE {})

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

/-- `r` cut to the values `K` knows of its sides, `idU X ≫ r ≫ idU L`, a side left whole where it is unknown. -/
def cut {A B : Obj} (K : Known A B) (r : Tab A B) : Except String (Tab A B) := do
  let l ← match K.dom with | some c => do (← Tab.idU c.2).comp r | none => pure r
  match K.ran with | some c => do l.comp (← Tab.idU c.2) | none => pure l

/-- `R ∩ S` of two values that are no `lazy`: a table met with a bit matrix keeps its rows whose bit is set
    (`Tab.keepBits`), so the matrix is never read back as rows; else `Tab.inter` of the two tables. -/
def meetV {A B : Obj} : Rel A B → Rel A B → Rel A B
  | .bits g w o x ra y rc, .tab t | .tab t, .bits g w o x ra y rc => .tab (t >>= (Tab.keepBits · g w o x ra y rc))
  | R, S => .tab do Tab.inter (← R.runE {}) (← S.runE {})

/-- `r` cut to `K`'s sides (`cut`), and the context its own sides make: beside a table `t` with `dom t ⊆ K`,
    `ran t ⊆ L`, `(K ≫ S ≫ L) ∩ t = S ∩ t`, so the other operand of `∩` or `−` runs knowing only `t`'s sides. -/
def bound {A B : Obj} (K : Known A B) (r : Tab A B) : Except String (Tab A B × Known A B) := do
  let t ← cut K r; let d ← Tab.dom t; let l ← Tab.ran t
  pure (t, ⟨some ⟨d.n, d.key⟩, some ⟨l.n, l.key⟩⟩)

/-- `T ∩ S` in `K`, `T` already run: a table bounds `S` (`bound`); anything else meets `S` run on `K`. -/
def meetOn {A B : Obj} (K : Known A B) (T S : Rel A B) : Rel A B := match T with
  | .tab (.ok r) => match bound K r with
    | .ok p => meetV (.tab (.ok p.1)) (S.force p.2)
    | .error e => .tab (.error e)
  | T => meetV T (S.force K)

/-- `R ∩ S` in `K`: the operand that is no `lazy` runs first and bounds the other (`meetOn`); of two lazy ones `R`,
    or `S` where `R` cannot run on `K` alone. -/
def meetK {A B : Obj} (K : Known A B) (R S : Rel A B) : Rel A B := match R, S with
  | .lazy _, .lazy _ => match R.force K with
    | .tab (.error _) => meetOn K (S.force K) R
    | R' => meetOn K R' S
  | .lazy _, S => meetOn K S R
  | R, S => meetOn K R S

def meet (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B := match R, S with
  | .lazy _, _ | _, .lazy _ => .lazy fun K => meetK K R S
  | R, S => meetV R S
def join (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 Tab.union (fun K => K) (fun K => K) R S
/-- `R − S`: a lazy `S` is needed only on `R`'s pairs, so it runs knowing `R`'s sides (`bound`). -/
def diff (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B := match S with
  | .lazy _ => .lazy fun K => .tab do let p ← bound K (← R.runE K); Tab.diff p.1 (← S.runE p.2)
  | S => lift2 Tab.diff (fun K => K) (fun K => K) R S
/-- A coreflexive's two sides are one value set, so either side the context knows bounds `R`'s side. -/
def dom (A B : Obj) (d : Bool) (R : Fn d A B) : Fn d A A := lift1 Tab.dom (fun K => ⟨K.dom <|> K.ran, none⟩) R
def ran (A B : Obj) (R : Fn false A B) : Fn false B B := lift1 Tab.ran (fun K => ⟨none, K.dom <|> K.ran⟩) R

/-! ### T3: `⊤ π₁ π₂ ⟨R,S⟩ × \ /`, `ν`, `μ` -/

/-- `X × L`: the known domain values by `V`'s values cut to the known range. -/
def top (A B : Obj) (V : Fn false B B) : Fn true A B := .lazy fun K => match K.dom with
  | none => .tab (.error "⊤ ran with its domain unknown")
  | some c => .tab do Tab.top c.2 (← cut ⟨none, K.ran⟩ (← V.runE {})).val
def outl (A B : Obj) : Fn true (.prod A B) A := ofVals _ _ fun X => Tab.outl X
def outr (A B : Obj) : Fn true (.prod A B) B := ofVals _ _ fun X => Tab.outr X
def pair (A B C : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A C) : Fn (d || e) A (.prod B C) :=
  lift2 Tab.pair (fun K => ⟨K.dom, none⟩) (fun K => ⟨K.dom, none⟩) R S
/-- `R × S`: on the pairs `Z` a context knows, `⟨π₁ ≫ R, π₂ ≫ S⟩` on `Z`, each operand run knowing its domain is that
    side of `Z`; where none is known, CROSS of the two tables. -/
def prod (A B C D : Obj) (R : Fn false A B) (S : Fn false C D) : Fn false (.prod A C) (.prod B D) :=
  .lazy fun K => .tab <| match K.dom with
    | some ⟨n, Z⟩ => do
      let l ← (← Tab.outl Z).comp (← R.runE ⟨some ⟨n, Z.1⟩, none⟩)
      l.pair (← (← Tab.outr Z).comp (← S.runE ⟨some ⟨n, Z.2⟩, none⟩))
    | none => do Tab.prod (← R.runE {}) (← S.runE {})
/-- `R/S` and `R\S` read both sides whole, with the universes `UA`, `UB` (`UB`, `UC`); `ldiv` is `Tab.ldivSel`, a bit
    matrix where `Tab.bitsWin` holds. -/
def rdiv (A B C : Obj) (R : Fn false A C) (S : Fn false B C) (UA : Fn false A A) (UB : Fn false B B) :
    Fn false A B :=
  lift2 (fun r s => do (← Tab.ldivSel Tab.bitsMax (← s.conv) (← r.conv) (← UB.runE {}) (← UA.runE {})).conv)
    (fun _ => {}) (fun _ => {}) R S
/-- `r \ M` within `ub`, `uc`, `M` a bit matrix: divided on its bits (`Tab.ldivTabMat`) and kept a matrix; read back
    and `Tab.ldivSel` only where the answer would pass `Tab.bitsMax`. -/
def ldivM {A B C : Obj} (r : Tab A B) (ub : Tab B B) (uc : Tab C C) {n m : USize} (g w : USize) (o : Enc)
    (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) : Rel B C :=
  match Tab.ldivTabMat r ub uc g w o x ra y rc with
  | .ok (some (kb, kc, o', ⟨_, zb⟩, rb, ⟨_, zc⟩, rc')) => .bits kb kc o' zb rb zc rc'
  | .ok none => .tab do Tab.ldivSel Tab.bitsMax r (← Tab.ofBits g w o x ra y rc) ub uc
  | .error e => .tab (.error e)

def ldiv (A B C : Obj) (R : Fn false A B) (S : Fn false A C) (UB : Fn false B B) (UC : Fn false C C) :
    Fn false B C := match S.force {} with
  | .bits g w o x ra y rc => match R.runE {}, UB.runE {}, UC.runE {} with
    | .ok r, .ok ub, .ok uc => ldivM r ub uc g w o x ra y rc
    | .error e, _, _ | _, .error e, _ | _, _, .error e => .tab (.error e)
  | S => lift2 (fun r s => do Tab.ldivSel Tab.bitsMax r s (← UB.runE {}) (← UC.runE {})) (fun _ => {}) (fun _ => {}) R S

/-- `νX : S ∩ φ` by plain rounds (`Tab.nu`), no AC-3 delta rounds; `μX : φ` (`Tab.mu`), at most `cap` rounds. -/
def nu (A B : Obj) (S : Fn false A B) (φ : Tab A B → Fn false A B) : Fn false A B :=
  .tab do Tab.nu (fun X => (φ X).runE {}) (← S.runE {})
def mu (A B : Obj) (what : String) (cap : Nat) (φ : Tab A B → Fn false A B) : Fn false A B :=
  .tab (Tab.mu what cap fun X => (φ X).runE {})

end GenK

/-- The rows of `prims` with a kernel body: each row's `Tab` operator, run under the `GenK` twin of the wrapper its
    old constant runs under (`Expand.primE`), as `RowCode` gives the old ones; a row not here keeps a program off
    the kernel path (`Tm.kernelNode`). -/
def kernRows : List (String × Lean.Name) :=
  [("∋", ``Tab.mem), ("τ", ``Tab.tau), ("length", ``Tab.length), ("setify", ``Tab.setify),
   ("snoc", ``Tab.snoc), ("cons", ``Tab.cons), ("cat", ``Tab.cat), ("zip", ``Tab.zip), ("sum", ``Tab.sum),
   ("uncons", ``Tab.uncons), ("unsnoc", ``Tab.unsnoc), ("uncat", ``Tab.uncat), ("inl", ``Tab.inl),
   ("inr", ``Tab.inr), ("prefix", ``Tab.«prefix»), ("suffix", ``Tab.suffix),
   ("inits", ``Tab.inits),
   ("tails", ``Tab.tails),
   ("concat", ``Tab.flatten),
   ("filter", ``Tab.filter),
   ("positions", ``Tab.positions),
   ("takewhile", ``Tab.takewhile),
   ("loop", ``Tab.loop),
   ("merge", ``Tab.merge),
   ("thinL", ``Tab.thinL),
   ("F", ``Tab.map)]

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
  | .hylo .. => true
  | .var .. => true
  | .arg .. => true
  | _ => false

/-- The nodes of `t` with no kernel body, each as its constructor's index (`Tm.ctorIdx`) and what names it: for a
    `call` its constant, for a `prim` its row's symbol, else `""`. A call has one where `twin` says its constant has
    a kernel twin (`Expand.emit` builds one for a definition whose body is on the kernel path). A `share` is entered
    here, though `Tm.parts` does not enter it. -/
partial def Tm.offKernel (twin : Lean.Name → Bool) {A B : Obj} (t : Tm A B) : List (Nat × String) :=
  match t with
  | .share _ R => R.offKernel twin
  | .call _ c .. | .callCv _ c .. => if twin c then [] else [(t.ctorIdx, toString c)]
  | t => (if t.kernelNode then [] else [(t.ctorIdx, match t with | .prim r => r.sym | _ => "")]) ++
    t.parts.flatMap fun ⟨_, _, u⟩ => u.offKernel twin

/-- Every node of `t` has a kernel body: the test that puts a program on the kernel path. -/
def Tm.onKernel (twin : Lean.Name → Bool) {A B : Obj} (t : Tm A B) : Bool := (t.offKernel twin).isEmpty

/-! ### T4, T5: `≤ < succ`, the value verbs, `Λ E nil est thin at`, and the wrapper `after` of the rows -/

namespace GenK

open Rel Gen

/-- A row composed after the keys: `f` on the coreflexive of the values the context knows (`Gen.after`'s rule). -/
def after (A B : Obj) (f : {K : Obj} → Tab K A → Except String (Tab K B)) : Fn true A B :=
  ofVals A B fun X => do f (← Tab.idU X)

/-- `succ`, a value verb on `U`'s universe: the keys' coreflexive `D`, then `D ≫ succDen U` (`Tab.succ`),
    `D ≫ arithDen k U` (`Tab.arith`), `U` run knowing its domain is the values each step asks about, so an infinite
    universe (`𝟙`) is as good as a table. -/
def succ (U : Fn false .long .long) : Fn true .long .long :=
  after _ _ fun D => Tab.succ D fun X => U.runE ⟨some ⟨_, X⟩, none⟩
def arith (k : UInt8) (U : Fn false .long .long) : Fn true (.prod .long .long) .long :=
  after _ _ fun D => Tab.arith k D fun X => U.runE ⟨some ⟨_, X⟩, none⟩

/-- One side of `cmp`: `U` run knowing its domain is the values `s` the context knows of that side, its `dom`, cut
    to `s` (`idU ≫ dom U`); `dom U` run closed where the context knows none, and where that fails (an infinite
    universe, `𝟙`) the message naming `op` and the side `w`. -/
def cmpSide (op w : String) (U : Rel .long .long) (s : Option ((n : USize) × Vals .long n)) :
    Except String ((n : USize) × Vals .long n) := do
  let u ← (U.runE ⟨s, none⟩).mapError fun e => if s.isSome then e else
    s!"{op} on an unbounded object: nothing bounds its {w} side; compose it with a table on that side ({e})"
  let d ← u.dom
  s.elim (pure ⟨d.n, d.key⟩) fun c => do let t ← (← Tab.idU c.2).comp d; pure ⟨t.n, t.key⟩

/-- `K ≫ op ≫ L` on `U`'s universe (`Tab.leq`, `Tab.lt`, CROSS of the two sides `cmpSide` reads, §0 `Known`). -/
def cmp (op : String) (f : {n m : USize} → Vals .long n → Vals .long m → Except String (Tab .long .long))
    (U : Fn false .long .long) : Fn false .long .long := .lazy fun K => .tab do
  let k ← cmpSide op "left" U K.dom; let l ← cmpSide op "right" U K.ran
  f k.2 l.2
def leq (U : Fn false .long .long) : Fn false .long .long := cmp "≤" Tab.leq U
def lt (U : Fn false .long .long) : Fn false .long .long := cmp "<" Tab.lt U

/-- `Λ(R)` on the keys `X` (`Tab.lam`), `R` run knowing its domain is `X`. -/
def lam (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true A (.arr B) :=
  ofVals _ _ fun X => do Tab.lam X (← R.runE ⟨some ⟨_, X⟩, none⟩)
/-- `E(R) = Λ(∋ ≫ R)` (`Tab.E`'s composition): `R` runs knowing its domain is `ran(∋)` at the arrays in demand. -/
def E (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true (.arr A) (.arr B) :=
  lam _ _ true (comp _ _ _ d (ofVals _ _ fun X => Tab.mem X) R)
def nil (A B : Obj) : Fn true A (.arr B) := ofVals _ _ fun X => Tab.nil X
/-- `f` on `R` run knowing its domain is `ran(∋)` at the arrays `X` in demand (`Gen.elems`' rule): the wrapper of the
    rows given a relation on elements (`filter`, `takewhile`). -/
def elems (A B C : Obj) (d : Bool) (R : Fn d A B)
    (f : {n : USize} → Tab A B → Vals (.arr A) n → Except String (Tab (.arr A) C)) : Fn true (.arr A) C :=
  ofVals _ _ fun X => do let k ← (← Tab.mem X).ran; f (← R.runE ⟨some ⟨k.n, k.key⟩, none⟩) X

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

/-- `⦇e,S⦈` on the arrays `X` in demand (§4 `fold`: a Lean loop of rounds, `Tab.foldRounds`): each array from every
    value of `e`, round `k` the pairs `(acc, x)` (`⟨P, el⟩`), `S` run on them (`compT`). -/
def fold (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod V E) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => do
    Tab.foldRounds Tab.peelL (fun P el => do (compT (P.pair el) S).runE {}) (X.1.toNat + 2) (← Tab.idU X)
      (← Tab.top X (← e.runE {}).val) (← Tab.zero)
/-- `⦇e,S⦈ʳ`: the mirror, each array from its end, `S` on `(x, acc)` (`⟨el, P⟩`). -/
def foldr (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod E V) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => do
    Tab.foldRounds Tab.peelR (fun P el => do (compT (el.pair P) S).runE {}) (X.1.toNat + 2) (← Tab.idU X)
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
  let out ← Tab.foldRounds Tab.peelL step (X.2.1.toNat + 2) (← Tab.outr X) (← i.pair (← es.comp (← Tab.outr es.val)))
    (← Tab.zero)
  out.comp (← Tab.outr out.val)

/-- `Rᴵ` on the pairs `X = (i, a)` in demand (`Tab.flat`), `R` run on their keys `i`. -/
def flat (I A B : Obj) (d : Bool) (R : Fn d I (.prod A B)) : Fn true (.prod I A) B :=
  ofVals _ _ fun X => do Tab.flat X (← R.runE ⟨some ⟨_, X.1⟩, none⟩)

/-! ### T9: `hylo(c, S)`, and the wrappers of the rows given a pair test or a step (`merge thinL loop`) -/

/-- The twins of `Gen.testVals`, `Gen.testAfter`: the row's `Tab` operator given `Q` as its pair test, run knowing its
    domain is the pairs `D` it is asked about (`est`'s rule); on the values in demand, or composed after them. -/
def testVals (B A C : Obj) (Q : Fn true (.prod B B) (.prod B B))
    (f : {n : USize} → (Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))) → Vals A n →
      Except String (Tab A C)) : Fn true A C :=
  ofVals _ _ fun X => f (fun D => Q.runE ⟨some ⟨D.n, D.val⟩, none⟩) X
def testAfter (B A C : Obj) (Q : Fn true (.prod B B) (.prod B B))
    (f : {K : Obj} → (Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))) → Tab K A →
      Except String (Tab K C)) : Fn true A C :=
  after _ _ fun P => f (fun D => Q.runE ⟨some ⟨D.n, D.val⟩, none⟩) P
/-- The twin of `Gen.stepAfter`: the step `F` given the coreflexive `D` of the pairs a round meets, `D ≫ F`
    (`compT`: not run on no pair). -/
def stepAfter (S T A C : Obj) (d : Bool) (F : Fn d S T)
    (f : {K : Obj} → (Tab S S → Except String (Tab S T)) → Tab K A → Except String (Tab K C)) : Fn true A C :=
  after _ _ fun P => f (fun D => (compT (.ok D) F).runE {}) P

/-- What the hylo `what` reports when its coalgebra reaches a node from itself, on either path (`Expand.mus`). -/
def cycleMsg (what : String) : String := s!"{what} reaches a node from itself, so it is not well-founded there"

/-- `hylo(c, S)` = `μX : c G(X) S` on the keys `D` in demand: the nodes `N = μN : D ∪ ran(N ≫ ch)` the children `ch`
    reach (`Tab.mu`), then `D ≫ μX : N ≫ φ(X)` (`Tab.mu`, as `GenK.mu`), `φ` read only at the nodes. A node of height
    `h` has its value from round `h + 1` on, so `|N| + 2` rounds reach the fixed point where `ch` has no cycle on `N`.
    A cycle fails it (`Gen.hylo`'s rule): the nodes with an endless descent, `νP : dom(N ≫ ch ≫ P)` from `N`, are
    those that reach a node from themselves, where the least fixed point would be a silent `𝟘`. -/
def hylo (A B : Obj) (what : String) (d e : Bool) (ch : Fn d A A) (φ : Tab A B → Fn e A B) : Fn true A B :=
  ofVals _ _ fun X => do
  let D ← Tab.idU X
  let N ← Tab.mu what USize.size fun N => do D.union (← (← (compT (.ok N) ch).runE {}).ran)
  let C ← (compT (.ok N) ch).runE {}
  let cyc ← Tab.nu (fun P => do (← C.comp P).dom) N
  if cyc.n != 0 then throw s!"{cycleMsg what} ({cyc.n} of {N.n} nodes)"
  D.comp (← Tab.mu what (N.n.toNat + 3) fun Y => (compT (.ok N) (φ Y)).runE {})

end GenK

end Rel.Lang
