import Rel.Run.AC3Def
import Rel.Run.CRelDef
import Rel.Run.CRelArithDef
import Rel.Run.CRelRelDef
import Rel.Run.CRelListDef
import Rel.Run.CRelFoldDef
import Rel.Run.CRelPowerDef
import Rel.Run.CRelLoopDef
import Rel.Run.CRelEstDef
import Rel.Run.Lang.Bits
import Rel.Run.Lang.Lazy

/-! The code a `rel_program` definition expands into (`Expand`): one function per core-term constructor, each
    a composition of `CRel` ops, so a definition is an ordinary Lean term over `CRel` and its ok bit is the `&&`
    of the ops it ran. A term that runs on demand (§a) is a function of its keys, `Dem true A`; a closed one of
    `Dem false A = Unit`. A closed term over `≫`/`∩`/`−`/`\` runs as a bit-matrix plan (`Bits.runC`), each node of
    the plan built by the `p*` functions below on the demand its parent gives it. -/

open Rel.Ext

namespace Rel.Lang

open Tab Rel.Alg

/-- The keys a term reads: a coreflexive when it runs on demand, nothing when it is closed. -/
@[reducible] def Dem : Bool → Obj → Type
  | true, A => Tab A A
  | false, _ => Unit

def Dem.of {A : Obj} : (d : Bool) → Tab A A → Dem d A
  | true, D => D
  | false, _ => ()

namespace Gen

open Rel Rel.Dep Rel.Kernel
open Rel.CRel (ofC)

/-- A term's code: its relation, a table run now or a function of what its context knows of its sides. `d` is
    phantom: the combinators still dispatch on it until they match on `tab`/`lazy` (3.6). -/
abbrev Fn (_d : Bool) (A B : Obj) := Rel A B

/-- The table `f` computes closed, or on the keys `D` (its domain known as `D`'s values): the view the
    combinators read until 3.6. -/
def Fn.at {A B : Obj} : {d : Bool} → Fn d A B → Dem d A → CRel A B
  | false, f, _ => f.run {}
  | true, f, D => f.run ⟨some ⟨D.n, D.val⟩, none⟩

/-- A term's bit-matrix plan and the ok bit of the tables at its leaves: closed, computed once where first read
    (a `Thunk`, so a closed node read every round of a fold is planned once); or on the keys `D` it is given, the
    shape of `Rel`'s `tab`/`lazy`. -/
inductive Pl (A B : Obj) where
  | closed (p : Thunk (Tm A B × Bool))
  | on (f : Tab A A → Tm A B × Bool)

/-- The plan on the keys `D`: a closed plan ignores them. -/
def Pl.at {A B : Obj} : Pl A B → Tab A A → Tm A B × Bool
  | .closed p, _ => p.get
  | .on f, D => f D

/-- The plan where no key is given: a closed plan's; one on keys vouches for nothing there (bit false). -/
def Pl.get {A B : Obj} : Pl A B → Tm A B × Bool
  | .closed p => p.get
  | .on _ => (.zero, false)

/-- `f` on the plans of `R` and `S`: closed where both are, else on the keys both are given. -/
def Pl.map2 {A B C E : Obj} (f : Tm A B × Bool → Tm A C × Bool → Tm A E × Bool) :
    Pl A B → Pl A C → Pl A E
  | .closed r, .closed s => .closed (Thunk.mk fun _ => f r.get s.get)
  | R, S => .on fun D => f (R.at D) (S.at D)

/-- A definition's value with its objects: what `rel_program n` lists as `n.expanded`. -/
abbrev Gv := (A : Obj) × (B : Obj) × CRel A B

def entry (n : String) (A B : Obj) (c : CRel A B) : String × Gv := (n, ⟨A, B, c⟩)


/-- `r` with the bits `b` of the ops that computed its inputs outside it. -/
def also {A B : Obj} (b : Bool) (r : CRel A B) : CRel A B := CRel.mk r.rel (b && r.ok)

/-! ### Leaves: the values `build` put in the term, rebuilt from their payloads -/

/-- The bytes of the hex text `s` (two lowercase digits a byte, as `Expand.hex` writes them). One string
    literal per column, so a column of any size is one node of the generated term. -/
def unhex (s : String) : ByteArray := Id.run do
  let u := s.toUTF8; let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
  let mut b := ByteArray.emptyWithCapacity (u.size / 2)
  for h : i in [0:u.size / 2] do
    have := h.upper; b := b.push (d u[2 * i] * 16 + d u[2 * i + 1])
  pure b

/-- The column of `t` whose payload is the hex text `s`, `bits` a boolean's (`Enc.bits`), else `Enc.bytes`, and
    its fit as its ok bit: `Enc.WF` is decided, so a payload that does not fit `n` is a blank column with bit
    false, never a wrong column read as right. -/
def atom (t : QAtomicType) (n : USize) (bits : Bool) (s : String) : Arr t n × Bool :=
  let e := if bits then Enc.bits (unhex s) else Enc.bytes (unhex s)
  if h : Enc.WF t n e then (Arr.mk e h, true) else (Arr.mk (Enc.blank t n) (Enc.blank_WF t n), false)

/-- A rebuilt column from its rebuilt parts, its bit the `&&` of theirs. -/
def pairV (A B : Obj) (n : USize) (x : Vals A n × Bool) (y : Vals B n × Bool) : Vals (.prod A B) n × Bool :=
  ((x.1, y.1), x.2 && y.2)
def arrV (B : Obj) (n m : USize) (lo hi : Arr .long n × Bool) (p : Vals B m × Bool) : Vals (.arr B) n × Bool :=
  (⟨m, lo.1, hi.1, p.1⟩, lo.2 && hi.2 && p.2)
def sumV (A B : Obj) (n l r : USize) (tag : Arr .boolean n × Bool) (idx : Arr .long n × Bool) (x : Vals A l × Bool)
    (y : Vals B r × Bool) : Vals (.sum A B) n × Bool :=
  (⟨l, r, tag.1, idx.1, x.1, y.1⟩, tag.2 && idx.2 && x.2 && y.2)
def relV (A B : Obj) (n : USize) (k : Vals A n × Bool) (v : Vals B n × Bool) : Tab A B × Bool :=
  (⟨n, k.1, v.1⟩, k.2 && v.2)

/-! ### Code -/

/-- A closed leaf: its table, run now whatever its context knows. -/
def const (A B : Obj) (c : CRel A B) : Fn false A B := .tab c
def val (A B : Obj) (R : Tab A B × Bool) : Fn false A B := const A B (ofC R)
def uni (A : Obj) (m : USize) (U : Vals A m × Bool) : Fn false A A := const A A (CRel.mk (idU U.1) U.2)
def zero (A B : Obj) : Fn false A B := const A B (some Alg.zero)

/-- A leaf on demand: `f` on the values its context knows its domain to hold, a run past capacity where the
    domain is unknown. Every leaf on demand is one, a row of `prims` read on its keys' values included. -/
def ofVals (A B : Obj) (f : {n : USize} → Vals A n → CRel A B) : Fn true A B :=
  .lazy fun K => K.dom.elim (.tab none) fun c => .tab (f c.2)

/-- Code on the keys `D` as a `Fn`: closed, its table; on demand, run on the coreflexive of the domain's known
    values. The form the combinators keep until 3.6 (`GenSpec.KSound.reps`). -/
def Fn.ofDem {A B : Obj} : {d : Bool} → (Dem d A → CRel A B) → Fn d A B
  | false, g => const A B (g ())
  | true, g => ofVals A B fun X => g (idU X)

/-- `r` cut to the values `K` knows of its sides, `idU X ≫ r ≫ idU L`, a side left whole where it is unknown. -/
def cut {A B : Obj} (K : Known A B) (r : CRel A B) : CRel A B :=
  let l := K.dom.elim r fun c => CRel.comp (some (idU c.2)) r
  K.ran.elim l fun c => CRel.comp l (some (idU c.2))

def id (A : Obj) : Fn true A A := ofVals A A fun X => ofC (idU X, true)
/-- `X × L`: the known domain values by `V`'s universe cut to the known range. -/
def top (A B : Obj) (V : Fn false B B) : Fn true A B := .lazy fun K => K.dom.elim (.tab none) fun c =>
  let v := cut ⟨none, K.ran⟩ (V.at ()); .tab (also v.ok (ofC (topC c.2 v.rel.val)))
def outl (A B : Obj) : Fn true (.prod A B) A := ofVals _ _ fun X => ofC (Alg.outl (idU X), true)
def outr (A B : Obj) : Fn true (.prod A B) B := ofVals _ _ fun X => ofC (Alg.outr (idU X), true)

/-- The demand of `S` in `R S` where `S` takes one: `ran(R)`, `R`'s plan run for it, `ranC`'s bit kept so the
    demand is proved a coreflexive on `R`'s range (`GenSpec.demP_spec`). -/
def demP {A B : Obj} (r : Tm A B) : Tab B B × Bool :=
  let x := Bits.runC r; let k := ranC x.1; (k.1, x.2 && k.2)

/-- `r S`, `r` the table of `R`: a table `S` is composed now; a lazy one runs knowing its domain is `r`'s value
    column, and not at all where `r` has no row. -/
def compT {A B C : Obj} : CRel A B → Rel B C → Rel A C
  | none, _ => .tab none
  | some r, .tab s => .tab (CRel.comp (some r) s)
  | some r, .lazy g => if r.n == 0 then .tab (some Alg.zero) else
    .lazy fun K => let d := ranC r
      .tab (also d.2 (CRel.comp (some r) ((Rel.lazy g).run ⟨some ⟨d.1.n, d.1.key⟩, K.ran⟩)))

/-- `R s`, `s` the table of `S`: the mirror of `compT`, `R` run knowing its range is `s`'s key column. -/
def compS {A B C : Obj} (R : Rel A B) : CRel B C → Rel A C
  | none => .tab none
  | some s => .tab (CRel.comp (R.run ⟨none, some ⟨s.n, s.key⟩⟩) (some s))

/-- `R S`: a lazy `R` starts from the side its context knows — the domain, then `compT`; only the range, `S`
    first on it, then `compS` — since `R` run on neither side enumerates its universe. -/
def comp (A B C : Obj) (e : Bool) (R : Fn true A B) (S : Fn e B C) : Fn true A C := match R with
  | .tab r => compT r S
  | .lazy f => .lazy fun
    | ⟨none, some L⟩ => compS (.lazy f) (S.run ⟨none, some L⟩)
    | K => compT ((Rel.lazy f).run ⟨K.dom, none⟩) S

/-- An op on one table: a table now, or lazy, its argument run on what `k` makes of the context. -/
def lift1 {A B C D : Obj} (f : CRel A B → CRel C D) (k : Known C D → Known A B) : Rel A B → Rel C D
  | .tab r => .tab (f r)
  | R => .lazy fun K => .tab (f (R.run (k K)))

/-- An op on two tables: a table where both are, else lazy, each run on what `kl`, `kr` make of the context. -/
def lift2 {A B C D E F : Obj} (f : CRel A B → CRel C D → CRel E F) (kl : Known E F → Known A B)
    (kr : Known E F → Known C D) : Rel A B → Rel C D → Rel E F
  | .tab r, .tab s => .tab (f r s)
  | R, S => .lazy fun K => .tab (f (R.run (kl K)) (S.run (kr K)))

def conv (A B : Obj) (R : Fn false A B) : Fn false B A :=
  lift1 (fun r => ofC (r.rel°, r.ok)) (fun K => ⟨K.ran, K.dom⟩) R
def meet (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 CRel.inter (fun K => K) (fun K => K) R S
def join (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 CRel.union (fun K => K) (fun K => K) R S
def diff (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B :=
  lift2 CRel.diff (fun K => K) (fun K => K) R S
def dom (A B : Obj) (d : Bool) (R : Fn d A B) : Fn d A A := lift1 CRel.dom (fun K => ⟨K.dom, none⟩) R
def ran (A B : Obj) (R : Fn false A B) : Fn false B B := lift1 CRel.ran (fun K => ⟨none, K.dom⟩) R
/-- `R/S` reads both sides whole, with the universes `UA`, `UB`. -/
def rdiv (A B C : Obj) (R : Fn false A C) (S : Fn false B C) (UA : Fn false A A) (UB : Fn false B B) :
    Fn false A B :=
  lift2 (fun r s => let ua : CRel A A := UA.run {}; let ub : CRel B B := UB.run {}
    also (ua.ok && ub.ok) (CRel.rightDiv r s ua.rel.val ub.rel.val)) (fun _ => {}) (fun _ => {}) R S
def pair (A B C : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A C) : Fn (d || e) A (.prod B C) :=
  lift2 CRel.pair (fun K => ⟨K.dom, none⟩) (fun K => ⟨K.dom, none⟩) R S
def prod (A B C D : Obj) (R : Fn false A B) (S : Fn false C D) : Fn false (.prod A C) (.prod B D) :=
  lift2 CRel.prod (fun _ => {}) (fun _ => {}) R S
def junc (A B C : Obj) (R : Fn false A C) (S : Fn false B C) : Fn false (.sum A B) C :=
  lift2 CRel.junc (fun _ => {}) (fun _ => {}) R S
/-- `Λ(R)` total on the keys `D`: `[]` at a key `R` relates to nothing (`CRel.lamOn`, `rep_lamOn`). -/
def lam (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true A (.arr B) := Fn.ofDem (d := true) fun D =>
  CRel.lamOn (R.at (Dem.of d D)) D.val
/-- `f` on `R` read at the elements of `D`'s arrays, `ran(∋)` at `D`: the one form of `E` and the rows
    given a relation on elements (`F`, `filter`, `takewhile`). -/
def elems (A B C : Obj) (d : Bool) (R : Fn d A B) (f : {n : USize} → CRel A B → Vals (.arr A) n → CRel (.arr A) C) :
    Fn true (.arr A) C := Fn.ofDem (d := true) fun D =>
  let k := CRel.ran (CRel.mem D.val); also k.ok (f (R.at (Dem.of d k.rel)) D.val)
def E (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true (.arr A) (.arr B) := elems A B (.arr B) d R CRel.E

/-- An order held as its pair test, run on the pairs the operator compares. -/
def est (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) B := Fn.ofDem (d := true) fun D =>
  CRel.estOn (fun P => Q.at P.rel) (CRel.mem D.val)
def thin (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) (.arr B) := Fn.ofDem (d := true) fun D =>
  let T := CRel.thinOn (fun P => Q.at P.rel) (CRel.mem D.val)
  let df := CRel.diff (some D) (CRel.dom T)
  CRel.union (CRel.transpose T) (also df.ok (ofC (topC df.rel.key (nilVal _))))
def nil (A B : Obj) : Fn true A (.arr B) := ofVals _ _ fun X => ofC (topC X (nilVal _))
/-- A row of `prims` (`Tm.prim`) on the keys in demand, `f` its constant at the objects (`Expand.primE`): read on
    their values (`ofVals`) or composed after them (`after`); given a relation `R`, `R` run on the elements of the
    arrays in demand (`elems`), as its pair test (`testVals`, `testAfter`), or on the keys each round meets
    (`stepAfter`). -/
def after (A B : Obj) (f : {K : Obj} → CRel K A → CRel K B) : Fn true A B := ofVals A B fun X => f (some (idU X))
def testVals (B A C : Obj) (Q : Fn true (.prod B B) (.prod B B))
    (f : {n : USize} → (CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) → Vals A n → CRel A C) :
    Fn true A C := Fn.ofDem (d := true) fun D => f (fun P => Q.at P.rel) D.val
def testAfter (B A C : Obj) (Q : Fn true (.prod B B) (.prod B B))
    (f : {K : Obj} → (CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) → CRel K A → CRel K C) :
    Fn true A C := Fn.ofDem (d := true) fun D => f (fun P => Q.at P.rel) (some D)
def atPos (B : Obj) (k : Nat) : Fn true (.arr B) B := ofVals _ _ fun X => CRel.atPos k X

/-- A step run on a round's pairs `P`, where its value is read only composed after rows into `P`: with no key,
    nothing reads it, so it is not run — the last round of a fold or loop meets no pair. -/
def onKeys {A B : Obj} (F : Rel A B) (P : CRel A A) : CRel A B :=
  if P.rel.n == 0 then some Alg.zero else F.run ⟨some ⟨P.rel.n, P.rel.val⟩, none⟩

def stepAfter (S T A C : Obj) (d : Bool) (F : Fn d S T) (f : {K : Obj} → (CRel S S → CRel S T) → CRel K A → CRel K C) :
    Fn true A C := Fn.ofDem (d := true) fun D => f (onKeys F) (some D)
/-- `succ`, a value verb, `≤`, `<` on the universe `U`: its keys. A declared object's universe is `uni` of its
    literal (`uni_lits`), an object variable's the constant's argument. A result outside `U` has no row. -/
def succ (U : Fn false .long .long) : Fn true .long .long := ofVals _ _ fun X =>
  let u := U.at (); also u.ok (CRel.comp (some (idU X)) (CRel.succ u.rel.key))
def arith (k : UInt8) (U : Fn false .long .long) : Fn true (.prod .long .long) .long :=
  comp _ _ _ true (dom _ _ true (comp _ _ _ false (outl _ _) U))
    (comp _ _ _ true (dom _ _ true (comp _ _ _ false (outr _ _) U))
      (ofVals _ _ fun X => CRel.comp (some (Alg.arith k X)) (U.at ())))
/-- `X ≫ ≤ ≫ L` on `U`'s universe, `X` and `L` what the context knows of the two sides. -/
def leq (U : Fn false .long .long) : Fn false .long .long := .lazy fun K =>
  let u := U.at (); .tab (also u.ok (cut K (CRel.leq u.rel.key)))
def lt (U : Fn false .long .long) : Fn false .long .long := .lazy fun K =>
  let u := U.at (); .tab (also u.ok (cut K (CRel.lt u.rel.key)))
def foldr (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod E V) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => let v : CRel V V := e.run {}; also v.ok (CRel.foldOn false pairC v.rel.val (onKeys S) X)

/-- The left fold `⦇e, S⦈` over `[nil, snoc]`, `S` on `(acc, x)`: each array read from its start (`foldOnC true`),
    the round's pair the value before the element (`pairC p el`). -/
def fold (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod V E) V) : Fn true (.arr E) V :=
  ofVals _ _ fun X => let v : CRel V V := e.run {}; also v.ok (CRel.foldOn true (fun el p => pairC p el) v.rel.val (onKeys S) X)

/-- The pairs `(i, xs)` in demand, one fold row each, starting from its own key's seeds `(i,v)` from `e`: `v` the
    value side of `e i`'s pairs, as `fold` seeds from `e`'s values (`foldIDen`). -/
def foldI (I E V : Obj) (d d' : Bool) (e : Fn d I (.prod V V)) (S : Fn d' (.prod (.prod I V) E) (.prod I V)) :
    Fn true (.prod I (.arr E)) V := ofVals _ _ fun X =>
  let D := idU X; let ro := ofC (ranC (Alg.outl D)); let es := onKeys e ro
  let res := CRel.ran es
  let iv := CRel.pair (CRel.dom es) (CRel.comp es (CRel.mk (Alg.outr res.rel) res.ok))
  let r := CRel.num (some D) 0
  let ci := CRel.comp (CRel.mk (Alg.outl r.rel) r.ok) iv
  let G := ofC (foldRowsC true (Alg.outr r.rel) ci.rel
    (demandStepC (fun el p => pairC p el) fun A => let s := onKeys S (some A); (s.rel, s.ok)))
  let rg := CRel.ran G
  also (ro.ok && ci.ok) (CRel.comp (CRel.mk r.rel° r.ok) (CRel.comp G (CRel.mk (Alg.outr rg.rel) rg.ok)))

/-- `R` at the keys of the pairs, its rows `(i,(a,b))` re-keyed as `((i,a),b)`, a join with the pairs. -/
def flat (I A B : Obj) (d : Bool) (R : Fn d I (.prod A B)) : Fn true (.prod I A) B := ofVals _ _ fun X =>
  let D := idU X; let ro := ofC (ranC (Alg.outl D)); let r := onKeys R ro; let u := CRel.ran r
  let p := CRel.pair (CRel.mk r.rel° r.ok) (CRel.mk (Alg.outl u.rel) u.ok)
  also ro.ok (CRel.comp (some D) (CRel.comp (CRel.mk p.rel° p.ok) (CRel.mk (Alg.outr u.rel) u.ok)))

/-- `νX : S ∩ φ`: rounds of `S ∩ φ` from `S` down to the greatest fixed point. Each round is met with `S`, so
    the chain stays below `S` whatever `φ` is: a strict round drops a row of the distinct-row chain below `S`, and
    `S`'s row count plus two rounds reach the fixed point (`nu_sound`). -/
def nu (A B : Obj) (S : Fn false A B) (φ : CRel A B → Fn false A B) : Fn false A B :=
  let s : CRel A B := S.run {}; .tab (CRel.fixOn (s.rel.n.toNat + 2) (fun X => CRel.inter s ((φ X).run {})) s).1

/-- One arc `A\(X C)` of an AC-3 body: `A`, `C`, `𝟙(V)`, `𝟙(D)`. -/
abbrev Arc (V D : Obj) := Fn false V V × Fn false D D × Fn false V V × Fn false D D

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by AC-3's delta rounds (`acFixC`), its arcs `a :: as`. -/
def nuAC (V D : Obj) (S : Fn false V D) (a : Arc V D) (as : List (Arc V D)) : Fn false V D :=
  let s : CRel V D := S.run {}
  let rs := (a :: as).map fun (x, c, uv, ud) => (x.run {}, c.run {}, uv.run {}, ud.run {})
  let ok := rs.all fun (x, c, uv, ud) => CRel.ok x && CRel.ok c && CRel.ok uv && CRel.ok ud
  let rv := rs.map fun (x, c, uv, ud) => (⟨CRel.rel x, CRel.rel c, CRel.rel uv, CRel.rel ud⟩ : Revise V D)
  let r := acFixC s.rel rv (CRel.rel (a.2.2.1.run {}))
  .tab (CRel.mk r.1.1 (s.ok && ok && r.2))

/-- `μX : φ`: rounds of `φ` from `𝟘` up to the least fixed point, at most `cap`. Fewer than `cap` rounds run means a
    round left the row count, so the chain reached its fixed point; `cap` rounds run is not ok, never a truncated
    chain passed off as the answer. -/
def mu (A B : Obj) (cap : Nat) (φ : CRel A B → Fn false A B) : Fn false A B :=
  let r := CRel.fixOn cap (fun X => (φ X).run {}) (some Alg.zero); .tab (also (decide (r.2 < cap)) r.1)

/-- `F` read only at the nodes `P`: a table composed after `P`, a lazy one run on their keys; not run on none. -/
def onNodes {A B : Obj} (F : Rel A B) (P : CRel A A) : CRel A B := match F with
  | .tab f => if P.rel.n == 0 then CRel.mk Alg.zero P.ok else CRel.comp P f
  | .lazy _ => also P.ok (onKeys F P)

/-- `[R,S]` on the sum values in demand: `R` on the left values they hold, `S` on the right, joined with them. A
    demand row whose tag names a side with no values reads that side's `dflt` (`Vals.row`), a value the demand does
    not hold, so one scan of the tags clears the ok bit there (D7 = P). -/
def juncD (A B C : Obj) (d e : Bool) (R : Fn d A C) (S : Fn e B C) : Fn true (.sum A B) C :=
  ofVals _ _ fun {n} X =>
  let ⟨l, r, tag, _, x, y⟩ := X
  also ((List.finRange n.toNat).all fun i => if tag.get i then decide (0 < r.toNat) else decide (0 < l.toNat))
    (CRel.comp (some (idU X)) (CRel.junc (onNodes R (some (idU x))) (onNodes S (some (idU y)))))

/-- `hylo`'s rounds, at most `f`, from the nodes `pend` not yet valued and the values `X` so far: the nodes
    of `pend` with no child in `pend` (`chN`, each node's children) are ready, valued by `φ X` there and leave
    `pend`. The bit: `pend` emptied, under its own bit; none ready while some pend is a cycle of `chN`. -/
def hyloRounds {A B : Obj} (chN : CRel A A) (φ : CRel A B → CRel A A → CRel A B) :
    Nat → CRel A A → CRel A B → CRel A B × Bool
  | 0, _, X => (X, false)
  | f + 1, pend, X =>
    if pend.rel.n == 0 then (X, pend.ok) else
    let ready := CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))
    if ready.rel.n == 0 then (X, false) else
    hyloRounds chN φ f (CRel.diff pend ready) (CRel.union X (φ X ready))

/-- `hylo(c, S)` = `μX : c G(X) S` on the keys `D`, bottom-up: the nodes `N` the children `ch` reach from `D`
    (no universe read), then `hyloRounds` over them, each node valued once by `φ` after its children, so no
    intermediate structure of `G` is built. Not ok where the reach did not settle or `ch` has a cycle on `N`. -/
def hylo (A B : Obj) (d e : Bool) (ch : Fn d A A) (φ : CRel A B → Fn e A B) : Fn true A B := ofVals _ _ fun X =>
  let D := idU X
  let N := CRel.fixOn USize.size (fun N => CRel.union N (CRel.ran (onNodes ch N))) (some D)
  let r := hyloRounds (onNodes ch N.1) (fun Y P => onNodes (φ Y) P) (N.1.rel.n.toNat + 1) N.1 (some Alg.zero)
  also (decide (N.2 < USize.size) && r.2) (CRel.comp (some D) r.1)

/-! ### Plans: terms with the bit-rule nodes kept, every other sub-term its table (`Tm.val`) -/

/-- A term's code as its plan's leaf: closed where the term is, `d` deciding as it does for `Fn.at`. -/
def pleaf (A B : Obj) : (d : Bool) → Fn d A B → Pl A B
  | false, f => .closed (Thunk.mk fun _ => let r := f.at (); (.val r.rel, r.ok))
  | true, f => .on fun D => let r := f.at D; (.val r.rel, r.ok)

/-- A plan's tables run as bits (`Bits.runC`), its leaves' bit kept. -/
def runPl {A B : Obj} (p : Tm A B × Bool) : CRel A B := also p.2 (ofC (Bits.runC p.1))

/-- The plan `P` run to its relation: a constant's result or argument read where a table is wanted; closed, its
    table, else run on the coreflexive of the domain's known values. -/
def ofPl (A B : Obj) : Pl A B → Rel A B
  | .closed p => .tab (runPl p.get)
  | .on f => ofVals A B fun X => runPl (f (idU X))

/-- `R S` from `R`'s plan `r` on some keys: a closed `S` composed as it is, one on keys run on `ran(r)` (`demP`),
    so a closed `S` costs no `ranC`. -/
def compPl {A B C : Obj} (r : Tm A B × Bool) : Pl B C → Tm A C × Bool
  | .closed s => (.comp r.1 s.get.1, r.2 && s.get.2)
  | .on g => let k := demP r.1; let s := g k.1; (.comp r.1 s.1, r.2 && k.2 && s.2)

def pcomp (A B C : Obj) (R : Pl A B) (S : Pl B C) : Pl A C := match R with
  | .closed r => .closed (r.map (compPl · S))
  | .on f => .on fun D => compPl (f D) S
def pconv (A B : Obj) (R : Pl A B) : Pl B A := .closed (Thunk.mk fun _ => let r := R.get; (.conv r.1, r.2))
def pmeet (A B : Obj) (R S : Pl A B) : Pl A B := Pl.map2 (fun r s => (.meet r.1 s.1, r.2 && s.2)) R S
def pjoin (A B : Obj) (R S : Pl A B) : Pl A B := Pl.map2 (fun r s => (.join r.1 s.1, r.2 && s.2)) R S
def pdiff (A B : Obj) (R S : Pl A B) : Pl A B := Pl.map2 (fun r s => (.diff r.1 s.1, r.2 && s.2)) R S
def pldiv (A B C : Obj) (R : Pl A B) (S : Pl A C) (UB : Fn false B B) (UC : Fn false C C) : Pl B C :=
  .closed <| Thunk.mk fun _ => let r := R.get; let s := S.get; let ub := UB.at (); let uc := UC.at ()
    (.ldiv r.1 s.1 (.val ub.rel) (.val uc.rel), r.2 && s.2 && ub.ok && uc.ok)

/-- A closed `R S`, `R ∩ S`, `R − S`, `R\S` as bit matrices where its plan's objects are small (`Bits.runC`). -/
def compB (A B C : Obj) (R : Pl A B) (S : Pl B C) : Fn false A C := .tab (runPl (pcomp A B C R S).get)
def meetB (A B : Obj) (R S : Pl A B) : Fn false A B := .tab (runPl (pmeet A B R S).get)
def diffB (A B : Obj) (R S : Pl A B) : Fn false A B := .tab (runPl (pdiff A B R S).get)
def ldivB (A B C : Obj) (R : Pl A B) (S : Pl A C) (UB : Fn false B B) (UC : Fn false C C) :
    Fn false B C := .tab (runPl (pldiv A B C R S UB UC).get)

end Gen

end Rel.Lang
