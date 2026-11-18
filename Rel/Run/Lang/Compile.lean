import Rel.Run.Lang.Gen

/-! `compile` (`doc/rel-denotation-design.md` §3.2): a term's code as one structural function over `Tm`, one `Gen`
    combinator per constructor, with its environment `CodeEnv`, the code side of `Val`. A `μ`/`ν` body's variable is
    bound to the round's table, an earlier binding of a program to its constant. The rows of `prims` are code here
    (`RowCode`); their meanings and lemmas are `Rows`. -/

namespace Rel.Lang

open Rel Rel.Alg Gen

/-- The plan each variable `k` is bound to, at the objects and demand bit the term asks for. -/
abbrev CodeEnv := Nat → (A B : Obj) → (d : Bool) → Pl d A B

/-- `η` with the variable `k` bound to the table `X : A ⟶ B`, read at every demand. A use of `k` at other objects
    is ill-typed and reads `𝟘`, as `Val.bind` reads it, so the two stay one binder. -/
def CodeEnv.bind (η : CodeEnv) (k : Nat) {A B : Obj} (X : CRel A B) : CodeEnv := fun j A' B' d =>
  if j = k then (if h : A = A' ∧ B = B' then fun _ => (.val (h.1 ▸ h.2 ▸ X.rel), X.ok) else fun _ => (.zero, true))
  else η j A' B' d

/-! ### The rows of `prims` as code -/

/-- A relation argument's code with its objects and demand bit. -/
abbrev Code := (X Y : Obj) × (e : Bool) × Fn e X Y

/-- `c` at `X ⟶ Y`, where those are its objects. -/
def Code.at (c : Code) (X Y : Obj) : Option ((e : Bool) × Fn e X Y) :=
  if h : c.1 = X ∧ c.2.1 = Y then some ⟨c.2.2.1, h.2 ▸ h.1 ▸ c.2.2.2⟩ else none

/-- The object variables `σ` that make the pattern `o` the object `A`, extending `σ`: none where they cannot. -/
def OExp.unify : OExp → Obj → List (String × Obj) → Option (List (String × Obj))
  | .var _ n, A, σ => match σ.lookup n with
    | some B => if A = B then some σ else none
    | none => some ((n, A) :: σ)
  | .prod a b, .prod A B, σ | .sum a b, .sum A B, σ => a.unify A σ >>= b.unify B
  | .list a, .arr A, σ => a.unify A σ
  | _, _, _ => none

/-- The row `r`'s object variables (`Prim.vars` order) at `A ⟶ B`, read off its constant's type. -/
def Prim.objs (r : Prim) (A B : Obj) : Option (List Obj) := do
  let σ ← r.sig.2.2.1.unify A [] >>= r.sig.2.2.2.unify B
  r.vars.mapM fun v => List.lookup v σ

/-- A row of `prims` as code: its objects at its object variables `σ`, and its code there given its relation
    arguments' codes; none where they do not fit. What `Expand.primE` finds by unification. -/
structure RowCode where
  sym : String
  ty : List Obj → Obj × Obj
  run : (σ : List Obj) → List Code → Option (Fn true (ty σ).1 (ty σ).2)

/-- A row with no relation argument. -/
def RowCode.plain (sym : String) (ty : List Obj → Obj × Obj) (f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2) :
    RowCode := ⟨sym, ty, fun σ cs => if cs.isEmpty then some (f σ) else none⟩

/-- A row with one relation argument at `X ⟶ Y` (`par σ`), its demand bit `e` free. -/
def RowCode.unary (sym : String) (ty : List Obj → Obj × Obj) (par : List Obj → Obj × Obj)
    (f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2) : RowCode :=
  ⟨sym, ty, fun σ cs => match cs with
    | [c] => (c.at (par σ).1 (par σ).2).map fun x => f σ x.1 x.2
    | _ => none⟩

/-- A row whose relation argument is a pair test `Q : B×B ⟶ B×B` run on demand. -/
def RowCode.test (sym : String) (ty : List Obj → Obj × Obj)
    (f : (σ : List Obj) → Fn true (.prod (σ.headD .long) (σ.headD .long)) (.prod (σ.headD .long) (σ.headD .long)) →
      Fn true (ty σ).1 (ty σ).2) : RowCode :=
  RowCode.unary sym ty (fun σ => (.prod (σ.headD .long) (σ.headD .long), .prod (σ.headD .long) (σ.headD .long)))
    fun σ e q => match e, q with
      | true, q => f σ q
      | false, _ => fun _ => ⟨Alg.zero, false⟩

/-- The first and second object variables. -/
abbrev σ₁ (σ : List Obj) : Obj := σ.headD .long
abbrev σ₂ (σ : List Obj) : Obj := σ.getD 1 .long

/-! The rows, each named so its meaning and lemma (`Rows`) name the code they are about. -/
namespace RowCode
def tau := plain "τ" (fun σ => (σ₁ σ, .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.τ X
def cons := plain "cons" (fun σ => (.prod (σ₁ σ) (.arr (σ₁ σ)), .arr (σ₁ σ))) fun _ => after _ _ fun P => CRel.cons P
def mem := plain "∋" (fun σ => (.arr (σ₁ σ), σ₁ σ)) fun _ => ofVals _ _ fun X => CRel.mem X
def inl := plain "inl" (fun σ => (σ₁ σ, .sum (σ₁ σ) (σ₂ σ))) fun _ => ofVals _ _ fun X => CRel.inl X
def inr := plain "inr" (fun σ => (σ₁ σ, .sum (σ₂ σ) (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.inr X
def map := unary "F" (fun σ => (.arr (σ₁ σ), .arr (σ₂ σ))) (fun σ => (σ₁ σ, σ₂ σ))
  fun σ e R => elems (σ₁ σ) (σ₂ σ) _ e R CRel.map
def filter := unary "filter" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) (fun σ => (σ₁ σ, σ₁ σ))
  fun σ e R => elems (σ₁ σ) (σ₁ σ) _ e R CRel.filter
def takewhile := unary "takewhile" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) (fun σ => (σ₁ σ, σ₁ σ))
  fun σ e R => elems (σ₁ σ) (σ₁ σ) _ e R CRel.takewhile
def thinL := test "thinL" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ)))
  fun σ Q => testVals (σ₁ σ) _ _ Q fun q X => CRel.thinLOn q X
def merge := test "merge" (fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₁ σ)), .arr (σ₁ σ)))
  fun σ Q => testAfter (σ₁ σ) _ _ Q fun q P => CRel.mergeOn q P
def loop := unary "loop" (fun σ => (.prod (σ₁ σ) (.arr (σ₂ σ)), σ₁ σ)) (fun σ => (.prod (σ₁ σ) (σ₂ σ), σ₁ σ))
  fun σ e F => stepAfter (.prod (σ₁ σ) (σ₂ σ)) (σ₁ σ) _ _ e F fun G P => CRel.loopOn G P
def uncons := plain "uncons" (fun σ => (.arr (σ₁ σ), .prod (σ₁ σ) (.arr (σ₁ σ)))) fun _ => ofVals _ _ fun X => CRel.uncons X
def length := plain "length" (fun σ => (.arr (σ₁ σ), .long)) fun _ => ofVals _ _ fun X => CRel.length X
def sum := plain "sum" (fun _ => (.arr .long, .long)) fun _ => ofVals _ _ fun X => CRel.Arr.sum X
def inits := plain "inits" (fun σ => (.arr (σ₁ σ), .arr (.arr (σ₁ σ)))) fun _ => ofVals _ _ fun X => CRel.inits X
def tails := plain "tails" (fun σ => (.arr (σ₁ σ), .arr (.arr (σ₁ σ)))) fun _ => ofVals _ _ fun X => CRel.tails X
def «prefix» := plain "prefix" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.«prefix» X
def suffix := plain "suffix" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.suffix X
def concat := plain "concat" (fun σ => (.arr (.arr (σ₁ σ)), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.concat X
def cat := plain "cat" (fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₁ σ)), .arr (σ₁ σ))) fun _ => after _ _ fun P => CRel.cat P
def uncat := plain "uncat" (fun σ => (.arr (σ₁ σ), .prod (.arr (σ₁ σ)) (.arr (σ₁ σ))))
  fun _ => ofVals _ _ fun X => CRel.uncat X
def zip := plain "zip" (fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₂ σ)), .arr (.prod (σ₁ σ) (σ₂ σ))))
  fun _ => after _ _ fun P => CRel.zip P
def snoc := plain "snoc" (fun σ => (.prod (.arr (σ₁ σ)) (σ₁ σ), .arr (σ₁ σ))) fun _ => after _ _ fun P => CRel.snoc P
def unsnoc := plain "unsnoc" (fun σ => (.arr (σ₁ σ), .prod (.arr (σ₁ σ)) (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.unsnoc X
def setify := plain "setify" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.setify X
def distinct := plain "distinct" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.distinct X
def asc := plain "asc" (fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))) fun _ => ofVals _ _ fun X => CRel.asc X
def tic := plain "tic" (fun σ => (.prod (σ₁ σ) (.arr (σ₁ σ)), .arr (.arr (σ₁ σ)))) fun _ => after _ _ fun P => CRel.tic P
end RowCode

/-- Every row of `prims`, as code. -/
def rowCodes : List RowCode :=
  open RowCode in
  [tau, cons, mem, inl, inr, map, filter, takewhile, thinL, merge, loop, uncons, length, sum, inits, tails, «prefix»,
   suffix, concat, cat, uncat, zip, snoc, unsnoc, setify, distinct, asc, tic]

/-- `o` with each object variable the object `σ` gives it (`.long` where none). -/
def OExp.inst (σ : List (String × Obj)) : OExp → Obj
  | .var _ n => (σ.lookup n).getD .long
  | .name .. => .long
  | .prod a b => .prod (a.inst σ) (b.inst σ)
  | .sum a b => .sum (a.inst σ) (b.inst σ)
  | .list a => .arr (a.inst σ)
/-- A code that vouches for nothing: its ok bit is false. -/
def none' (A B : Obj) (d : Bool) : Fn d A B := fun _ => ⟨Alg.zero, false⟩

/-- The row `r` at `A ⟶ B` given its relation arguments' codes `cs`, where its code fits them. -/
def Prim.run (r : Prim) (A B : Obj) (cs : List Code) : Option (Fn true A B) := do
  let c ← rowCodes.find? (·.sym == r.sym)
  let σ ← r.objs A B
  let f ← c.run σ cs
  if h : (c.ty σ).1 = A ∧ (c.ty σ).2 = B then some (h.2 ▸ h.1 ▸ f) else none

/-- The row `r`'s code at demand bit `d`; not ok where it has none (`d = false` never holds of a row). -/
def Prim.fn (r : Prim) (A B : Obj) : (d : Bool) → List Code → Fn d A B
  | true, cs => (r.run A B cs).getD (none' A B true)
  | false, _ => none' A B false

-- every row of `prims` has a code, and it runs at its constant's type, each object variable `.long`, given one
-- argument of each parameter's type, a pair test's at `B×B` (`prims` and `rowCodes` cannot drift apart unseen)
#guard prims.all fun r =>
  let o (x : OExp) := x.inst []
  let arg : (OExp × OExp) × Option Bool → Code
    | ((x, y), some true) => ⟨.prod (o x) (o x), .prod (o y) (o y), true, none' _ _ true⟩
    | ((x, y), _) => ⟨o x, o y, true, none' _ _ true⟩
  (r.run (o r.sig.2.2.1) (o r.sig.2.2.2) (r.sig.2.1.map arg)).isSome

/-! ### `compile` -/

/-- A term's code, its bit-matrix plan, and, at a row's spine of `arg`s, the row and its arguments' codes. -/
structure Out (d : Bool) (A B : Obj) where
  fn : Fn d A B
  pl : Pl d A B
  row : Option (Prim × List Code) := none

/-- A closed node's table and plan computed once, where the `Gen` combinators would recompute it at every call
    (each round of a fold over it): the sharing `rel_program` gets from Lean hoisting closed terms. -/
def Out.memo {A B : Obj} : {d : Bool} → Out d A B → Out d A B
  | false, o => let r := o.fn (); let p := o.pl (); ⟨fun _ => r, fun _ => p, o.row⟩
  | true, o => o

/-- `t`'s code and plan, one `Gen` combinator per constructor, as `Expand.node` and `Expand.plan?` build them. The
    plan is the bit-rule node where the node has one, else its table as a leaf (`Gen.pleaf`); a closed term's plan
    is its table. `ν` runs as plain rounds (`Gen.nu`); `call` vouches for nothing until stage 5. -/
def Tm.gen (η : CodeEnv) {A B : Obj} {d : Bool} (t : Tm A B d) : Out d A B := Out.memo <| match η, A, B, d, t with
  | _, A, B, _, .val R => leaf (Gen.val A B (R, true))
  | _, A, _, _, .uni (m := m) U => leaf (Gen.uni A m (U, true))
  | _, A, B, _, .zero => leaf (Gen.zero A B)
  | _, A, _, _, .id => leaf (Gen.id A)
  | η, A, B, _, .top V => leaf (Gen.top A B (V.gen η).fn)
  | _, _, _, _, .outl (A := A) (B := B) => leaf (Gen.outl A B)
  | _, _, _, _, .outr (A := A) (B := B) => leaf (Gen.outr A B)
  | η, A, C, true, .comp (B := B) (e := e) R S =>
    ⟨Gen.comp A B C e (R.gen η).fn (S.gen η).fn, Gen.pcomp A B C true e (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, C, false, .comp (B := B) (e := e) R S =>
    ⟨Gen.compB A B C e (R.gen η).pl (S.gen η).pl, Gen.pcomp A B C false e (R.gen η).pl (S.gen η).pl, none⟩
  | η, _, _, _, .conv (A := A) (B := B) R => ⟨Gen.conv A B (R.gen η).fn, Gen.pconv A B (R.gen η).pl, none⟩
  | η, A, B, _, .meet (d := false) (e := false) R S =>
    ⟨Gen.meetB A B (R.gen η).pl (S.gen η).pl, Gen.pmeet A B false false (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, B, _, .meet (d := d) (e := e) R S =>
    ⟨Gen.meet A B d e (R.gen η).fn (S.gen η).fn, Gen.pmeet A B d e (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, B, _, .join (d := d) (e := e) R S =>
    ⟨Gen.join A B d e (R.gen η).fn (S.gen η).fn, Gen.pjoin A B d e (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, B, _, .diff (d := false) (e := false) R S =>
    ⟨Gen.diffB A B (R.gen η).pl (S.gen η).pl, Gen.pdiff A B false false (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, B, _, .diff (d := d) (e := e) R S =>
    ⟨Gen.diff A B d e (R.gen η).fn (S.gen η).fn, Gen.pdiff A B d e (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, _, d, .dom (B := B) R => leaf (Gen.dom A B d (R.gen η).fn)
  | η, _, _, _, .ran (A := A) (B := B) R => leaf (Gen.ran A B (R.gen η).fn)
  | η, B, C, _, .ldiv (A := A) R S UB UC =>
    ⟨Gen.ldivB A B C (R.gen η).pl (S.gen η).pl (UB.gen η).fn (UC.gen η).fn,
     Gen.pldiv A B C (R.gen η).pl (S.gen η).pl (UB.gen η).fn (UC.gen η).fn, none⟩
  | η, A, B, _, .rdiv (C := C) R S UA UB =>
    leaf (Gen.rdiv A B C (R.gen η).fn (S.gen η).fn (UA.gen η).fn (UB.gen η).fn)
  | η, A, _, _, .pair (B := B) (C := C) (d := d) (e := e) R S => leaf (Gen.pair A B C d e (R.gen η).fn (S.gen η).fn)
  | η, _, _, _, .prod (A := A) (B := B) (C := C) (D := D) R S => leaf (Gen.prod A B C D (R.gen η).fn (S.gen η).fn)
  | η, _, C, _, .junc (A := A) (B := B) R S => leaf (Gen.junc A B C (R.gen η).fn (S.gen η).fn)
  | η, _, C, _, .juncD (A := A) (B := B) (d := d) (e := e) R S => leaf (Gen.juncD A B C d e (R.gen η).fn (S.gen η).fn)
  | η, A, _, _, .lam (B := B) (d := d) R => leaf (Gen.lam A B d (R.gen η).fn)
  | η, _, _, _, .E (A := A) (B := B) (d := d) R => leaf (Gen.E A B d (R.gen η).fn)
  | η, _, B, _, .est Q => leaf (Gen.est B (Q.gen η).fn)
  | η, _, _, _, .thin (B := B) Q => leaf (Gen.thin B (Q.gen η).fn)
  | _, A, _, _, .nil (B := B) => leaf (Gen.nil A B)
  | _, _, _, _, .prim r => ⟨r.fn _ _ true [], pleaf _ _ true (r.fn _ _ true []), some (r, [])⟩
  | _, _, B, _, .atPos k => leaf (Gen.atPos B k)
  | η, _, _, _, .own R => R.gen η
  | η, _, _, _, .succ U => leaf (Gen.succ (U.gen η).fn)
  | η, _, _, _, .arith k U => leaf (Gen.arith k (U.gen η).fn)
  | η, _, _, _, .leq U => leaf (Gen.leq (U.gen η).fn)
  | η, _, _, _, .lt U => leaf (Gen.lt (U.gen η).fn)
  | η, _, V, _, .foldr (E := X) (d := d) e S => leaf (Gen.foldr X V d (e.gen η).fn (S.gen η).fn)
  | η, _, V, _, .fold (E := X) (d := d) e S => leaf (Gen.fold X V d (e.gen η).fn (S.gen η).fn)
  | η, _, _, _, .share _ R => R.gen η
  | η, _, V, _, .foldI (I := I) (E := X) (d := d) (d' := d') e S =>
    leaf (Gen.foldI I X V d d' (e.gen η).fn (S.gen η).fn)
  | η, _, B, _, .flat (I := I) (A := A) (d := d) R => leaf (Gen.flat I A B d (R.gen η).fn)
  | η, A, B, d, .var k => ⟨Gen.ofPl A B d (η k A B d), η k A B d, none⟩
  | _, A, B, d, .call .. => leaf (none' A B d)
  | η, A, B, d, .arg f x => match (f.gen η).row with
    | some (r, cs) => let cs := cs ++ [⟨_, _, _, (x.gen η).fn⟩]
      ⟨r.fn A B d cs, pleaf A B d (r.fn A B d cs), some (r, cs)⟩
    | none => leaf (none' A B d)
  | η, A, B, _, .nu k S b => leaf (Gen.nu A B (S.gen η).fn fun X => (b.gen (η.bind k X)).fn)
  | η, A, B, _, .mu k _ cap b => leaf (Gen.mu A B cap fun X => (b.gen (η.bind k X)).fn)
  | η, A, B, _, .hylo (d := d) (e := e) k _ ch b =>
    leaf (Gen.hylo A B d e (ch.gen η).fn fun X => (b.gen (η.bind k X)).fn)
where
  /-- A node with no bit rule: its plan is its table. -/
  leaf {A B : Obj} {d : Bool} (f : Fn d A B) : Out d A B := ⟨f, pleaf A B d f, none⟩

/-- `t`'s code. -/
def compile (η : CodeEnv) {A B : Obj} {d : Bool} (t : Tm A B d) : Fn d A B := (t.gen η).fn

/-- `t`'s bit-matrix plan where its node has a bit rule, else its table as a leaf (`Gen.pleaf`). -/
def Tm.plan (η : CodeEnv) {A B : Obj} {d : Bool} (t : Tm A B d) : Pl d A B := (t.gen η).pl

end Rel.Lang
