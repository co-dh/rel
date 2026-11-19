import Rel.Run.Lang.Gen

/-! `compile` (`doc/rel-denotation-design.md` §3.2): a term's code as one structural function over `Tm`, one `Gen`
    combinator per constructor, with its environment `CodeEnv`, the code side of `Val`. A `μ`/`ν` body's variable is
    bound to the round's table, an earlier binding of a program to its constant. The rows of `prims` are code here
    (`RowCode`); their meanings and lemmas are `Rows`. -/

namespace Rel.Lang

open Tab Rel.Alg Gen

/-- The plan each variable `k` is bound to, at the objects the term asks for. -/
abbrev CodeEnv := Nat → (A B : Obj) → Pl A B

/-! ### The rows of `prims` as code -/

/-- A relation argument's code with its objects and demand bit. -/
abbrev Code := (X Y : Obj) × (e : Bool) × Fn e X Y

/-- `c` at `X ⟶ Y`, where those are its objects. -/
def Code.at (c : Code) (X Y : Obj) : Option ((e : Bool) × Fn e X Y) :=
  if h : c.1 = X ∧ c.2.1 = Y then some ⟨c.2.2.1, h.2 ▸ h.1 ▸ c.2.2.2⟩ else none

/-- `η` with the variable `k` bound to the code `c`: at `c`'s objects, `c`'s plan leaf (`pleaf`: closed where `c`
    is, else on the keys it is given, so read closed it has none and is not ok, `Pl.get`); at other objects `𝟘`, as
    `Val.bind` reads it. A `μ`/`ν` round's table `X` is bound as the closed code `⟨A, B, false, .tab X⟩`. -/
def CodeEnv.bindCode (η : CodeEnv) (k : Nat) (c : Code) : CodeEnv := fun j A B =>
  if j = k then (match c.at A B with | some ⟨e, f⟩ => pleaf A B e f | none => .closed (.pure (.zero, true)))
  else η j A B

/-- The codes `cs` bound to the variables `0, 1, …` in order, every other variable `𝟘`: what a call's body is
    compiled under, the code side of `Val.args`. -/
def CodeEnv.args (cs : List Code) : CodeEnv := go 0 cs where
  /-- `cs` bound from the variable `k` on. -/
  go (k : Nat) : List Code → CodeEnv
    | [] => fun _ _ _ => .closed (.pure (.zero, true))
    | c :: cs => (go (k + 1) cs).bindCode k c

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
      | false, _ => .tab (CRel.toE Option.none)

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
def none' (A B : Obj) (d : Bool) : Fn d A B := .tab (CRel.toE Option.none)

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
  pl : Pl A B
  row : Option (Prim × List Code) := none

/-- `t`'s code and plan, one `Gen` combinator per constructor, as `Expand.node` and `Expand.plan?` build them. The
    plan is the bit-rule node where the node has one, else its table as a leaf (`Gen.pleaf`); a closed term's plan
    is its table. `ν` runs as plain rounds (`Gen.nu`); `call` vouches for nothing until stage 5. A closed field
    (`conv`, `ldiv`) holding a term run on demand reads its `on` plan by `Pl.get`, which vouches for nothing. A
    `hylo` runs its body's `kids`, not a part of it: the recursion is on `Tm.size` (`Tm.size_kids`). -/
def Tm.gen (η : CodeEnv) {A B : Obj} (t : Tm A B) : Out t.dem A B := match η, A, B, t with
  | _, A, B, .val R => leaf (Gen.val A B (R, true))
  | _, A, _, .uni (m := m) U => leaf (Gen.uni A m (U, true))
  | _, A, B, .zero => leaf (Gen.zero A B)
  | _, A, _, .id => leaf (Gen.id A)
  | η, A, B, .top V => leaf (Gen.top A B (V.gen η).fn)
  | _, _, _, .outl (A := A) (B := B) => leaf (Gen.outl A B)
  | _, _, _, .outr (A := A) (B := B) => leaf (Gen.outr A B)
  | η, A, C, .comp (B := B) R S =>
    show Out R.dem A C from match R.dem, R.gen η with
    | true, r => ⟨Gen.comp A B C S.dem r.fn (S.gen η).fn, Gen.pcomp A B C r.pl (S.gen η).pl, none⟩
    | false, r => ⟨Gen.compB A B C r.pl (S.gen η).pl, Gen.pcomp A B C r.pl (S.gen η).pl, none⟩
  | η, _, _, .conv (A := A) (B := B) R => ⟨Gen.conv A B (R.gen η).fn, Gen.pconv A B (R.gen η).pl, none⟩
  | η, A, B, .meet R S =>
    show Out (R.dem || S.dem) A B from match R.dem, S.dem, R.gen η, S.gen η with
    | false, false, r, s => ⟨Gen.meetB A B r.pl s.pl, Gen.pmeet A B r.pl s.pl, none⟩
    | d, e, r, s => ⟨Gen.meet A B d e r.fn s.fn, Gen.pmeet A B r.pl s.pl, none⟩
  | η, A, B, .join R S =>
    ⟨Gen.join A B R.dem S.dem (R.gen η).fn (S.gen η).fn, Gen.pjoin A B (R.gen η).pl (S.gen η).pl, none⟩
  | η, A, B, .diff R S =>
    show Out (R.dem || S.dem) A B from match R.dem, S.dem, R.gen η, S.gen η with
    | false, false, r, s => ⟨Gen.diffB A B r.pl s.pl, Gen.pdiff A B r.pl s.pl, none⟩
    | d, e, r, s => ⟨Gen.diff A B d e r.fn s.fn, Gen.pdiff A B r.pl s.pl, none⟩
  | η, A, _, .dom (B := B) R => leaf (Gen.dom A B R.dem (R.gen η).fn)
  | η, _, _, .ran (A := A) (B := B) R => leaf (Gen.ran A B (R.gen η).fn)
  | η, B, C, .ldiv (A := A) R S UB UC =>
    ⟨Gen.ldivB A B C (R.gen η).pl (S.gen η).pl (UB.gen η).fn (UC.gen η).fn,
     Gen.pldiv A B C (R.gen η).pl (S.gen η).pl (UB.gen η).fn (UC.gen η).fn, none⟩
  | η, A, B, .rdiv (C := C) R S UA UB =>
    leaf (Gen.rdiv A B C (R.gen η).fn (S.gen η).fn (UA.gen η).fn (UB.gen η).fn)
  | η, A, _, .pair (B := B) (C := C) R S => leaf (Gen.pair A B C R.dem S.dem (R.gen η).fn (S.gen η).fn)
  | η, _, _, .prod (A := A) (B := B) (C := C) (D := D) R S => leaf (Gen.prod A B C D (R.gen η).fn (S.gen η).fn)
  | η, _, C, .junc (A := A) (B := B) R S => leaf (Gen.junc A B C (R.gen η).fn (S.gen η).fn)
  | η, _, C, .juncD (A := A) (B := B) R S => leaf (Gen.juncD A B C R.dem S.dem (R.gen η).fn (S.gen η).fn)
  | η, A, _, .lam (B := B) R => leaf (Gen.lam A B R.dem (R.gen η).fn)
  | η, _, _, .E (A := A) (B := B) R => leaf (Gen.E A B R.dem (R.gen η).fn)
  | η, _, B, .est Q => leaf (Gen.est B (Q.gen η).fn)
  | η, _, _, .thin (B := B) Q => leaf (Gen.thin B (Q.gen η).fn)
  | _, A, _, .nil (B := B) => leaf (Gen.nil A B)
  | _, _, _, .prim r => ⟨r.fn _ _ true [], pleaf _ _ true (r.fn _ _ true []), some (r, [])⟩
  | _, _, B, .atPos k => leaf (Gen.atPos B k)
  | η, _, _, .own R => R.gen η
  | η, _, _, .succ U => leaf (Gen.succ (U.gen η).fn)
  | η, _, _, .arith k U => leaf (Gen.arith k (U.gen η).fn)
  | η, _, _, .leq U => leaf (Gen.leq (U.gen η).fn)
  | η, _, _, .lt U => leaf (Gen.lt (U.gen η).fn)
  | η, _, V, .foldr (E := X) e S => leaf (Gen.foldr X V S.dem (e.gen η).fn (S.gen η).fn)
  | η, _, V, .fold (E := X) e S => leaf (Gen.fold X V S.dem (e.gen η).fn (S.gen η).fn)
  | η, _, _, .share _ R => R.gen η
  | η, _, V, .foldI (I := I) (E := X) e S =>
    leaf (Gen.foldI I X V e.dem S.dem (e.gen η).fn (S.gen η).fn)
  | η, _, B, .flat (I := I) (A := A) R => leaf (Gen.flat I A B R.dem (R.gen η).fn)
  | η, A, B, .var _ k => ⟨Gen.ofPl A B (η k A B), η k A B, none⟩
  | _, A, B, .call d .. => leaf (none' A B d)
  | η, A, B, .arg f x => match (f.gen η).row with
    | some (r, cs) => let cs := cs ++ [⟨_, _, _, (x.gen η).fn⟩]
      ⟨r.fn A B f.dem cs, pleaf A B f.dem (r.fn A B f.dem cs), some (r, cs)⟩
    | none => leaf (none' A B f.dem)
  | η, A, B, .nu k S b => leaf (Gen.nu A B (S.gen η).fn fun X => (b.gen (η.bindCode k ⟨A, B, false, .tab X⟩)).fn)
  | η, A, B, .mu k _ cap b => leaf (Gen.mu A B cap fun X => (b.gen (η.bindCode k ⟨A, B, false, .tab X⟩)).fn)
  | η, A, B, .hylo k _ b =>
    have := Tm.size_kids k A b
    leaf (Gen.hylo A B _ b.dem (((b.kids k A).getD .zero).gen η).fn
      fun X => (b.gen (η.bindCode k ⟨A, B, false, .tab X⟩)).fn)
termination_by t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
where
  /-- A node with no bit rule: its plan is its table. -/
  leaf {A B : Obj} {d : Bool} (f : Fn d A B) : Out d A B := ⟨f, pleaf A B d f, none⟩

/-- `t`'s code. -/
def compile (η : CodeEnv) {A B : Obj} (t : Tm A B) : Fn t.dem A B := (t.gen η).fn

/-- `t`'s bit-matrix plan where its node has a bit rule, else its table as a leaf (`Gen.pleaf`). -/
def Tm.plan (η : CodeEnv) {A B : Obj} (t : Tm A B) : Pl A B := (t.gen η).pl

end Rel.Lang
