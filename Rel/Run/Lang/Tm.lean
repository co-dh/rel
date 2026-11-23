module

public import Rel.Run.Struct
public import Rel.Run.Lang.Syntax

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The core term `Tm` of the Rel language, indexed by its source and target, and `Tm.dem`, whether it runs on
    demand; the elaborator (`Elab`) builds it and `Expand` reads it (`doc/rel-lang-design.md` §a, §e). -/

namespace Rel.Lang

open Tab

/-! ### The core term -/

/-- A core term `A ⟶ B` over `Alg`. Whether it runs on DEMAND (§a), its value read only at the keys the
    coreflexive its left context supplies, is `Tm.dem`; a term with `dem = false` needs no keys: a closed term.
    A field documented closed is not checked by the type: the elaborator puts only closed terms there (`closed?`). -/
inductive Tm : Obj → Obj → Type where
  | val {A B : Obj} (R : Tab A B) : Tm A B
  | uni {A : Obj} {m : USize} (U : Vals A m) : Tm A A
  | zero {A B : Obj} : Tm A B
  | id {A : Obj} : Tm A A
  /-- `⊤` onto the values of the closed coreflexive `V`. -/
  | top {A B : Obj} (V : Tm B B) : Tm A B
  | outl {A B : Obj} : Tm (.prod A B) A
  | outr {A B : Obj} : Tm (.prod A B) B
  | comp {A B C : Obj} (R : Tm A B) (S : Tm B C) : Tm A C
  | conv {A B : Obj} (R : Tm A B) : Tm B A
  | meet {A B : Obj} (R : Tm A B) (S : Tm A B) : Tm A B
  | join {A B : Obj} (R : Tm A B) (S : Tm A B) : Tm A B
  | diff {A B : Obj} (R : Tm A B) (S : Tm A B) : Tm A B
  | ldiv {A B C : Obj} (R : Tm A B) (S : Tm A C) (UB : Tm B B) (UC : Tm C C) : Tm B C
  | rdiv {A B C : Obj} (R : Tm A C) (S : Tm B C) (UA : Tm A A) (UB : Tm B B) : Tm A B
  | pair {A B C : Obj} (R : Tm A B) (S : Tm A C) : Tm A (.prod B C)
  /-- `Λ(R)`, a map: total on the keys in demand, `[]` where `R` has no image, so it always runs on demand and a
      closed use reads its source's universe (`closeRes`). -/
  | lam {A B : Obj} (R : Tm A B) : Tm A (.arr B)
  /-- `∋`, an array to each of its elements, on the arrays in demand. -/
  | mem {B : Obj} : Tm (.arr B) B
  /-- The injections into a sum; their converses `inl°`, `inr°` are `conv inl`, `conv inr`, run on the sum values in
      demand (`Tm.dem`, `Tab.inlConv`). -/
  | inl {A B : Obj} : Tm A (.sum A B)
  | inr {A B : Obj} : Tm B (.sum A B)
  /-- The row `r` of `prims` at `A ⟶ B`, an instance of its constant's type; its relations given by `arg`. -/
  | prim {A B : Obj} (r : Prim) : Tm A B
  /-- `⦇e,S⦈ʳ`, the right fold, on the arrays in demand: each read from its end, `S` on `(x, acc)`. -/
  | foldr {E V : Obj} (e : Tm V V) (S : Tm (.prod E V) V) : Tm (.arr E) V
  /-- `⦇e,S⦈`, the left fold, on the arrays in demand: each read from index 0, `S` on `(acc, x)`. -/
  | fold {E V : Obj} (e : Tm V V) (S : Tm (.prod V E) V) : Tm (.arr E) V
  /-- `R`, closed, numbered `k` among the program's closed parts (`Tm.number`): its code is built once
      (`Code.shares`). -/
  | share {A B : Obj} (k : Nat) (R : Tm A B) : Tm A B
  /-- The variable `k` of the fixed point that binds it: its value in the round being run; or a constant's
      parameter, on the keys in demand when its argument is a pair test (`Form`). `d`: its demand bit, which the
      use site fixes, as `call` stores its own. -/
  | var {A B : Obj} (d : Bool) (k : Nat) : Tm A B
  /-- `let ks := args in b`: the definition elaborated once to the constant `c`, called before its arguments
      (`arg`). `b` its body at the call's objects (`Tm.instObj`), `ks` the variables of `b` its arguments bind, in
      the order `arg` gives them; `c` at `os`, the objects of the variables it is generic over, its shared code.
      `cv`: the constant of the converse `c°` (`convTm`), `none` where no converse runs on demand. `c°` is `c` itself
      where it is a theorem (`perm° = perm`, which the fold `perm` is cannot derive), else `c'` the converse the body
      `b` derives. -/
  | call {A B : Obj} (ks : List Nat) (c : Lean.Name) (cv : Option Lean.Name) (os : List Obj) (b : Tm A B) : Tm A B
  /-- `f` given one more argument `x`: a relation, a pair test, or the universe of one of its object variables. -/
  | arg {A B C D : Obj} (f : Tm A B) (x : Tm C D) : Tm A B
  /-- `νX : φ`, `X` the variable `k`: rounds of `body` from `S`, the conjuncts of `φ` without `X`, down to the
      greatest fixed point. -/
  | nu {A B : Obj} (k : Nat) (S body : Tm A B) : Tm A B
  /-- `μX : φ`: rounds of `body` from `𝟘` up to the least fixed point, at most `cap`; `what` names the `μ` in the
      failure a run that reaches `cap` first reports. -/
  | mu {A B : Obj} (k : Nat) (what : String) (cap : Nat) (body : Tm A B) : Tm A B
  /-- `hylo(c, S)` = `μX : c G(X) S`, `X` the variable `k`, on the keys in demand: bottom-up over the nodes the
      children `body.kids k` (`c` then `G`'s membership) reach from them, each node's value `body` run once its
      children have theirs; `what` names the coalgebra `c`, where the failure a cycle of the children reports is. -/
  | hylo {A B : Obj} (k : Nat) (what : String) (body : Tm A B) : Tm A B

/-- A built term with its objects. -/
abbrev Res := (A : Obj) × (B : Obj) × Tm A B

/-- The object variables `σ` that make the pattern `o` the object `A`, extending `σ`: none where they cannot. -/
def OExp.unify : OExp → Obj → List (String × Obj) → Option (List (String × Obj))
  | .var _ n, A, σ => match σ.lookup n with
    | some B => if A = B then some σ else none
    | none => some ((n, A) :: σ)
  | .prod a b, .prod A B, σ | .sum a b, .sum A B, σ => a.unify A σ >>= b.unify B
  | .list a, .arr A, σ => a.unify A σ
  | _, _, _ => none

/-- The row `r`'s object variables (`Prim.vars` order) at `A ⟶ B` given arguments at the objects `ps`: read off its
    constant's type, and a variable only a parameter names (`dom(R : A ⟶ B) : A ⟶ A`'s `B`) off that argument's
    objects, a pair-test parameter (`some true`, §a) at `X×Y ⟶ X×Y` as `rowObjs` gives it. -/
def Prim.objs (r : Prim) (A B : Obj) (ps : List (Obj × Obj)) : Option (List Obj) := do
  let σ ← r.sig.2.1.unify A [] >>= r.sig.2.2.unify B
  r.vars.mapM fun v => (σ.lookup v).orElse fun _ => ((r.sig.1.zip ps).foldlM (fun τ (((x, y), fm), X, Y) =>
    let (x, y) := if fm == some true then (OExp.prod x y, OExp.prod x y) else (x, y)
    x.unify X τ >>= y.unify Y) σ) >>= List.lookup v

instance {A B : Obj} : Inhabited (Tm A B) := ⟨.var false 0⟩

/-- The spine `t` is headed by a row whose dem is read off its relations (`Prim.dem` `whole` or `arg`). -/
def Tm.whole : {A B : Obj} → Tm A B → Bool
  | _, _, .prim r => (r.dem matches .whole | .arg)
  | _, _, .arg f _ => f.whole
  | _, _, _ => false

/-- The spine `t` is headed by a `bounds` row (`PrimDem`): lazy on `Known`, so no keys are asked of it given its
    relations, whatever they are. -/
def Tm.bounds : {A B : Obj} → Tm A B → Bool
  | _, _, .prim r => r.dem == .bounds
  | _, _, .arg f _ => f.bounds
  | _, _, _ => false

/-- `t` runs on demand (§a): read only at the keys its left context supplies. A function of the constructor and its
    parts, except `var`, which stores its bit; a row made from its relations' whole tables (`Tm.whole`) given all of
    them needs keys where one of them does, its head alone (`prim`) is no term that runs. -/
def Tm.dem : {A B : Obj} → Tm A B → Bool
  | _, _, .arg R x => if R.whole then (!(R matches .prim _) && R.dem) || x.dem else R.dem && !R.bounds
  | _, _, .comp R _ | _, _, .share _ R | _, _, .call _ _ _ _ R => R.dem
  | _, _, .join R S => R.dem || S.dem
  -- `⟨R,S⟩`'s domain is `dom R ∩ dom S`, `R ∩ S` within `R` and `S`, so one closed operand bounds the other
  -- (`GenK.pairK`, `GenK.meetK`); `R − S` within `R`, which bounds `S` (`GenK.diff`)
  | _, _, .pair R S | _, _, .meet R S => R.dem && S.dem
  | _, _, .diff R _ => R.dem
  | _, _, .var d _ => d
  -- an injection's converse runs on the sum values in demand (`Tab.inlConv`); any other converse is read whole
  | _, _, .conv R => (R matches .inl | .inr)
  -- every leaf listed, as in `Tm.fv`
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .ldiv .. | _, _, .rdiv ..
  | _, _, .nu .. | _, _, .mu .. => false
  | _, _, .id | _, _, .top _ | _, _, .outl | _, _, .outr | _, _, .lam _
  | _, _, .mem | _, _, .inl | _, _, .inr | _, _, .prim _
  | _, _, .foldr .. | _, _, .fold .. | _, _, .hylo .. => true

/-- `R × S ≜ ⟨π₁R, π₂S⟩` (`Tm.prod_den`): on demand, each operand on its side of the pairs in demand; where none
    are, the product is closed by its source's universe (`closeRes`, `Tm.prodUni`). -/
def Tm.prod {A B C D : Obj} (R : Tm A B) (S : Tm C D) : Tm (.prod A C) (.prod B D) :=
  .pair (.comp .outl R) (.comp .outr S)

/-- `dom(R) = 𝟙 ∩ R R°`, the row `domRow` given `R` (`Tm.dom_den`). -/
def Tm.dom {A B : Obj} (R : Tm A B) : Tm A A := .arg (.prim domRow) R

/-- `ran(R) = 𝟙 ∩ R° R`, the row `ranRow` given `R` (`Tm.ran_den`). -/
def Tm.ran {A B : Obj} (R : Tm A B) : Tm B B := .arg (.prim ranRow) R

/-- `≤`, `<` on the number universe `U` of the atom `t` (`ltAt`): the row `cmpRelRow` given `U`, run fused
    (`GenK.cmpRel`); its composition `Tm.cmpDef` is tied to it (`Tm.ltDef_den`, `Tm.leqDef_den`). -/
def Tm.leq {t : QAtomicType} (U : Tm (.atom t) (.atom t)) : Tm (.atom t) (.atom t) := .arg (.prim (cmpRelRow false)) U

def Tm.lt {t : QAtomicType} (U : Tm (.atom t) (.atom t)) : Tm (.atom t) (.atom t) := .arg (.prim (cmpRelRow true)) U

/-- `asc(P) : ℕ ⟶ B`, the row `ascRow` given `P` (`Prim.den_ascRow`): the set `dom P` numbered by `Obj.lt` order. -/
def Tm.asc {B : Obj} (P : Tm B B) : Tm .long B := .arg (.prim ascRow) P

/-- `[] : A ⟶ [B]`, the row `nilRow` (`Tm.nil_den`). -/
def Tm.nil {A B : Obj} : Tm A (.arr B) := .prim nilRow

/-- `est(Q) ≜ ∋ ∩ (∈ \ (Q ∪ 𝟙)°)`, the row `estRow` given the pair test `τ(Q)` (`Tm.est_den`). -/
def Tm.est {B : Obj} (Q : Tm (.prod B B) (.prod B B)) : Tm (.arr B) B := .arg (.prim estRow) Q

/-- `front(Q) ≜ Λ(∋ − ∋ (Q − Q°))`, the row `frontRow` given the pair test `τ(Q)` (`Tm.front_den`). -/
def Tm.front {B : Obj} (Q : Tm (.prod B B) (.prod B B)) : Tm (.arr B) (.arr B) := .arg (.prim frontRow) Q

/-- The closed universe `u × v` of a product object, `ran(⟨u, ⊤(v)⟩)`: `u` runs closed and bounds `⊤(v)`, so the
    pair is CROSS of `u`'s values and `v`'s, which `Tab.top` and `Tab.pair` refuse past `crossMax`
    (`Tm.prodUni_den`). -/
def Tm.prodUni {A B : Obj} (u : Tm A A) (v : Tm B B) : Tm (.prod A B) (.prod A B) :=
  .ran (.pair u (.top v))

/-- A unary atom row `r` (`succRow`) cut to the universe `U`: `U r U` (§3.5, `Tm.cut1_den`). -/
def Tm.cut1 {A : Obj} (r : Prim) (U : Tm A A) : Tm A A := .comp U (.comp (.prim r) U)

/-- A binary atom row `r` (`arithRow`) cut to the universe `U`: `(U×U) r U`, i.e. `⟨π₁U, π₂U⟩ r U` (§3.5,
    `Tm.cut2_den`). -/
def Tm.cut2 {A : Obj} (r : Prim) (U : Tm A A) : Tm (.prod A A) A := .comp (U.prod U) (.comp (.prim r) U)

/-- One per node, a `prim` one whatever its row: `kids` puts `mem` for `mapRow`, and must not grow a term
    (`size_kids`), since `Tm.gen` recurses into `kids` of a `hylo`'s body. -/
def Tm.size : {A B : Obj} → Tm A B → Nat
  | _, _, .top R | _, _, .conv R | _, _, .lam R
  | _, _, .share _ R | _, _, .mu _ _ _ R | _, _, .hylo _ _ R | _, _, .call _ _ _ _ R =>
    R.size + 1
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S
  | _, _, .foldr R S | _, _, .fold R S | _, _, .arg R S
  | _, _, .nu _ R S => R.size + S.size + 1
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.size + S.size + U.size + V.size + 1
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .mem
  | _, _, .inl | _, _, .inr | _, _, .prim _ | _, _, .var .. => 1

local macro "lt_size" : term => `(by simp only [Tm.size]; omega)

/-- `t` with each of its parts through `f`, one level down, `f` given that the part is smaller than `t`, so a walk
    may recurse on it with `termination_by t.size` (`Tm.number`). A `share` is closed and numbered, so no walk
    enters it. -/
def Tm.mapMSz {m : Type → Type} [Monad m] : {A B : Obj} → (t : Tm A B) →
    ({C D : Obj} → (c : Tm C D) → c.size < t.size → m (Tm C D)) → m (Tm A B)
  | _, _, .top V, f => return .top (← f V lt_size)
  | _, _, .comp R S, f => return .comp (← f R lt_size) (← f S lt_size)
  | _, _, .conv R, f => return .conv (← f R lt_size)
  | _, _, .meet R S, f => return .meet (← f R lt_size) (← f S lt_size)
  | _, _, .join R S, f => return .join (← f R lt_size) (← f S lt_size)
  | _, _, .diff R S, f => return .diff (← f R lt_size) (← f S lt_size)
  | _, _, .ldiv R S U V, f => return .ldiv (← f R lt_size) (← f S lt_size) (← f U lt_size) (← f V lt_size)
  | _, _, .rdiv R S U V, f => return .rdiv (← f R lt_size) (← f S lt_size) (← f U lt_size) (← f V lt_size)
  | _, _, .pair R S, f => return .pair (← f R lt_size) (← f S lt_size)
  | _, _, .lam R, f => return .lam (← f R lt_size)
  | _, _, .foldr e S, f => return .foldr (← f e lt_size) (← f S lt_size)
  | _, _, .fold e S, f => return .fold (← f e lt_size) (← f S lt_size)
  | _, _, .arg g x, f => return .arg (← f g lt_size) (← f x lt_size)
  | _, _, .nu k S b, f => return .nu k (← f S lt_size) (← f b lt_size)
  | _, _, .mu k w n b, f => return .mu k w n (← f b lt_size)
  | _, _, .hylo k w b, f => return .hylo k w (← f b lt_size)
  | _, _, t, _ => pure t

/-- `t` with each of its parts through `f`, one level down; every walk over `Tm` is an instance (`Tm.parts`,
    `Tm.fv`, `Expand.mus`, `Tm.number`), through `Tm.mapMSz`. -/
def Tm.mapM {m : Type → Type} [Monad m] (f : {A B : Obj} → Tm A B → m (Tm A B)) {A B : Obj} (t : Tm A B) :
    m (Tm A B) :=
  t.mapMSz fun c _ => f c

/-- The parts of `t`, in `Tm.mapM`'s order. -/
def Tm.parts {A B : Obj} (t : Tm A B) : List Res :=
  (Id.run ((t.mapM (m := StateM (List Res)) fun c => do modify (· ++ [⟨_, _, c⟩]); pure c).run [])).2

/-- The terms a check over every node of `t` visits next: its parts, and the term `Tm.mapM` does not enter, a
    `share`'s and a call's body, since a `callOf` call's body is no registry constant's. -/
def Tm.inner {A B : Obj} : Tm A B → List Res
  | .share _ R | .call _ _ _ _ R => [⟨_, _, R⟩]
  | t => t.parts

/-- The variables free in `t`: a binder (`μ`, `ν`, `hylo`) drops its own, and a `share` is closed. Structural,
    so `den_congr` can be stated with it. -/
def Tm.fv : {A B : Obj} → Tm A B → List Nat
  | _, _, .var _ k => [k]
  | _, _, .top V => V.fv
  | _, _, .comp R S => R.fv ++ S.fv
  | _, _, .conv R => R.fv
  | _, _, .meet R S => R.fv ++ S.fv
  | _, _, .join R S => R.fv ++ S.fv
  | _, _, .diff R S => R.fv ++ S.fv
  | _, _, .ldiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, .rdiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, .pair R S => R.fv ++ S.fv
  | _, _, .lam R => R.fv
  | _, _, .foldr e S | _, _, .fold e S => e.fv ++ S.fv
  | _, _, .arg g x => g.fv ++ x.fv
  | _, _, .nu k S b => S.fv ++ b.fv.filter (· != k)
  | _, _, .mu k _ _ b => b.fv.filter (· != k)
  | _, _, .hylo k _ b => b.fv.filter (· != k)
  -- every leaf listed: a wildcard makes the equation lemmas of this 40-constructor family slow to build
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .mem | _, _, .inl | _, _, .inr | _, _, .prim _ | _, _, .share .. | _, _, .call .. => []

/-! ### Substitution -/

/-- A substitution: each entry `(k, ⟨A, B, s⟩)` puts the closed term `s : A ⟶ B` for the variable `k`, the first
    entry for `k` winning, and a variable with no entry stays. The syntax side of `Val` (`Tm.Sub.den`). -/
abbrev Tm.Sub := List (Nat × (A : Obj) × (B : Obj) × Tm A B)

/-- What `σ` puts for the variable `i` used at `A' ⟶ B'` with demand bit `d`: its entry's term where the objects
    match, `𝟘` where they do not, as `Val.bind` reads a variable at other objects; with no entry, the variable. -/
def Tm.Sub.get (i : Nat) {A' B' : Obj} (d : Bool) : Tm.Sub → Tm A' B'
  | [] => .var d i
  | (k, ⟨A, B, s⟩) :: σ => if i = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ s else .zero) else Sub.get i d σ

/-- The variables free in the terms of `σ`. -/
def Tm.Sub.fvs : Tm.Sub → List Nat
  | [] => []
  | (_, ⟨_, _, s⟩) :: σ => s.fv ++ fvs σ

/-- A variable above every one of `l`. -/
def Tm.fresh (l : List Nat) : Nat := l.foldr max 0 + 1

/-- `t` with `σ` put for its free variables. A binder is renamed to a variable `fresh` for its body and `σ`, so no
    variable of `σ` is captured, whatever `σ` holds. A `share` is closed, so it is kept. -/
def Tm.subst : Tm.Sub → {A B : Obj} → Tm A B → Tm A B
  | σ, _, _, .var d i => σ.get i d
  | σ, _, _, .top V => .top (V.subst σ)
  | σ, _, _, .comp R S => .comp (R.subst σ) (S.subst σ)
  | σ, _, _, .conv R => .conv (R.subst σ)
  | σ, _, _, .meet R S => .meet (R.subst σ) (S.subst σ)
  | σ, _, _, .join R S => .join (R.subst σ) (S.subst σ)
  | σ, _, _, .diff R S => .diff (R.subst σ) (S.subst σ)
  | σ, _, _, .ldiv R S U V => .ldiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, .rdiv R S U V => .rdiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, .pair R S => .pair (R.subst σ) (S.subst σ)
  | σ, _, _, .lam R => .lam (R.subst σ)
  | σ, _, _, .foldr e S => .foldr (e.subst σ) (S.subst σ)
  | σ, _, _, .fold e S => .fold (e.subst σ) (S.subst σ)
  | σ, _, _, .arg g x => .arg (g.subst σ) (x.subst σ)
  | σ, A, B, .nu k S b =>
    .nu (fresh (b.fv ++ σ.fvs)) (S.subst σ) (b.subst ((k, ⟨A, B, .var false (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | σ, A, B, .mu k w n b =>
    .mu (fresh (b.fv ++ σ.fvs)) w n (b.subst ((k, ⟨A, B, .var false (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | σ, A, B, .hylo k w b =>
    .hylo (fresh (b.fv ++ σ.fvs)) w (b.subst ((k, ⟨A, B, .var false (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | _, _, _, .val R => .val R
  | _, _, _, .uni U => .uni U
  | _, _, _, .zero => .zero
  | _, _, _, .id => .id
  | _, _, _, .outl => .outl
  | _, _, _, .outr => .outr
  | _, _, _, .mem => .mem
  | _, _, _, .inl => .inl
  | _, _, _, .inr => .inr
  | _, _, _, .prim r => .prim r
  | _, _, _, .share k R => .share k R
  | _, _, _, .call ks c cv os b => .call ks c cv os b

mutual
/-- `X`, the variable `k`, occurs in `t` only with sign `s` (`true` positive): the one monotonicity check (D5 = J),
    `den_mono`/`den_anti`. A node with no rule below must not mention `k` at all. `ldiv`'s `R` and `rdiv`'s `S`
    occur on both sides (`ldivDen`'s `∀` and its `∃`), so they must be free of `k`; `Λ`, `front` hold an image
    whole (`lamDen`'s `↔`), so their part must be too. A row given any number of relations passes their sign where
    its `prims` entry is `mono` (`Tm.spinePol`, `rowDens_mono`), `F(X)` among them. -/
def Tm.pol (s : Bool) (k : Nat) : {A B : Obj} → Tm A B → Bool
  | _, _, .var _ j => if j == k then s else true
  | _, _, .top V => V.pol s k
  | _, _, .comp R S => R.pol s k && S.pol s k
  | _, _, .conv R => R.pol s k
  | _, _, .meet R S => R.pol s k && S.pol s k
  | _, _, .join R S => R.pol s k && S.pol s k
  | _, _, .diff R S => R.pol s k && S.pol (!s) k
  | _, _, .ldiv R S U V => !R.fv.contains k && S.pol s k && U.pol s k && V.pol s k
  | _, _, .rdiv R S U V => R.pol s k && !S.fv.contains k && U.pol s k && V.pol s k
  | _, _, .pair R S => R.pol s k && S.pol s k
  | _, _, .nu j S b => S.pol s k && (j == k || b.pol s k)
  | _, _, .mu j _ _ b => j == k || b.pol s k
  | _, _, .hylo j _ b => j == k || b.pol s k
  | _, _, .foldr e S | _, _, .fold e S => e.pol s k && S.pol s k
  | _, _, t@(.arg f x) => f.spinePol s k && x.pol s k || !t.fv.contains k
  | _, _, t@(.lam _) => !t.fv.contains k
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .mem | _, _, .inl | _, _, .inr | _, _, .prim _ | _, _, .share .. | _, _, .call .. => true

/-- `t` a `mono` row (`prims`) given relations, each occurring with sign `s` in `k` (`Tm.pol`): the spine
    `.arg (… (.arg (.prim r) x₁) …) xₙ`, of any length `n` (`Tm.den_pol_spine`). -/
def Tm.spinePol (s : Bool) (k : Nat) : {A B : Obj} → Tm A B → Bool
  | _, _, .prim r => (Prim.find? r.sym).any (·.mono)
  | _, _, .arg f x => f.spinePol s k && x.pol s k
  | _, _, _ => false
end

/-- `X`, the variable `k`, occurs in `t` only where `⟦t⟧` distributes over `∪` in it, `⟦t⟧(X ∪ Y) ⊑ ⟦t⟧X ∪ ⟦t⟧Y`
    (`Tm.den_linIn`): what lets `μ` run semi-naive (`Tab.muLin`). `k` itself, a part free of `k`, `∪` of two such, `°`
    and `own` of one, `≫`, `∩`, `⟨,⟩` with `k` in one operand only: in both, `(X ∪ Y) ≫ (X ∪ Y)` holds `X ≫ Y`. Any
    other node holding `k` fails: `−`, `Λ`, a division (`∀`), a fold or nested fixed point, a row's argument (`F(X ∪ Y)`
    relates lists mixing `X` and `Y` steps, which neither `F(X)` nor `F(Y)` holds). -/
def Tm.linIn (k : Nat) : {A B : Obj} → Tm A B → Bool
  | _, _, .var _ _ => true
  | _, _, .join R S => R.linIn k && S.linIn k
  | _, _, .comp R S | _, _, .meet R S | _, _, .pair R S =>
    R.linIn k && !S.fv.contains k || !R.fv.contains k && S.linIn k
  | _, _, .conv R => R.linIn k
  | _, _, t => !t.fv.contains k

/-! ### The children of a recursion -/

/-- `∋` at `C ⟶ E`: `mem` where `C` is `[E]`, `𝟘` at any other objects, as a row's meaning is at objects not its
    own (`Prim.den`); what `kids` puts for `F(x)`, whose source a row's type does not fix. -/
def Tm.memAt : (C E : Obj) → Tm C E
  | .arr B, E => if h : B = E then h ▸ .mem else .zero
  | _, _ => .zero

@[simp] theorem Tm.size_memAt (C E : Obj) : (Tm.memAt C E).size = 1 := by
  unfold Tm.memAt; split <;> (try split) <;> (try subst_vars) <;> rfl

/-- `𝟙` at `C ⟶ E`: `id` where `C` is `E`, `𝟘` at any other objects; what `kids` puts for `dom(x)`, which reads
    `x` at its own source, a source a row's type does not tie to `x`'s. -/
def Tm.idAt (C E : Obj) : Tm C E := if h : C = E then h ▸ .id else .zero

@[simp] theorem Tm.size_idAt (C E : Obj) : (Tm.idAt C E).size = 1 := by
  unfold Tm.idAt; split <;> (try subst_vars) <;> rfl

/-- The children `t` reads the variable `k : A ⟶ _` at: from `t`'s source to the nodes of `A` (`Tm.den_local`);
    `𝟘` where `t` does not mention `k`, `none` where it reads `k` in a shape no relation bounds. The shapes are
    those `hyloG` builds `G(X)` from: the place, `⟨ , ⟩`, `[ , ]`, `F`, a part composed with a closed one. -/
def Tm.kids (k : Nat) (A : Obj) {C D : Obj} (t : Tm C D) : Option (Tm C A) :=
  if t.fv.contains k then
    match C, D, t with
    | C, _, .var _ _ => if h : C = A then some (h ▸ .id) else some .zero
    | _, _, .comp R S =>
      if !S.fv.contains k then R.kids k A
      else if R.fv.contains k then none
      else match S.kids k A with | some s => some (.comp R s) | none => none
    | _, _, .meet R S | _, _, .join R S | _, _, .pair R S => match R.kids k A, S.kids k A with
      | some r, some s => some (.join r s) | _, _ => none
    -- `F(x)` reads `X` at the children of the members, `dom(x)` at those of its key
    | _, _, .arg (.prim r) x =>
      if r.sym == mapRow.sym then match x.kids k A with | some s => some (.comp (memAt _ _) s) | none => none
      else if r.sym == domRow.sym then match x.kids k A with | some s => some (.comp (idAt _ _) s) | none => none
      else none
    | _, _, _ => none
  else some .zero

theorem Tm.size_kids (k : Nat) (A : Obj) {C D : Obj} (t : Tm C D) : ((t.kids k A).getD .zero).size ≤ t.size := by
  induction t
  case arg f x _ _ => cases f <;> unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> simp_all [Tm.size] <;> omega
  all_goals unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> (try subst_vars) <;> simp_all [Tm.size] <;> omega

end Rel.Lang
