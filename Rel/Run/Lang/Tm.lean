import Rel.Run.Algebra
import Rel.Run.Lang.Syntax

/-! The core term `Tm` of the Rel language, indexed by its source and target, and `Tm.dem`, whether it runs on
    demand; the elaborator (`Elab`) builds it and `Expand` reads it (`doc/rel-lang-design.md` §a, §e). -/

namespace Rel.Lang

open Tab Rel.Alg

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
  | dom {A B : Obj} (R : Tm A B) : Tm A A
  | ran {A B : Obj} (R : Tm A B) : Tm B B
  | ldiv {A B C : Obj} (R : Tm A B) (S : Tm A C) (UB : Tm B B) (UC : Tm C C) : Tm B C
  | rdiv {A B C : Obj} (R : Tm A C) (S : Tm B C) (UA : Tm A A) (UB : Tm B B) : Tm A B
  | pair {A B C : Obj} (R : Tm A B) (S : Tm A C) : Tm A (.prod B C)
  | prod {A B C D : Obj} (R : Tm A B) (S : Tm C D) : Tm (.prod A C) (.prod B D)
  | junc {A B C : Obj} (R : Tm A C) (S : Tm B C) : Tm (.sum A B) C
  /-- `[R,S]` on the keys in demand, a part with no universe to be read whole on: each part run on the values of
      its side the demand holds. -/
  | juncD {A B C : Obj} (R : Tm A C) (S : Tm B C) : Tm (.sum A B) C
  /-- `Λ(R)`, a map: total on the keys in demand, `[]` where `R` has no image, so it always runs on demand and a
      closed use reads its source's universe (`closeRes`). -/
  | lam {A B : Obj} (R : Tm A B) : Tm A (.arr B)
  | E {A B : Obj} (R : Tm A B) : Tm (.arr A) (.arr B)
  /-- An operator that takes an order `Q : B ⟶ B` (or a coreflexive `p`) holds it as its pair test
      `τ(Q) : B×B ⟶ B×B` (§a), run on demand on the pairs the operator compares. -/
  | est {B : Obj} (Q : Tm (.prod B B) (.prod B B)) : Tm (.arr B) B
  | thin {B : Obj} (Q : Tm (.prod B B) (.prod B B)) : Tm (.arr B) (.arr B)
  | nil {A B : Obj} : Tm A (.arr B)
  /-- The row `r` of `prims` at `A ⟶ B`, an instance of its constant's type; its relations given by `arg`. -/
  | prim {A B : Obj} (r : Prim) : Tm A B
  /-- `at(k)`, the element at position `k` from `0`, on the arrays in demand. -/
  | atPos {B : Obj} (k : Nat) : Tm (.arr B) B
  /-- The prelude's `perm`, kept as its own converse (`convTm`): the one converse rule the language has for a
      definition, because `perm° = perm` is a theorem it cannot derive from the fold `perm` is. -/
  | own {A : Obj} (R : Tm A A) : Tm A A
  /-- `succ`, the kernel's value verb `k` (`plus`, `times`, …), `≤`, `<` on the number universe `U`: a declared
      object's (`uni`), or the one a constant is given for an object variable (`var`). -/
  | succ (U : Tm .long .long) : Tm .long .long
  | arith (k : UInt8) (U : Tm .long .long) : Tm (.prod .long .long) .long
  | leq (U : Tm .long .long) : Tm .long .long
  | lt (U : Tm .long .long) : Tm .long .long
  /-- `⦇e,S⦈ʳ`, the right fold, on the arrays in demand: each read from its end, `S` on `(x, acc)`. -/
  | foldr {E V : Obj} (e : Tm V V) (S : Tm (.prod E V) V) : Tm (.arr E) V
  /-- `⦇e,S⦈`, the left fold, on the arrays in demand: each read from index 0, `S` on `(acc, x)`. -/
  | fold {E V : Obj} (e : Tm V V) (S : Tm (.prod V E) V) : Tm (.arr E) V
  /-- `R`, closed, numbered `k` among the expansion's sub-terms (`Expand.number`): its code is built once
      (`Expand.code`). -/
  | share {A B : Obj} (k : Nat) (R : Tm A B) : Tm A B
  /-- `⦇e,S⦈` given a family (§e), on the pairs (key, array) in demand: one fold with carrier `I×V`, seeded at
      each key by the fibre of `e` there, its step `S` given `((i,v),x)` and carrying the key `i`. -/
  | foldI {I E V : Obj} (e : Tm I (.prod V V)) (S : Tm (.prod (.prod I V) E) (.prod I V)) :
      Tm (.prod I (.arr E)) V
  /-- `Rᴵ`, the family `R : I ⟶ A×B` as one relation of the key and the source, on the pairs (key, source) in
      demand: `R` at their keys, each row `(i,(a,b))` re-keyed as `((i,a),b)`, then joined with the pairs. -/
  | flat {I A B : Obj} (R : Tm I (.prod A B)) : Tm (.prod I A) B
  /-- The variable `k` of the fixed point that binds it: its value in the round being run; or a constant's
      parameter, on the keys in demand when its argument is a pair test (`Form`). `d`: its demand bit, which the
      use site fixes, as `call` stores its own. -/
  | var {A B : Obj} (d : Bool) (k : Nat) : Tm A B
  /-- The constant `c` a parametric definition was elaborated once to, before its arguments (`arg`): called, its
      body not expanded; its plan runs on the keys in demand when `d`. `os`: the objects of the object variables it
      is generic over; `cv`: its converse's constant and demand bit, when its body has a converse (`convTm`). -/
  | call {A B : Obj} (d : Bool) (c : Lean.Name) (os : List Obj) (cv : Option (Lean.Name × Bool)) : Tm A B
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

instance {A B : Obj} : Inhabited (Tm A B) := ⟨.var false 0⟩

/-- `t` runs on demand (§a): read only at the keys its left context supplies. A function of the constructor and its
    parts, except `var` and `call`, which store their bit. -/
def Tm.dem : {A B : Obj} → Tm A B → Bool
  | _, _, .comp R _ | _, _, .dom R | _, _, .own R | _, _, .share _ R | _, _, .arg R _ => R.dem
  | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S => R.dem || S.dem
  | _, _, .var d _ | _, _, .call d .. => d
  -- every leaf listed, as in `Tm.fv`
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .conv _ | _, _, .ran _ | _, _, .ldiv .. | _, _, .rdiv ..
  | _, _, .prod .. | _, _, .junc .. | _, _, .leq _ | _, _, .lt _ | _, _, .nu .. | _, _, .mu .. => false
  | _, _, .id | _, _, .top _ | _, _, .outl | _, _, .outr | _, _, .juncD .. | _, _, .lam _ | _, _, .E _
  | _, _, .est _ | _, _, .thin _ | _, _, .nil | _, _, .prim _ | _, _, .atPos _ | _, _, .succ _ | _, _, .arith ..
  | _, _, .foldr .. | _, _, .fold .. | _, _, .foldI .. | _, _, .flat _ | _, _, .hylo .. => true

/-- `t` with each of its parts through `f`, one level down; every walk over `Tm` is an instance (`Tm.parts`,
    `Tm.fv`, `Expand.mus`, `Expand.number`). A `share` is closed and numbered, so no walk enters it. -/
def Tm.mapM {m : Type → Type} [Monad m] (f : {A B : Obj} → Tm A B → m (Tm A B)) :
    {A B : Obj} → Tm A B → m (Tm A B)
  | _, _, .top V => return .top (← f V)
  | _, _, .comp R S => return .comp (← f R) (← f S)
  | _, _, .conv R => return .conv (← f R)
  | _, _, .meet R S => return .meet (← f R) (← f S)
  | _, _, .join R S => return .join (← f R) (← f S)
  | _, _, .diff R S => return .diff (← f R) (← f S)
  | _, _, .dom R => return .dom (← f R)
  | _, _, .ran R => return .ran (← f R)
  | _, _, .ldiv R S U V => return .ldiv (← f R) (← f S) (← f U) (← f V)
  | _, _, .rdiv R S U V => return .rdiv (← f R) (← f S) (← f U) (← f V)
  | _, _, .pair R S => return .pair (← f R) (← f S)
  | _, _, .prod R S => return .prod (← f R) (← f S)
  | _, _, .junc R S => return .junc (← f R) (← f S)
  | _, _, .juncD R S => return .juncD (← f R) (← f S)
  | _, _, .lam R => return .lam (← f R)
  | _, _, .E R => return .E (← f R)
  | _, _, .est Q => return .est (← f Q)
  | _, _, .thin Q => return .thin (← f Q)
  | _, _, .own R => return .own (← f R)
  | _, _, .succ U => return .succ (← f U)
  | _, _, .arith k U => return .arith k (← f U)
  | _, _, .leq U => return .leq (← f U)
  | _, _, .lt U => return .lt (← f U)
  | _, _, .foldr e S => return .foldr (← f e) (← f S)
  | _, _, .fold e S => return .fold (← f e) (← f S)
  | _, _, .foldI e S => return .foldI (← f e) (← f S)
  | _, _, .flat R => return .flat (← f R)
  | _, _, .arg g x => return .arg (← f g) (← f x)
  | _, _, .nu k S b => return .nu k (← f S) (← f b)
  | _, _, .mu k w n b => return .mu k w n (← f b)
  | _, _, .hylo k w b => return .hylo k w (← f b)
  | _, _, t => pure t

/-- The parts of `t`, in `Tm.mapM`'s order. -/
def Tm.parts {A B : Obj} (t : Tm A B) : List Res :=
  (Id.run ((t.mapM (m := StateM (List Res)) fun c => do modify (· ++ [⟨_, _, c⟩]); pure c).run [])).2

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
  | _, _, .dom R => R.fv
  | _, _, .ran R => R.fv
  | _, _, .ldiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, .rdiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, .pair R S => R.fv ++ S.fv
  | _, _, .prod R S => R.fv ++ S.fv
  | _, _, .junc R S => R.fv ++ S.fv
  | _, _, .juncD R S => R.fv ++ S.fv
  | _, _, .lam R => R.fv
  | _, _, .E R => R.fv
  | _, _, .est Q => Q.fv
  | _, _, .thin Q => Q.fv
  | _, _, .own R => R.fv
  | _, _, .succ U => U.fv
  | _, _, .arith _ U => U.fv
  | _, _, .leq U => U.fv
  | _, _, .lt U => U.fv
  | _, _, .foldr e S | _, _, .fold e S => e.fv ++ S.fv
  | _, _, .foldI e S => e.fv ++ S.fv
  | _, _, .flat R => R.fv
  | _, _, .arg g x => g.fv ++ x.fv
  | _, _, .nu k S b => S.fv ++ b.fv.filter (· != k)
  | _, _, .mu k _ _ b => b.fv.filter (· != k)
  | _, _, .hylo k _ b => b.fv.filter (· != k)
  -- every leaf listed: a wildcard makes the equation lemmas of this 40-constructor family slow to build
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .nil | _, _, .prim _ | _, _, .atPos _ | _, _, .share .. | _, _, .call .. => []

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
  | σ, _, _, .dom R => .dom (R.subst σ)
  | σ, _, _, .ran R => .ran (R.subst σ)
  | σ, _, _, .ldiv R S U V => .ldiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, .rdiv R S U V => .rdiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, .pair R S => .pair (R.subst σ) (S.subst σ)
  | σ, _, _, .prod R S => .prod (R.subst σ) (S.subst σ)
  | σ, _, _, .junc R S => .junc (R.subst σ) (S.subst σ)
  | σ, _, _, .juncD R S => .juncD (R.subst σ) (S.subst σ)
  | σ, _, _, .lam R => .lam (R.subst σ)
  | σ, _, _, .E R => .E (R.subst σ)
  | σ, _, _, .est Q => .est (Q.subst σ)
  | σ, _, _, .thin Q => .thin (Q.subst σ)
  | σ, _, _, .own R => .own (R.subst σ)
  | σ, _, _, .succ U => .succ (U.subst σ)
  | σ, _, _, .arith k U => .arith k (U.subst σ)
  | σ, _, _, .leq U => .leq (U.subst σ)
  | σ, _, _, .lt U => .lt (U.subst σ)
  | σ, _, _, .foldr e S => .foldr (e.subst σ) (S.subst σ)
  | σ, _, _, .fold e S => .fold (e.subst σ) (S.subst σ)
  | σ, _, _, .foldI e S => .foldI (e.subst σ) (S.subst σ)
  | σ, _, _, .flat R => .flat (R.subst σ)
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
  | _, _, _, .nil => .nil
  | _, _, _, .prim r => .prim r
  | _, _, _, .atPos k => .atPos k
  | _, _, _, .share k R => .share k R
  | _, _, _, .call d c os cv => .call d c os cv

/-- `X`, the variable `k`, occurs in `t` only with sign `s` (`true` positive): the one monotonicity check (D5 = J),
    `den_mono`/`den_anti`. A node with no rule below must not mention `k` at all. `ldiv`'s `R` and `rdiv`'s `S`
    occur on both sides (`ldivDen`'s `∀` and its `∃`), so they must be free of `k`; `Λ`, `E`, `thin` hold an image
    whole (`lamDen`'s `↔`), so their part must be too. A row passes its argument's sign where its `prims` entry is
    `mono` (`rowDens_mono`), `F(X)` among them. -/
def Tm.pol (s : Bool) (k : Nat) : {A B : Obj} → Tm A B → Bool
  | _, _, .var _ j => if j == k then s else true
  | _, _, .top V => V.pol s k
  | _, _, .comp R S => R.pol s k && S.pol s k
  | _, _, .conv R => R.pol s k
  | _, _, .meet R S => R.pol s k && S.pol s k
  | _, _, .join R S => R.pol s k && S.pol s k
  | _, _, .diff R S => R.pol s k && S.pol (!s) k
  | _, _, .dom R => R.pol s k
  | _, _, .ran R => R.pol s k
  | _, _, .ldiv R S U V => !R.fv.contains k && S.pol s k && U.pol s k && V.pol s k
  | _, _, .rdiv R S U V => R.pol s k && !S.fv.contains k && U.pol s k && V.pol s k
  | _, _, .pair R S => R.pol s k && S.pol s k
  | _, _, .prod R S => R.pol s k && S.pol s k
  | _, _, .junc R S => R.pol s k && S.pol s k
  | _, _, .juncD R S => R.pol s k && S.pol s k
  | _, _, .own R => R.pol s k
  | _, _, .nu j S b => S.pol s k && (j == k || b.pol s k)
  | _, _, .mu j _ _ b => j == k || b.pol s k
  | _, _, .hylo j _ b => j == k || b.pol s k
  | _, _, .est Q => Q.pol s k
  | _, _, .succ U | _, _, .arith _ U | _, _, .leq U | _, _, .lt U => U.pol s k
  | _, _, .foldr e S | _, _, .fold e S | _, _, .foldI e S => e.pol s k && S.pol s k
  | _, _, .flat R => R.pol s k
  | _, _, t@(.arg (.prim r) x) => (Prim.find? r.sym).any (·.mono) && x.pol s k || !t.fv.contains k
  | _, _, t@(.lam _) | _, _, t@(.E _) | _, _, t@(.thin _) | _, _, t@(.arg ..) => !t.fv.contains k
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .nil | _, _, .prim _ | _, _, .atPos _ | _, _, .share .. | _, _, .call .. => true

/-! ### The children of a recursion -/

/-- One per node, a `prim` one whatever its row: `kids` puts `memRow` for `mapRow`, and must not grow a term
    (`size_kids`), since `Tm.gen` recurses into `kids` of a `hylo`'s body. -/
def Tm.size : {A B : Obj} → Tm A B → Nat
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .est R
  | _, _, .thin R | _, _, .own R | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R | _, _, .flat R
  | _, _, .share _ R | _, _, .mu _ _ _ R | _, _, .hylo _ _ R => R.size + 1
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .junc R S | _, _, .juncD R S | _, _, .foldr R S | _, _, .fold R S | _, _, .foldI R S | _, _, .arg R S
  | _, _, .nu _ R S => R.size + S.size + 1
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.size + S.size + U.size + V.size + 1
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil | _, _, .prim _
  | _, _, .atPos _ | _, _, .var .. | _, _, .call .. => 1

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
    | _, _, .junc R S | _, _, .juncD R S => match R.kids k A, S.kids k A with
      | some r, some s => some (.junc r s) | _, _ => none
    | _, _, .dom R | _, _, .own R => R.kids k A
    -- `F(x)` reads `X` at the children of the members
    | _, _, .arg (.prim r) x =>
      if r.sym == mapRow.sym then match x.kids k A with | some s => some (.comp (.prim memRow) s) | none => none
      else none
    | _, _, _ => none
  else some .zero

theorem Tm.size_kids (k : Nat) (A : Obj) {C D : Obj} (t : Tm C D) : ((t.kids k A).getD .zero).size ≤ t.size := by
  induction t
  case arg f x _ _ => cases f <;> unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> simp_all [Tm.size] <;> omega
  all_goals unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> (try subst_vars) <;> simp_all [Tm.size] <;> omega

end Rel.Lang
