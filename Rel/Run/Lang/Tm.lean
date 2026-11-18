import Rel.Run.Algebra
import Rel.Run.Lang.Syntax

/-! The core term `Tm` of the Rel language, indexed by its source, target and whether it runs on demand; the
    elaborator (`Elab`) builds it and `Expand` reads it (`doc/rel-lang-design.md` §a, §e). -/

namespace Rel.Lang

open Tab Rel.Alg

/-! ### The core term -/

/-- A core term `A ⟶ B` over `Alg`. `d` says it runs on DEMAND (§a): its value is read only at the keys the
    coreflexive its left context supplies. A term with `d = false` needs no keys: a closed term. -/
inductive Tm : Obj → Obj → Bool → Type where
  | val {A B : Obj} (R : Tab A B) : Tm A B false
  | uni {A : Obj} {m : USize} (U : Vals A m) : Tm A A false
  | zero {A B : Obj} : Tm A B false
  | id {A : Obj} : Tm A A true
  /-- `⊤` onto the values of the closed coreflexive `V`. -/
  | top {A B : Obj} (V : Tm B B false) : Tm A B true
  | outl {A B : Obj} : Tm (.prod A B) A true
  | outr {A B : Obj} : Tm (.prod A B) B true
  | comp {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm B C e) : Tm A C d
  | conv {A B : Obj} (R : Tm A B false) : Tm B A false
  | meet {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | join {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | diff {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | dom {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A A d
  | ran {A B : Obj} (R : Tm A B false) : Tm B B false
  | ldiv {A B C : Obj} (R : Tm A B false) (S : Tm A C false) (UB : Tm B B false) (UC : Tm C C false) : Tm B C false
  | rdiv {A B C : Obj} (R : Tm A C false) (S : Tm B C false) (UA : Tm A A false) (UB : Tm B B false) : Tm A B false
  | pair {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A C e) : Tm A (.prod B C) (d || e)
  | prod {A B C D : Obj} (R : Tm A B false) (S : Tm C D false) : Tm (.prod A C) (.prod B D) false
  | junc {A B C : Obj} (R : Tm A C false) (S : Tm B C false) : Tm (.sum A B) C false
  /-- `[R,S]` on the keys in demand, a part with no universe to be read whole on: each part run on the values of
      its side the demand holds. -/
  | juncD {A B C : Obj} {d e : Bool} (R : Tm A C d) (S : Tm B C e) : Tm (.sum A B) C true
  /-- `Λ(R)`, a map: total on the keys in demand, `[]` where `R` has no image, so it always runs on demand and a
      closed use reads its source's universe (`closeRes`). -/
  | lam {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A (.arr B) true
  | E {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  /-- An operator that takes an order `Q : B ⟶ B` (or a coreflexive `p`) holds it as its pair test
      `τ(Q) : B×B ⟶ B×B` (§a), run on demand on the pairs the operator compares. -/
  | est {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) B true
  | thin {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) (.arr B) true
  | nil {A B : Obj} : Tm A (.arr B) true
  /-- The row `r` of `prims` at `A ⟶ B`, an instance of its constant's type; its relations given by `arg`. -/
  | prim {A B : Obj} (r : Prim) : Tm A B true
  /-- `at(k)`, the element at position `k` from `0`, on the arrays in demand. -/
  | atPos {B : Obj} (k : Nat) : Tm (.arr B) B true
  /-- The prelude's `perm`, kept as its own converse (`convTm`): the one converse rule the language has for a
      definition, because `perm° = perm` is a theorem it cannot derive from the fold `perm` is. -/
  | own {A : Obj} {d : Bool} (R : Tm A A d) : Tm A A d
  /-- `succ`, the kernel's value verb `k` (`plus`, `times`, …), `≤`, `<` on the number universe `U`: a declared
      object's (`uni`), or the one a constant is given for an object variable (`var`). -/
  | succ (U : Tm .long .long false) : Tm .long .long true
  | arith (k : UInt8) (U : Tm .long .long false) : Tm (.prod .long .long) .long true
  | leq (U : Tm .long .long false) : Tm .long .long false
  | lt (U : Tm .long .long false) : Tm .long .long false
  /-- `⦇e,S⦈ʳ`, the right fold, on the arrays in demand: each read from its end, `S` on `(x, acc)`. -/
  | foldr {E V : Obj} {d : Bool} (e : Tm V V false) (S : Tm (.prod E V) V d) : Tm (.arr E) V true
  /-- `⦇e,S⦈`, the left fold, on the arrays in demand: each read from index 0, `S` on `(acc, x)`. -/
  | fold {E V : Obj} {d : Bool} (e : Tm V V false) (S : Tm (.prod V E) V d) : Tm (.arr E) V true
  /-- `R`, closed, numbered `k` among the expansion's sub-terms (`Expand.number`): its code is built once
      (`Expand.code`). -/
  | share {A B : Obj} {d : Bool} (k : Nat) (R : Tm A B d) : Tm A B d
  /-- `⦇e,S⦈` given a family (§e), on the pairs (key, array) in demand: one fold with carrier `I×V`, seeded at
      each key by the fibre of `e` there, its step `S` given `((i,v),x)` and carrying the key `i`. -/
  | foldI {I E V : Obj} {d d' : Bool} (e : Tm I (.prod V V) d) (S : Tm (.prod (.prod I V) E) (.prod I V) d') :
      Tm (.prod I (.arr E)) V true
  /-- `Rᴵ`, the family `R : I ⟶ A×B` as one relation of the key and the source, on the pairs (key, source) in
      demand: `R` at their keys, each row `(i,(a,b))` re-keyed as `((i,a),b)`, then joined with the pairs. -/
  | flat {I A B : Obj} {d : Bool} (R : Tm I (.prod A B) d) : Tm (.prod I A) B true
  /-- The variable `k` of the fixed point that binds it: its value in the round being run; or a constant's
      parameter, on the keys in demand when its argument is a pair test (`Form`). -/
  | var {A B : Obj} {d : Bool} (k : Nat) : Tm A B d
  /-- The constant `c` a parametric definition was elaborated once to, before its arguments (`arg`): called, its
      body not expanded; its plan runs on the keys in demand when `d`. `os`: the objects of the object variables it
      is generic over; `cv`: its converse's constant and demand bit, when its body has a converse (`convTm`). -/
  | call {A B : Obj} (d : Bool) (c : Lean.Name) (os : List Obj) (cv : Option (Lean.Name × Bool)) : Tm A B d
  /-- `f` given one more argument `x`: a relation, a pair test, or the universe of one of its object variables. -/
  | arg {A B C D : Obj} {d e : Bool} (f : Tm A B d) (x : Tm C D e) : Tm A B d
  /-- `νX : φ`, `X` the variable `k`: rounds of `body` from `S`, the conjuncts of `φ` without `X`, down to the
      greatest fixed point. -/
  | nu {A B : Obj} (k : Nat) (S body : Tm A B false) : Tm A B false
  /-- `μX : φ`: rounds of `body` from `𝟘` up to the least fixed point, at most `cap`; `what` names the `μ` in the
      failure a run that reaches `cap` first reports. -/
  | mu {A B : Obj} (k : Nat) (what : String) (cap : Nat) (body : Tm A B false) : Tm A B false
  /-- `hylo(c, S)` = `μX : c G(X) S`, `X` the variable `k`, on the keys in demand: bottom-up over the nodes `ch`
      (`c` then `G`'s membership) reaches from them, each node's value `body` run once its children have theirs;
      `what` names the coalgebra `c`, where the failure a cycle of `ch` reports is. -/
  | hylo {A B : Obj} {d e : Bool} (k : Nat) (what : String) (ch : Tm A A d) (body : Tm A B e) : Tm A B true

/-- A built term with its objects. -/
abbrev Res := (A : Obj) × (B : Obj) × (d : Bool) × Tm A B d

instance {A B : Obj} {d : Bool} : Inhabited (Tm A B d) := ⟨.var 0⟩

/-- `t` with each of its parts through `f`, one level down; every walk over `Tm` is an instance (`Tm.parts`,
    `Tm.fv`, `Expand.mus`, `Expand.number`). A `share` is closed and numbered, so no walk enters it. -/
def Tm.mapM {m : Type → Type} [Monad m] (f : {A B : Obj} → {d : Bool} → Tm A B d → m (Tm A B d)) :
    {A B : Obj} → {d : Bool} → Tm A B d → m (Tm A B d)
  | _, _, _, .top V => return .top (← f V)
  | _, _, _, .comp R S => return .comp (← f R) (← f S)
  | _, _, _, .conv R => return .conv (← f R)
  | _, _, _, .meet R S => return .meet (← f R) (← f S)
  | _, _, _, .join R S => return .join (← f R) (← f S)
  | _, _, _, .diff R S => return .diff (← f R) (← f S)
  | _, _, _, .dom R => return .dom (← f R)
  | _, _, _, .ran R => return .ran (← f R)
  | _, _, _, .ldiv R S U V => return .ldiv (← f R) (← f S) (← f U) (← f V)
  | _, _, _, .rdiv R S U V => return .rdiv (← f R) (← f S) (← f U) (← f V)
  | _, _, _, .pair R S => return .pair (← f R) (← f S)
  | _, _, _, .prod R S => return .prod (← f R) (← f S)
  | _, _, _, .junc R S => return .junc (← f R) (← f S)
  | _, _, _, .juncD R S => return .juncD (← f R) (← f S)
  | _, _, _, .lam R => return .lam (← f R)
  | _, _, _, .E R => return .E (← f R)
  | _, _, _, .est Q => return .est (← f Q)
  | _, _, _, .thin Q => return .thin (← f Q)
  | _, _, _, .own R => return .own (← f R)
  | _, _, _, .succ U => return .succ (← f U)
  | _, _, _, .arith k U => return .arith k (← f U)
  | _, _, _, .leq U => return .leq (← f U)
  | _, _, _, .lt U => return .lt (← f U)
  | _, _, _, .foldr e S => return .foldr (← f e) (← f S)
  | _, _, _, .fold e S => return .fold (← f e) (← f S)
  | _, _, _, .foldI e S => return .foldI (← f e) (← f S)
  | _, _, _, .flat R => return .flat (← f R)
  | _, _, _, .arg g x => return .arg (← f g) (← f x)
  | _, _, _, .nu k S b => return .nu k (← f S) (← f b)
  | _, _, _, .mu k w n b => return .mu k w n (← f b)
  | _, _, _, .hylo k w ch b => return .hylo k w (← f ch) (← f b)
  | _, _, _, t => pure t

/-- The parts of `t`, in `Tm.mapM`'s order. -/
def Tm.parts {A B : Obj} {d : Bool} (t : Tm A B d) : List Res :=
  (Id.run ((t.mapM (m := StateM (List Res)) fun c => do modify (· ++ [⟨_, _, _, c⟩]); pure c).run [])).2

/-- The variables free in `t`: a binder (`μ`, `ν`, `hylo`) drops its own, and a `share` is closed. Structural,
    so `den_congr` can be stated with it. -/
def Tm.fv : {A B : Obj} → {d : Bool} → Tm A B d → List Nat
  | _, _, _, .var k => [k]
  | _, _, _, .top V => V.fv
  | _, _, _, .comp R S => R.fv ++ S.fv
  | _, _, _, .conv R => R.fv
  | _, _, _, .meet R S => R.fv ++ S.fv
  | _, _, _, .join R S => R.fv ++ S.fv
  | _, _, _, .diff R S => R.fv ++ S.fv
  | _, _, _, .dom R => R.fv
  | _, _, _, .ran R => R.fv
  | _, _, _, .ldiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, _, .rdiv R S U V => R.fv ++ S.fv ++ U.fv ++ V.fv
  | _, _, _, .pair R S => R.fv ++ S.fv
  | _, _, _, .prod R S => R.fv ++ S.fv
  | _, _, _, .junc R S => R.fv ++ S.fv
  | _, _, _, .juncD R S => R.fv ++ S.fv
  | _, _, _, .lam R => R.fv
  | _, _, _, .E R => R.fv
  | _, _, _, .est Q => Q.fv
  | _, _, _, .thin Q => Q.fv
  | _, _, _, .own R => R.fv
  | _, _, _, .succ U => U.fv
  | _, _, _, .arith _ U => U.fv
  | _, _, _, .leq U => U.fv
  | _, _, _, .lt U => U.fv
  | _, _, _, .foldr e S | _, _, _, .fold e S => e.fv ++ S.fv
  | _, _, _, .foldI e S => e.fv ++ S.fv
  | _, _, _, .flat R => R.fv
  | _, _, _, .arg g x => g.fv ++ x.fv
  | _, _, _, .nu k S b => S.fv ++ b.fv.filter (· != k)
  | _, _, _, .mu k _ _ b => b.fv.filter (· != k)
  | _, _, _, .hylo k _ ch b => ch.fv ++ b.fv.filter (· != k)
  -- every leaf listed: a wildcard makes the equation lemmas of this 40-constructor family slow to build
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .zero | _, _, _, .id | _, _, _, .outl | _, _, _, .outr
  | _, _, _, .nil | _, _, _, .prim _ | _, _, _, .atPos _ | _, _, _, .share .. | _, _, _, .call .. => []

/-! ### Substitution -/

/-- A substitution: each entry `(k, ⟨A, B, s⟩)` puts the closed term `s : A ⟶ B` for the variable `k`, the first
    entry for `k` winning, and a variable with no entry stays. The syntax side of `Val` (`Tm.Sub.den`). -/
abbrev Tm.Sub := List (Nat × (A : Obj) × (B : Obj) × Tm A B false)

/-- `s` at demand `d`: `𝟙 s` at `true`, since no constructor lowers a demand bit. -/
def Tm.lift {A B : Obj} (s : Tm A B false) : (d : Bool) → Tm A B d
  | false => s
  | true => .comp .id s

/-- What `σ` puts for the variable `i` used at `A' ⟶ B'`: its entry's term where the objects match, `𝟘` where they
    do not, as `Val.bind` reads a variable at other objects. -/
def Tm.Sub.get (i : Nat) {A' B' : Obj} (d : Bool) : Tm.Sub → Tm A' B' d
  | [] => .var i
  | (k, ⟨A, B, s⟩) :: σ =>
    if i = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ s.lift d else Tm.zero.lift d) else Sub.get i d σ

/-- The variables free in the terms of `σ`. -/
def Tm.Sub.fvs : Tm.Sub → List Nat
  | [] => []
  | (_, ⟨_, _, s⟩) :: σ => s.fv ++ fvs σ

/-- A variable above every one of `l`. -/
def Tm.fresh (l : List Nat) : Nat := l.foldr max 0 + 1

/-- `t` with `σ` put for its free variables. A binder is renamed to a variable `fresh` for its body and `σ`, so no
    variable of `σ` is captured, whatever `σ` holds. A `share` is closed, so it is kept. -/
def Tm.subst : Tm.Sub → {A B : Obj} → {d : Bool} → Tm A B d → Tm A B d
  | σ, _, _, d, .var i => σ.get i d
  | σ, _, _, _, .top V => .top (V.subst σ)
  | σ, _, _, _, .comp R S => .comp (R.subst σ) (S.subst σ)
  | σ, _, _, _, .conv R => .conv (R.subst σ)
  | σ, _, _, _, .meet R S => .meet (R.subst σ) (S.subst σ)
  | σ, _, _, _, .join R S => .join (R.subst σ) (S.subst σ)
  | σ, _, _, _, .diff R S => .diff (R.subst σ) (S.subst σ)
  | σ, _, _, _, .dom R => .dom (R.subst σ)
  | σ, _, _, _, .ran R => .ran (R.subst σ)
  | σ, _, _, _, .ldiv R S U V => .ldiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, _, .rdiv R S U V => .rdiv (R.subst σ) (S.subst σ) (U.subst σ) (V.subst σ)
  | σ, _, _, _, .pair R S => .pair (R.subst σ) (S.subst σ)
  | σ, _, _, _, .prod R S => .prod (R.subst σ) (S.subst σ)
  | σ, _, _, _, .junc R S => .junc (R.subst σ) (S.subst σ)
  | σ, _, _, _, .juncD R S => .juncD (R.subst σ) (S.subst σ)
  | σ, _, _, _, .lam R => .lam (R.subst σ)
  | σ, _, _, _, .E R => .E (R.subst σ)
  | σ, _, _, _, .est Q => .est (Q.subst σ)
  | σ, _, _, _, .thin Q => .thin (Q.subst σ)
  | σ, _, _, _, .own R => .own (R.subst σ)
  | σ, _, _, _, .succ U => .succ (U.subst σ)
  | σ, _, _, _, .arith k U => .arith k (U.subst σ)
  | σ, _, _, _, .leq U => .leq (U.subst σ)
  | σ, _, _, _, .lt U => .lt (U.subst σ)
  | σ, _, _, _, .foldr e S => .foldr (e.subst σ) (S.subst σ)
  | σ, _, _, _, .fold e S => .fold (e.subst σ) (S.subst σ)
  | σ, _, _, _, .foldI e S => .foldI (e.subst σ) (S.subst σ)
  | σ, _, _, _, .flat R => .flat (R.subst σ)
  | σ, _, _, _, .arg g x => .arg (g.subst σ) (x.subst σ)
  | σ, A, B, _, .nu k S b =>
    .nu (fresh (b.fv ++ σ.fvs)) (S.subst σ) (b.subst ((k, ⟨A, B, .var (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | σ, A, B, _, .mu k w n b =>
    .mu (fresh (b.fv ++ σ.fvs)) w n (b.subst ((k, ⟨A, B, .var (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | σ, A, B, _, .hylo k w ch b =>
    .hylo (fresh (b.fv ++ σ.fvs)) w (ch.subst σ) (b.subst ((k, ⟨A, B, .var (fresh (b.fv ++ σ.fvs))⟩) :: σ))
  | _, _, _, _, .val R => .val R
  | _, _, _, _, .uni U => .uni U
  | _, _, _, _, .zero => .zero
  | _, _, _, _, .id => .id
  | _, _, _, _, .outl => .outl
  | _, _, _, _, .outr => .outr
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .prim r => .prim r
  | _, _, _, _, .atPos k => .atPos k
  | _, _, _, _, .share k R => .share k R
  | _, _, _, _, .call d c os cv => .call d c os cv

/-- `X`, the variable `k`, occurs in `t` only with sign `s` (`true` positive): the one monotonicity check (D5 = J),
    `den_mono`/`den_anti`. A node with no rule below must not mention `k` at all. `ldiv`'s `R` and `rdiv`'s `S`
    occur on both sides (`ldivDen`'s `∀` and its `∃`), so they must be free of `k`; `Λ`, `E`, `thin` hold an image
    whole (`lamDen`'s `↔`), so their part must be too. A row passes its argument's sign where its `prims` entry is
    `mono` (`rowDens_mono`), `F(X)` among them. -/
def Tm.pol (s : Bool) (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Bool
  | _, _, _, .var j => if j == k then s else true
  | _, _, _, .top V => V.pol s k
  | _, _, _, .comp R S => R.pol s k && S.pol s k
  | _, _, _, .conv R => R.pol s k
  | _, _, _, .meet R S => R.pol s k && S.pol s k
  | _, _, _, .join R S => R.pol s k && S.pol s k
  | _, _, _, .diff R S => R.pol s k && S.pol (!s) k
  | _, _, _, .dom R => R.pol s k
  | _, _, _, .ran R => R.pol s k
  | _, _, _, .ldiv R S U V => !R.fv.contains k && S.pol s k && U.pol s k && V.pol s k
  | _, _, _, .rdiv R S U V => R.pol s k && !S.fv.contains k && U.pol s k && V.pol s k
  | _, _, _, .pair R S => R.pol s k && S.pol s k
  | _, _, _, .prod R S => R.pol s k && S.pol s k
  | _, _, _, .junc R S => R.pol s k && S.pol s k
  | _, _, _, .juncD R S => R.pol s k && S.pol s k
  | _, _, _, .own R => R.pol s k
  | _, _, _, .nu j S b => S.pol s k && (j == k || b.pol s k)
  | _, _, _, .mu j _ _ b => j == k || b.pol s k
  | _, _, _, .hylo j _ _ b => j == k || b.pol s k
  | _, _, _, .est Q => Q.pol s k
  | _, _, _, .succ U | _, _, _, .arith _ U | _, _, _, .leq U | _, _, _, .lt U => U.pol s k
  | _, _, _, .foldr e S | _, _, _, .fold e S | _, _, _, .foldI e S => e.pol s k && S.pol s k
  | _, _, _, .flat R => R.pol s k
  | _, _, _, t@(.arg (.prim r) x) => (Prim.find? r.sym).any (·.mono) && x.pol s k || !t.fv.contains k
  | _, _, _, t@(.lam _) | _, _, _, t@(.E _) | _, _, _, t@(.thin _) | _, _, _, t@(.arg ..) => !t.fv.contains k
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .zero | _, _, _, .id | _, _, _, .outl | _, _, _, .outr
  | _, _, _, .nil | _, _, _, .prim _ | _, _, _, .atPos _ | _, _, _, .share .. | _, _, _, .call .. => true

end Rel.Lang
