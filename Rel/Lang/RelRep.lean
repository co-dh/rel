import Rel.Run.Lang.Embed
import Rel.Lang.GenSpec

/-! `Expand.rep n`: the proof that the code of the program `n` computes its terms. `rel_program n` emits only the
    program and records each definition's numbered term with the expansion's constants (`RegEntry.rep`); this
    function reads them back and assembles `n.rep_x : (n.x).ok = true → rep (n.x).rel = ⟦x⟧` from `GenSpec`'s
    lemmas, so a program's module imports no proof; `TestRep` runs it on every program the registry lists. -/

namespace Rel.Lang

open Tab Rel.Alg

namespace Expand

open Lean Meta Elab Command

/-- The theorem of each shared constant (`n.c.c<i>.rep`), and the first combinator met with no lemma. -/
abbrev PM := StateT (Std.HashMap Name Name × Option Name) RM

/-- The lemma `n` at the proofs `hs` of its parts, each with its term's `d`, its objects inferred from them; none
    where a part has none. `Fn d A B` is `Rel A B`, so no proof's type names `d`: each part's comes from its term. -/
def lem (n : Name) (hs : List (Option (Lean.Expr × Bool))) : PM (Option Lean.Expr) := do
  let some as := hs.mapM id | return none
  let c ← mkConstWithFreshMVarLevels n
  let (xs, bs, _) ← forallMetaTelescope (← inferType c)
  let ex := (xs.zip bs).filterMap fun (x, b) => if b.isExplicit then some x else none
  unless ex.size == as.length do throwError "Expand.lem: `{n}` takes {ex.size} parts, given {as.length}"
  for (x, a, d) in ex.toList.zip as do
    -- the part `R : Fn ?d A B` that `x : Sound R T` is about: its `d` is the term's
    for r in (← inferType x).getAppArgs do
      let rt ← inferType r
      if r.isMVar && rt.isAppOfArity ``Gen.Fn 3 then
        unless ← isDefEq rt.appFn!.appFn!.appArg! (bE d) do
          throwError "Expand.lem: `{n}`: the part {a} is at d = {d}, its binder at {rt}"
    unless ← isDefEq (← inferType x) (← inferType a) do
      throwError "Expand.lem: `{n}`: the part {a} : {← inferType a} does not fit {← inferType x}"
    x.mvarId!.assign a
  let e ← instantiateMVars (mkAppN c xs)
  if e.hasExprMVar then throwError "Expand.lem: `{n}`: arguments left open in {e}"
  pure (some e)

/-- A leaf lemma `n` whose objects only the term gives. -/
def lemO (n : Name) (as : Array (Option Lean.Expr)) : PM (Option Lean.Expr) := do some <$> mkAppOptM n as

mutual

/-- A proof of `Gen.Sound (code t) T`, `T` the allegory's term; a closed `t` cites its constant's theorem. -/
partial def prf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} (t : Tm A B) :
    PM (Option Lean.Expr) := do
  if !closed t then return ← prfNode pre ρ t
  let cd ← code pre ρ t
  let c := cd.constName!
  if let some h := (← get).1[c]? then return some (mkConst h)
  let h := c ++ `rep
  -- under its number, `t`'s node: proving `.share k R` by `R`'s own `prf` would add `h` twice
  let some p ← (match t with | .share _ R => prfNode pre ρ R | t => prfNode pre ρ t) | return none
  -- `p` itself at `c`, so the kernel meets `c =?= node(t)` and unfolds `c`, never the data
  let ty := g ``Gen.Sound #[oE A, oE B, cd, (← inferType p).appArg!]
  addDecl (.thmDecl { name := h, levelParams := [], type := ty, value := p })
  modify fun (m, g) => (m.insert c h, g)
  pure (some (mkConst h))

/-- A proof of `Gen.PSound (planOr t) T`, following `planOr`. -/
partial def pprf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} (t : Tm A B) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} (u : Tm X Y) : PM (Option (Lean.Expr × Bool)) := return (← prf pre ρ u).map (·, u.dem)
  let q {X Y : Obj} (u : Tm X Y) : PM (Option (Lean.Expr × Bool)) := return (← pprf pre ρ u).map (·, u.dem)
  if closed t then return ← lem ``Gen.pleaf_sound [← p t]
  match A, B, t with
  | _, _, .val _ | _, _, .uni _ | _, _, .var _ _ => lem ``Gen.pleaf_sound [(← prfNode pre ρ t).map (·, t.dem)]
  | _, _, .share _ R | _, _, .own R => return (← q R).map (·.1)
  | _, _, .comp R S => lem ``Gen.pcomp_sound [← q R, ← q S]
  | _, _, .conv R => lem ``Gen.pconv_sound [← q R]
  | _, _, .meet R S => lem ``Gen.pmeet_sound [← q R, ← q S]
  | _, _, .join R S => lem ``Gen.pjoin_sound [← q R, ← q S]
  | _, _, .diff R S => lem ``Gen.pdiff_sound [← q R, ← q S]
  | _, _, .ldiv R S UB UC => lem ``Gen.pldiv_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _ => lem ``Gen.pleaf_sound [← p t]

/-- A proof of `Gen.Sound (node t) T`, one `GenSpec` lemma per node, following `node`. -/
partial def prfNode (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} (t : Tm A B) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} (u : Tm X Y) : PM (Option (Lean.Expr × Bool)) := return (← prf pre ρ u).map (·, u.dem)
  let q {X Y : Obj} (u : Tm X Y) : PM (Option (Lean.Expr × Bool)) := return (← pprf pre ρ u).map (·, u.dem)
  match A, B, t with
  | _, _, .val R => lem ``Gen.val_sound [some (← liftE (relE R), false)]
  | A, _, .uni (m := m) U => lemO ``Gen.uni_sound #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, .zero => lemO ``Gen.zero_sound #[oE A, oE B]
  | A, _, .id => lemO ``Gen.id_sound #[oE A]
  | A, _, .top V => match ← p V with
    | some (h, _) => lemO ``Gen.top_sound #[oE A, none, none, none, h]
    | none => pure none
  | .prod A B, _, .outl => lemO ``Gen.outl_sound #[oE A, oE B]
  | .prod A B, _, .outr => lemO ``Gen.outr_sound #[oE A, oE B]
  | _, _, .comp R S => if R.dem then lem ``Gen.comp_sound [← p R, ← p S] else lem ``Gen.compB_sound [← q R, ← q S]
  | _, _, .conv R => lem ``Gen.conv_sound [← p R]
  | _, _, .meet R S =>
    if !R.dem && !S.dem then lem ``Gen.meetB_sound [← q R, ← q S] else lem ``Gen.meet_sound [← p R, ← p S]
  | _, _, .join R S => lem ``Gen.join_sound [← p R, ← p S]
  | _, _, .diff R S =>
    if !R.dem && !S.dem then lem ``Gen.diffB_sound [← q R, ← q S] else lem ``Gen.diff_sound [← p R, ← p S]
  | _, _, .dom R => lem ``Gen.dom_sound [← p R]
  | _, _, .ran R => lem ``Gen.ran_sound [← p R]
  | _, _, .ldiv R S UB UC => lem ``Gen.ldivB_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, .rdiv R S UA UB => lem ``Gen.rdiv_sound [← p R, ← p S, ← p UA, ← p UB]
  | _, _, .pair R S => lem ``Gen.pair_sound [← p R, ← p S]
  | _, _, .prod R S => lem ``Gen.prod_sound [← p R, ← p S]
  | _, _, .junc R S => lem ``Gen.junc_sound [← p R, ← p S]
  | A, .arr B, .nil => lemO ``Gen.nil_sound #[oE A, oE B]
  | .arr B, _, .atPos k => lemO ``Gen.atPos_sound #[oE B, toExpr k]
  | _, _, .est Q => lem ``Gen.est_sound [← p Q]
  | _, _, .succ U => lem ``Gen.succ_sound [← p U]
  | _, _, .leq U => lem ``Gen.leq_sound [← p U]
  | _, _, .lt U => lem ``Gen.lt_sound [← p U]
  | _, _, .arith k U => match ← p U with
    | some (h, _) => lemO ``Gen.arith_sound #[toExpr k, none, none, h]
    | none => pure none
  | _, _, .foldr e S => lem ``Gen.foldr_sound [← p e, ← p S]
  | _, _, .fold e S => lem ``Gen.fold_sound [← p e, ← p S]
  | _, _, .own R | _, _, .share _ R => return (← p R).map (·.1)
  | _, _, _ => match primOf t with
    -- a row's spine is proved by `compile_sound` (`Prim.run_sound`) over `compile`'s code, not this node's: its
    -- constant is the gap until stage 4 cites that
    | some (r, _) => modify (fun (m, g) => (m, g <|> some r.sig.1)); pure none
    | none =>
      -- a call is named by its constant, not by the `Gen.ofPl` that runs its plan
      let e ← node pre ρ t
      let f := (if e.isAppOf ``Gen.ofPl then e.appArg! else e).getAppFn.constName?
      modify fun (m, g) => (m, g <|> f); pure none

end

/-- The theorems `n.rep_x` of the program `n`, from the terms and constants `emit` recorded, and `n.unproved`:
    the definitions with none, each with the first combinator `GenSpec` has no lemma for. -/
def rep (n : Name) : MetaM Unit := do
  let some (ds, shared, codes) := (relRegistry.getState (← getEnv)).reps[n]?
    | throwError "Expand.rep: `{n}` is no rel_program"
  -- `emit`'s constants by value and by number, so `code` finds each one and adds none
  let st : Std.HashMap Lean.Expr Name × Std.HashMap Nat Lean.Expr := (.ofList shared.toList, .ofList codes.toList)
  let kern := ((← getEnv).find? (n ++ `kernel)).bind (·.value?) == some (toExpr true)
  let unproved ← (do
    let mut gaps : List (String × String) := []
    for (x, ⟨_, _, t⟩) in ds do
      -- a program on the kernel path runs `GenK`, which `GenSpec` has no lemma for yet
      if kern then gaps := gaps ++ [(x, "GenK")]; continue
      let kc := mkConst (Parse.constOf n x)
      modify fun (m, _) => (m, none)
      let body : PM (Option String) := do
        match ← prf n [] t with
        | some p =>
          let ty ← mkArrow (← mkEq (← mkAppM ``CRel.ok #[kc]) (toExpr true))
            (← mkEq (← mkAppM ``Rel.Rep.rep #[← mkAppM ``CRel.rel #[kc]]) (← inferType p).appArg!)
          let pv ← mkAppM ``Gen.Sound.run_eq #[p]
          addDecl (.thmDecl { name := n ++ Name.mkSimple s!"rep_{x}", levelParams := [], type := ty, value := pv })
          pure none
        | none => pure (((← get).2.map toString).getD "?")
      -- a fresh heartbeat count per theorem, since the command has spent its own
      if let some c ← withCurrHeartbeats body then gaps := gaps ++ [(x, c)]
    pure gaps : PM (List (String × String))).run' ({}, none) |>.run false |>.run' st
  let sty := pairT (mkConst ``String) (mkConst ``String)
  addConst (n ++ `unproved) (listT sty) (← mkListLit sty (unproved.map fun (x, c) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``String) (toExpr x) (toExpr c)))

end Expand

end Rel.Lang
