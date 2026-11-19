import Lean
open Lean Meta

/-!
The gates that need Lean's environment (`make axioms`, `externs`, `bang`, `pointfree`): the index records which
constants a declaration mentions, but not the code the elaborator moved into its auxiliaries (`f._unsafe_rec` of a
`partial def`, reached through `@[implemented_by]`), nor what a type unfolds to. `gates/` is outside the `Rel` glob, so
`lake build Rel` never builds or runs this. Each gate enumerates the declarations of the named modules, the obligations,
not a table of records.
-/

/-- The axioms `Rel.Core` may rest on (`CLAUDE.md`: the core is constructive, so it holds in every allegory). -/
def allowed : List Name := [`propext, `Quot.sound]

/-- Every constant of the imported environment whose defining module is one of `mods`, internal ones included. -/
def declsOf (env : Environment) (mods : Array Name) : Array Name :=
  -- `moduleNames` maps the header's module array on every call: read once, not once per constant
  let names := env.header.moduleNames
  env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if mods.contains names[i]! then acc.push n else acc
    | none => acc

def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (((CollectAxioms.collect n).run env).run {}).2.axioms

/-- A declaration someone wrote, not one the elaborator derived from it (`f.match_1`, `f._unary`, `f.eq_1`, `T.rec`). -/
def written (env : Environment) (n : Name) : Bool :=
  !n.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n && !Meta.isMatcherCore env n

/-- The constants `n`'s code mentions: its value's, and those of the declarations it owns (`n.match_1`, `n._unary`,
    `n._unsafe_rec`: the elaborator moves parts of a body there) or runs instead (`@[implemented_by]`). -/
partial def bodyConsts (env : Environment) (n : Name) : NameSet :=
  go {} n
where
  go (s : NameSet) (c : Name) : NameSet :=
    let impl := Compiler.getImplementedBy? env c
    let ds := ((env.find? c).bind (·.value? (allowOpaque := true))).map (·.getUsedConstants) |>.getD #[]
    (ds ++ impl.toArray).foldl (init := s) fun s d =>
      if s.contains d then s else if n.isPrefixOf d || impl == some d then go (s.insert d) d else s.insert d

/-- Lean's naming convention: a name ending in `!` is the variant that panics where its `?` sibling returns `none`
    (`a[i]!` is `GetElem?.getElem!`, `Option.get!`, `List.head!`, `Expr.appFn!`). The panicking accessors are the
    constants so named that are declared outside the checked modules, i.e. in core or Lean. -/
def panicking (inMods : Name → Bool) : Name → Bool
  | n@(.str _ s) => s.endsWith "!" && !inMods n
  | _ => false

/-- The repo's relation types. `Core.Rel α β` is the arrow of `Rel(Set)`, the only one: `Den` and `RowDen` are reducible
    abbreviations that reach it, so they need no entry; `Tab`/`CRel` are executable tables, not predicates. A predicate
    or invariant of two arguments is written `… → Prop`, never as one of these, so it is not a relation here. -/
def relTypes : List Name := [`Rel.Core.Rel]

/-- Whether the result of type `t` (after its `∀`s), unfolding reducible abbreviations only and never a `relTypes`
    head itself, is a relation type or a type built from one (`List ((c : RowCode) × RowDen c)`). -/
partial def relational (t : Expr) : MetaM Bool := withReducible do
  let t ← whnfCore t
  if t.isForall then return ← forallTelescope t fun _ b => relational b
  if t.getAppFn.constName?.any relTypes.contains then return true
  if let some u ← unfoldDefinition? t then return ← relational u
  t.getAppArgs.anyM fun a => lambdaTelescope a fun _ e => do if ← isType e then relational e else pure false

def runMeta (env : Environment) (x : MetaM α) : IO α :=
  Prod.fst <$> (x.run' {}).toIO { fileName := "<gates>", fileMap := default } { env }

def main : List String → IO UInt32
  | cmd :: mods => do
    initSearchPath (← findSysroot)
    let mods := mods.toArray.map String.toName
    if mods.isEmpty then throw (IO.userError s!"gates {cmd}: no module given")
    let env ← importModules (mods.map ({ module := · })) {} 0
    let ds := (declsOf env mods).qsort Name.lt
    -- zero declarations means the module list is wrong, which must not read as a pass
    if ds.isEmpty then throw (IO.userError s!"gates {cmd}: no declaration in {mods}")
    match cmd with
    | "axioms" =>
      let bad := ds.filterMap fun n =>
        let ax := (axiomsOf env n).filter (!allowed.contains ·)
        if ax.isEmpty then none else some (n, ax)
      for (n, ax) in bad do IO.println s!"{n}: {ax.toList}"
      IO.eprintln s!"gates axioms: {ds.size} declarations of {mods.size} modules, {bad.size} outside {allowed}"
      return if bad.isEmpty then 0 else 1
    | "externs" =>
      -- `sym<TAB>decl`, sorted by sym: `make externs` joins it against `nm` of `librelk.a`
      let es := ds.filterMap fun n => (getExternNameFor env `c n).map (·, n)
      for (s, n) in es.qsort (·.1 < ·.1) do IO.println s!"{s}\t{n}"
      IO.eprintln s!"gates externs: {es.size} @[extern] declarations among {ds.size} of {mods.size} modules"
      return 0
    | "bang" =>
      -- every written def or opaque whose code reaches a panicking accessor; theorems only state facts about one
      let idx := env.header.moduleNames.zipIdx.filterMap fun (m, i) => if mods.contains m then some i else none
      let inMods n := (env.getModuleIdxFor? n).any (idx.contains ·.toNat)
      let bad := ds.filter fun n => written env n && match env.find? n with
        | some (.defnInfo _) | some (.opaqueInfo _) => (bodyConsts env n).any (panicking inMods)
        | _ => false
      for n in bad do IO.println n
      IO.eprintln s!"gates bang: {bad.size} of {ds.size} declarations of {mods.size} modules reach a `!` accessor"
      return 0
    | "pointfree" =>
      -- every written def whose type is a relation and whose code mentions `Exists`
      let cand := ds.filter fun n => written env n && match env.find? n with
        | some (.defnInfo _) => (bodyConsts env n).contains ``Exists
        | _ => false
      let bad ← cand.filterM fun n => runMeta env do relational (← getConstInfo n).type
      for n in bad do IO.println n
      IO.eprintln s!"gates pointfree: {bad.size} relation-valued of {cand.size} defs with ∃ among {ds.size} declarations"
      return 0
    | _ => throw (IO.userError s!"gates: unknown command {cmd} (axioms | externs | bang | pointfree)")
  | [] => throw (IO.userError "usage: gates axioms|externs|bang|pointfree MODULE...")
