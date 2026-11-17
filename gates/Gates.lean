import Lean
open Lean

/-!
The two gates that need Lean's environment (`make axioms`, `make externs`); `gates/` is outside the `Rel` glob, so
`lake build Rel` never builds or runs this. Each gate enumerates the declarations of the named modules, the obligations,
not a table of records.
-/

/-- The axioms `Rel.Core` may rest on (`CLAUDE.md`: the core is constructive, so it holds in every allegory). -/
def allowed : List Name := [`propext, `Quot.sound]

/-- Every constant of the imported environment whose defining module is one of `mods`, internal ones included. -/
def declsOf (env : Environment) (mods : Array Name) : Array Name :=
  env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if mods.contains env.header.moduleNames[i]! then acc.push n else acc
    | none => acc

def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (((CollectAxioms.collect n).run env).run {}).2.axioms

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
    | _ => throw (IO.userError s!"gates: unknown command {cmd} (axioms | externs)")
  | [] => throw (IO.userError "usage: gates axioms|externs MODULE...")
