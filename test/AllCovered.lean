import Rel.Lang.AllPrograms

/-! Gate `allcov`: `Rel.Lang.AllPrograms` imports every module of `Rel/` that defines a `rel_program`. Every module of
    the `Rel` library on disk (found by walking `Rel/`) that `AllPrograms` does not import has its olean read, and one
    whose registry extension (`Expand.relRegistry`) holds an entry defines a program and is an error.
    It runs after the full build and outside the library: a library module that read its siblings' oleans depended on
    files lake did not know it reads, so it failed whenever lake had not built one of them yet. -/

open Lean Elab Command

/-- The modules `.lean` files under `Rel/` name, as Lean's own path API reads them. -/
def Rel.Lang.AllPrograms.diskModules : IO (Array Name) := do
  let root ← IO.currentDir
  let files ← try System.FilePath.walkDir (root / "Rel") catch e =>
    throw <| IO.userError s!"allcov: cannot list {root / "Rel"} (run `lake` from the package root): {e}"
  (files.filter (·.extension == some "lean")).mapM (moduleNameOfFileName · (some root))

run_cmd do
  let env ← getEnv
  let imported : Std.HashSet Name := env.header.moduleNames.foldl (·.insert ·) {}
  let mut missing : Array Name := #[]
  for m in ← Rel.Lang.AllPrograms.diskModules do
    unless imported.contains m do
      let o ← match ← (findOLean m).toBaseIO with
        | .ok o => pure o
        | .error e => throwError "allcov: {m} is in Rel/ but has no olean ({e}); run `make build` first (this gate reads the whole built library)"
      let (md, region) ← (readModuleData o)
      if (md.entries.find? (·.1 == Rel.Lang.Expand.relRegistry.name)).any (·.2.size > 0) then missing := missing.push m
      region.free
  unless missing.isEmpty do
    throwError "allcov: {missing.size} module(s) of Rel/ define a `rel_program` but Rel/Lang/AllPrograms.lean does not \
      import them, so the gates built on that list never visit them; add `import <module>` there for each: \
      {missing.qsort Name.lt}"
  logInfo m!"allcov: every module of Rel/ that defines a rel_program is imported by Rel.Lang.AllPrograms"
