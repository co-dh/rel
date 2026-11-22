import Lake
open Lake DSL

/-!
The Rel language: its concrete allegory core, its kernels (Lean model + `@[extern]` into the Rust crate `relk` in
`crate/`), its runtime and compiler, its laws and its programs. No `require`: the package depends on the toolchain
alone; freyd's bridge and qlean `require` it.

Lean rather than TOML because a TOML configuration cannot declare an `extern_lib`, and fails silently.
-/

package rel where
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]
  -- every executable and shared library carries a build-id, so a perf profile resolves against the binary it ran
  -- (cap keeps them by build-id) and not the one rebuilt since; ld.lld writes none unless asked
  moreLinkArgs := #["-Wl,--build-id"]

/-- The concrete allegory core: toolchain only, choice-free (`CLAUDE.md`). -/
lean_lib RelCore where
  globs := #[.submodules `Rel.Core]

/-- `relk.o`: the crate built by `crate/build.sh`, partial-linked with only the `qlean_*` externs global. Keyed on every
    crate source and build file, so a Rust edit reruns it and nothing else does. -/
target relk.o pkg : System.FilePath := do
  let crate := pkg.dir / "crate"
  let src ← inputDir (crate / "src") (text := true) (·.extension == some "rs")
  let cfg ← #["Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "build.sh", "RELK.txt", "RELIO.txt"].mapM
    fun (f : String) => inputTextFile (crate / f)
  let dir := pkg.buildDir / "crate"
  buildFileAfterDep (dir / "relk.o") (cfg.foldl (fun j f => j.zipWith (fun s _ => s) f) src) fun _ => do
    IO.FS.createDirAll dir
    proc { cmd := "sh", args := #[(crate / "build.sh").toString, (dir / "relk.o").toString],
           env := #[("CARGO_TARGET_DIR", (dir / "target").toString)] }

/-- `librelk.a`, the one archive both the Lean build and the native program link. -/
def relkLib (pkg : Package) : FetchM (Job System.FilePath) := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "relk") #[← relk.o.fetch]

/-- The kernels every `@[extern]` of `RelKernel` names; a precompiled module's shared library links it. -/
extern_lib relk pkg := relkLib pkg

/-- The modules under `Rel/Kernel` and `Rel/KernelSpec`, read from the directory and split into (tests, the rest). A
    test is a module whose name matches `*Test*`, as the Makefile's test gates read it. -/
def kernelModules (dir : System.FilePath) : IO (Array Lean.Name × Array Lean.Name) := do
  let files := (← (dir / "Rel" / "Kernel").walkDir) ++ (← (dir / "Rel" / "KernelSpec").walkDir)
  let mods ← (files.filter (·.extension == some "lean")).mapM (Lean.moduleNameOfFileName · (some dir))
  -- sorted: `walkDir` order varies between checkouts
  return (mods.qsort (·.toString < ·.toString)).partition fun m => (m.toString.splitOn "Test").length > 1

/-- The kernels' Lean side: each `@[extern "qlean_…"] def` is its own specification. Precompiled, so that `#eval`,
    `#guard` and the elaborator run the Rust. -/
lean_lib RelKernel where
  -- `KernelSpec` too: kernel modules import its lemmas, and a precompiled module's imports must sit in a library whose
  -- shared library it can link without a cycle. Not the tests: every precompiled module of the lib is in its shared
  -- library, which every module of `RelRun` and `Rel` traces, so a test edit would rebuild the whole package; they are
  -- in lib `Rel`
  globs := (run_io kernelModules __dir__).2.map .one
  -- no root: the default one, `RelKernel`, names no module, and Lake would load the library as that module's plugin
  roots := #[]
  precompileModules := true

/-- What `rel_program` runs at elaboration time: the expander, the code it emits and their imports. -/
lean_lib RelRun where
  -- one root named like the lib makes its shared library a plugin
  roots := #[`Rel.Run]
  libName := "rel_Rel_Run"
  globs := #[.andSubmodules `Rel.Run]
  -- a precompiled module puts every module it imports into native code, so only the run path is precompiled, and an
  -- edit to a proof rebuilds no shared library
  precompileModules := true

/-- Every top-level name under `Rel/` that none of the three libraries above owns, read from the directory, so a new
    module or directory needs no edit here. -/
def restRoots (dir : System.FilePath) : IO (Array (Lean.Name × Bool × Bool)) := do
  let own := #["Core", "Kernel", "KernelSpec", "Run"]
  let stems := (← (dir / "Rel").readDir).filterMap fun e =>
    let s : String := (e.fileName : System.FilePath).fileStem.getD e.fileName
    if own.contains s || s.startsWith "." then none else some s
  -- sorted and deduplicated: `Lang.lean` beside `Lang/` is one glob, and `readDir` order varies between checkouts
  (stems.qsort (· < ·)).toList.eraseDups.toArray.mapM fun (s : String) => do
    return (`Rel ++ Lean.Name.mkSimple s, ← (dir / "Rel" / s!"{s}.lean").pathExists, ← (dir / "Rel" / s).isDir)

/-- The laws, the language's specification, the programs and the tests (the kernels' too); interpreted. -/
@[default_target]
lean_lib Rel where
  -- a module file, a directory of modules, or both: `andSubmodules` reads the directory, so a file alone is `one`
  globs := (run_io restRoots __dir__).map (fun (m, file, dir) => (show Glob from
    if dir then (if file then .andSubmodules m else .submodules m) else .one m)) ++
    (run_io kernelModules __dir__).1.map .one

/-- `make compile-diff`: the differential test, built (so traced and replayed when its imports are unchanged) rather than
    elaborated on every run. Outside the `Rel` glob, so `lake build Rel` does not run it. -/
lean_lib RelGate where
  srcDir := "test"
  roots := #[`TestCompile]

/-- `make bench`: the programs whose instance measures size or throughput, each over what a program may cost the gate
    (`gateMs`, `test/TestCompile.lean`), in `Bench/`; building the library runs them. No gate imports it. -/
lean_lib RelBench where
  -- its own root, `Bench`: a glob over `Rel` would claim every module of lib `Rel` too
  globs := #[.submodules `Bench]

/-- `Rel.Lang.TestNative`'s `main`: prints its plan as C (`relc c FILE`) and writes the Lean side's column directory
    (`lean DIR`, `plan DIR`). -/
lean_exe relc where
  root := `Rel.Lang.TestNative
  -- `relc run` interprets a program's `io`, which calls compiled code (`Init`, the externs): the symbols exported
  supportInterpreter := true

/-- The C `relc` prints, linked with `librelk.a` and `qrt.o` and nothing of Lean's: the archive contributes the kernels
    the program calls, and `qrt.o` (`crate/build.sh rt`, from `crate/rt`) the runtime symbols those reach. -/
target «rel-native» pkg : System.FilePath := do
  let dir := pkg.buildDir / "native"
  let inc := (← getLeanIncludeDir).toString
  let relc ← relc.fetch
  -- `relc` elaborates the program, which reads the modules `lake env` puts on `LEAN_PATH` (`TestNative.planIO`)
  let env ← getAugmentedEnv
  let cJob ← relc.mapM fun exe => do
    let c := dir / "rel-native.c"
    IO.FS.createDirAll dir
    let out ← IO.Process.output { cmd := exe.toString, args := #["c", c.toString], env }
    unless out.exitCode == 0 do error s!"{exe} c {c}: exit {out.exitCode}: {out.stderr}"
    return c
  let crate := pkg.dir / "crate"
  let cargo := dir / "cargo"
  let src ← inputDir (crate / "rt" / "src") (text := true) (·.extension == some "rs")
  let cfg ← #["rt/Cargo.toml", "rt/Cargo.lock", "rust-toolchain.toml", "build.sh"].mapM
    fun (f : String) => inputTextFile (crate / f)
  let rtO ← buildFileAfterDep (cargo / "qrt.o") (cfg.foldl (fun j f => j.zipWith (fun s _ => s) f) src) fun _ =>
    proc { cmd := "sh", args := #[(crate / "build.sh").toString, "rt"], env := #[("CARGO_TARGET_DIR", cargo.toString)] }
  let mainO ← buildO (dir / "rel-native.o") cJob #["-I", inc] #["-O2"]
  let kern ← relkLib pkg
  mainO.bindM fun m => rtO.bindM fun r => kern.mapM fun k => do
    let exe := dir / "rel-native"
    proc { cmd := "cc", args := #["-o", exe.toString, m.toString, r.toString, k.toString, "-lm"] }
    return exe

/-- `make axioms` and `make externs`: enumerate the declarations of named modules. Outside the `Rel` glob, so
    `lake build Rel` neither builds nor runs it. -/
lean_exe gates where
  srcDir := "gates"
  root := `Gates
