import Rel.Lang.EmitC
import Rel.Run.Lang.Embed

/-! Stage 1a of the native backend (`doc/rel-native-design.md` §13): `x ≜ {…}°`, `output x to "out"`. Its plan is
    literals, the converse's `canon` (`kasc`, `kseen`, `kgather`) and `qlean_own_write` calls. `main` is the `relc-1a` exe:
    `c FILE` prints the plan as C, `lean DIR` writes `DIR/out` from the value Lean computed (`writeRel`), `plan DIR`
    runs the plan in `DIR` (`Plan.run`). The language has no `output` declaration yet (stage 2), so the output is
    stated here, as `planOf`'s arguments. -/

namespace Rel.Lang.TestNative

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel

rel_program native1a where
    obj X = {A,B,C}
    obj N = 0…9
    x : X ⟶ N ≜ {(1,A),(2,B),(5,C),(5,A)}°
    u : N ⟶ X ≜ {(1,A),(2,B)} ∪ {(5,C),(2,B)}
    i : N ⟶ X ≜ {(1,A),(2,B)} ∩ {(5,C),(2,B)}
    d : N ⟶ X ≜ {(1,A),(2,B)} − {(5,C),(2,B)}
    z : X ⟶ N ≜ 𝟘
    m : X ⟶ X ≜ x x°
    dm : X ⟶ X ≜ dom(x)
    rn : N ⟶ N ≜ ran(x)
    pr : X ⟶ N × N ≜ ⟨x, x⟩
    c : X × N ⟶ N × X ≜ x × x°
    o : X × N ⟶ X ≜ (x × x°) π₂
    l : X × N ⟶ N ≜ (x × x°) π₁
    e : X ⟶ X ≜ x x° 𝟙
    tp : X ⟶ X ≜ x ⊤

/-- `output x to "out"`. -/
def plan : Lean.Meta.MetaM (Except String Plan) := return (← outputOf [] native1a "x" "out") >>= Bld.plan

/-! F-e: a computed relation as columns. `arithB` on two literal columns answers a count register and `Enc`
    registers; the output is the one-row relation of lists `gu ↦ s`: each side's `.e` a computed column handed over
    encoded (`encRegs`), its `.hi` the one-row column of the count (`constB`), its `.lo` the literal `[0]`. -/

/-- The literal `i64` column of `xs`, encoded as the kernels encode their answers (`wordsFoR`). -/
def longs (xs : List Int64) : Enc := wordsFoR (xs.map Int64.toUInt64).toArray

/-- A list side of one row: `.lo` `[0]`, `.hi` `[m]`, `.e` the `m` rows of the column `e`. -/
def listSide (m e : Nat) : Bld Side := do
  let one ← lit (.size 1)
  return [(".lo", ← encRegs .i64 one (← lit (Reg.put (longs [0])))),
    (".hi", ← encRegs .i64 one (← constB one (← call1 (kernel% USize.toUInt64) #[m]))), (".e", ← encRegs .i64 m e)]

/-- `arith add`'s operands: a null, an overflow, a negative operand among the rows. -/
def arithIn : Bld (Array Nat) := do
  let n ← lit (.size 5)
  arithB .add n (← lit (Reg.put (longs [5, 7, Alg.nul, Int64.maxValue, -3]))) (← lit (Reg.put (longs [1, 2, 3, 1, 4])))

/-- `arithIn`'s relation, written to `dir`. -/
def arithOut (dir : String) : Bld Unit := do
  let rs ← arithIn
  output dir (← listSide (← nth rs 0 "arithB") (← nth rs 1 "arithB"), ← listSide (← nth rs 0 "arithB") (← nth rs 3 "arithB"))

-- six columns, each one `qlean_own_write`
#eval show IO Unit from do
  let (_, ws) ← IO.ofExcept ((← IO.ofExcept (Bld.plan (arithOut "out"))).run abiOf)
  unless ws.size == 6 do throw (IO.userError s!"arithOut writes {ws.size} columns, not six")

-- the kept rows are those of `arith`: `5+1`, `7+2`, `-3+4` (the null and the overflow out); decoded here, in the test
#eval show IO Unit from do
  let (rs, is, _, fs, gs) ← IO.ofExcept (arithIn.run (#[], 0, #[], #[]))
  let (vs, _) ← IO.ofExcept (({ funs := fs, globals := gs, main := is.toList } : Plan).run abiOf)
  let col (i : Nat) : List UInt64 := match rs[i]?.bind (vs[·]?) |>.bind (Reg.get? (α := Enc)) with
    | some e => (Ext.Enc.raw .i64 3 e).toList | none => []
  unless (rs[0]?.bind (vs[·]?) |>.bind (Reg.get? (α := USize))) == some 3 do throw (IO.userError "arithB keeps not 3 rows")
  unless col 1 == [5, 7, (-3 : Int64).toUInt64] && col 3 == [6, 9, 1] do
    throw (IO.userError s!"arithB keeps u = {col 1}, s = {col 3}")

/-! Group ids (`groupIdsB`, design §4 group-by `kasc ≫ kseen`), as a plan function, so a function's C is printed. -/

/-- The plan function of `groupIdsB` on its parameters: the type's byte, the row count, the column. -/
def gfun : Bld Nat := defFun #[.u8, .size, .obj] fun ps => do
  pure #[← groupIdsB (← nth ps 0 "gfun") (← nth ps 1 "gfun") (← nth ps 2 "gfun")]

/-- Columns of each type a key reads, with their group ids: ties, a boolean, no row. -/
def codes : List (QAtomicType × Nat × Enc × List UInt64) :=
  [(.i64, 5, longs [3, 1, 3, 2, 1], [2, 0, 2, 1, 0]), (.u1, 4, wordsFoR #[1, 0, 1, 1], [1, 0, 1, 1]),
   (.i64, 0, longs [], [])]

/-- `gfun` applied to `c`: its ids register. -/
def gapply (c : QAtomicType × Nat × Enc × List UInt64) (f : Nat) : Bld Nat := do
  nth (← apply f #[← lit (Reg.put c.1), ← lit (.size c.2.1.toUSize), ← lit (Reg.put c.2.2.1)] 1) 0 "gfun"

/-- `gfun` applied to each of `cs`; `main`'s last register is the last column's ids. -/
def gplan (cs : List (QAtomicType × Nat × Enc × List UInt64)) : Except String Plan := Bld.plan do
  let f ← gfun
  for c in cs do discard <| gapply c f

/-- `Plan.run` of `gplan [c]` answers `c`'s ids. -/
def agrees (c : QAtomicType × Nat × Enc × List UInt64) : IO Bool := do
  let (rs, _) ← IO.ofExcept ((← IO.ofExcept (gplan [c])).run abiOf)
  pure <| (rs.back?.bind (Reg.get? (α := Enc))).any fun g => (Ext.Enc.raw .i64 c.2.1.toUSize g).toList == c.2.2.2

#eval show IO Unit from do for c in codes do unless ← agrees c do throw (IO.userError s!"group ids differ at {repr c.1}")

/-- The ids of `codes`' first column, written to `dir/key`. -/
def gidOut (dir : String) : Bld Unit := do
  let some c := codes.head? | throw "codes is empty"
  output dir ([("", ← encRegs .i64 (← lit (.size c.2.1.toUSize)) (← gapply c (← gfun)))], [])

/-! IO step I10: a program's `input`s read and its `output`s written by the plan as `n.io` reads and writes them. The
    native gate runs `nativeIO.io` (`relc run`) beside the native executable on `test/native/in` (a CSV file and a
    table directory) and compares `out/io` byte for byte. -/

rel_program nativeIO where
    obj N
    schema Row = {px : N, qty : N}
    input t : N ⟶ Row from csv "in/t.csv"
    -- the own-format files `output t to "out/io/t"` writes, kept as test/native/in/t
    input s : N ⟶ Row from "in/t"
    cp : N ⟶ Row ≜ t
    un : N ⟶ Row ≜ t ∪ t
    cm : N ⟶ N ≜ t t°
    output t to "out/io/t"
    output t to csv "out/io/t.csv"
    output cp to csv "out/io/cp.csv"
    output s to "out/io/s"
    output un to "out/io/un"
    output cm to "out/io/cm"

/-- `R`'s Lean value written to `dir` (`writeRel`), its error the program's. -/
def semOut {A B : Obj} (R : Except String (Tab A B)) (dir : String) : IO Unit := do writeRel dir (← IO.ofExcept R)

/-- The closed definitions of `native1a`, one per `Tm` node the plan builds (`tabB`), each written to `out/NAME`:
    by `relc lean` from its Lean value and by the gate's plan from its term, the one list both sides read. -/
def semOuts : List (String × (String → IO Unit)) :=
  [("x", semOut native1a.x), ("u", semOut native1a.u), ("i", semOut native1a.i), ("d", semOut native1a.d),
   ("z", semOut native1a.z), ("m", semOut native1a.m), ("dm", semOut native1a.dm), ("rn", semOut native1a.rn),
   ("pr", semOut native1a.pr), ("c", semOut native1a.c), ("o", semOut native1a.o), ("l", semOut native1a.l),
   ("e", semOut native1a.e), ("tp", semOut native1a.tp)]

/-- The native gate's plan: `nativeIO`'s IO statements (its input edge first), each of `semOuts` to `out/NAME`, then
    the computed relation's to `out/arith` and the group ids to `out/gid`. -/
def gatePlan : Lean.Meta.MetaM (Except String Plan) := do
  let bs ← semOuts.mapM fun (x, _) => outputOf [] native1a x ("out/" ++ x)
  let io ← ioOf [] nativeIO
  return do
    let (bs, (rd, wr)) := (← bs.mapM id, ← io)
    Bld.planIO rd fun ins => do
      wr ins
      for b in bs do b
      arithOut "out/arith"; gidOut "out/gid"

/-- `gatePlan` run outside Lean, in the environment of the modules on `LEAN_PATH` (as `lake env` sets it), where
    the elaborator's unifier finds the objects' constants (`Obj.named`). -/
def planIO : IO Plan := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Rel.Lang.TestNative }] {}
  let (r, _) ← gatePlan.run'.toIO { fileName := "relc-1a", fileMap := default } { env }
  IO.ofExcept r

-- the plan's writes are those of the Lean value `native1a.x` (`Tab.conv`: swapped, then `canon`), column for column:
-- each written `OwnFile` equal to the one `Db.ownFile` makes of the value's column
#eval show Lean.Meta.MetaM Unit from do
  let p ← match ← plan with | .ok p => pure p | .error e => throwError e
  let (_, ws) ← match p.run abiOf with | .ok r => pure r | .error e => throwError e
  let x ← match native1a.x with | .ok x => pure x | .error e => throwError e
  let side (s : String) (cs : List (String × QValue)) := cs.map fun (p, v) => ("out/" ++ s ++ p, v)
  let want ← match (side "key" (cols _ x.key "") ++ side "val" (cols _ x.val "")).filterMapM
      (fun (p, v) => do pure ((← ownFile p v).map fun f => (p, f))) with | .ok w => pure w | .error e => throwError e
  let got := ws.toList.filterMap fun (_, vs) => match vs.toList with
    | .str p :: c :: a :: k :: n :: d :: ps :: _ => (p, ·) <$> Reg.get? (α := Db.OwnFile) (.ctor 0 #[d, ps] #[c, a, k, n])
    | _ => none
  let flat (pf : String × Db.OwnFile) :=
    (pf.1, pf.2.code, pf.2.attr, pf.2.kind, pf.2.count.toNat, pf.2.domain, pf.2.parts.toList.map (·.toList))
  unless got.length == ws.size && got.map flat == want.map flat do
    throwError "the plan of `x` writes {got.length} of {ws.size} columns, not those of its Lean value"

/-- `NAME.io` (IO design B) of the program `NAME` elaborated in the module `MOD`, both read by Lean's name parser,
    run in the environment of the modules on `LEAN_PATH` (as `planIO`); its error is the program's. -/
unsafe def runIOImpl (mod name : String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := mod.toName }] {}
  (← IO.ofExcept (env.evalConst (IO Unit) {} (name.toName ++ `io)))

@[implemented_by runIOImpl] opaque runIO (mod name : String) : IO Unit

end Rel.Lang.TestNative

open Rel.Lang.Plan Rel.Lang.TestNative in
/-- The `relc-1a` exe (`lakefile.lean`): `c FILE`, `lean DIR`, `plan DIR`, as the module doc says; `run MOD NAME`
    runs the reads, computations and writes of the program `NAME` (`runIO`). -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["run", mod, name] => runIO mod name
    | ["c", file] => IO.FS.writeFile file (← IO.ofExcept (relc abiOf (← planIO)))
    | ["lean", dir] => for (x, w) in semOuts do w (System.FilePath.mk dir / "out" / x).toString
    | ["plan", dir] => IO.Process.setCurrentDir dir; discard <| (← planIO).exec abiOf
    | ["g", file] => IO.FS.writeFile file (← IO.ofExcept (gplan codes >>= relc abiOf))
    | _ => throw (IO.userError "usage: relc-1a c FILE | lean DIR | plan DIR | g FILE | run MOD NAME")
    pure 0
  catch e => IO.eprintln e; pure 1
