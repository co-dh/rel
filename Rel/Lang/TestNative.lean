import Rel.Lang.EmitC
import Rel.Run.Lang.Embed
import Rel.Lang.GenSpec

/-! Stage 1a of the native backend (`doc/rel-native-design.md` §13): `x ≜ {…}°`, `output x to "out"`. Its plan is
    literals and `qlean_own_write` calls only: the converse is a register rename. `main` is the `relc-1a` exe:
    `c FILE` prints the plan as C, `lean DIR` writes `DIR/out` from the value Lean computed (`writeRel`), `plan DIR`
    runs the plan in `DIR` (`Plan.run`). The language has no `output` declaration yet (stage 2), so the output is
    stated here, as `planOf`'s arguments. -/

namespace Rel.Lang.TestNative

open Tab Rel.Lang Rel.Lang.Plan

rel_program native1a where
    obj X = {A,B,C}
    obj N = 0…9
    x : X ⟶ N ≜ {(1,A),(2,B),(5,C),(5,A)}°

/-- `output x to "out"`. -/
def plan : Lean.Meta.MetaM (Except String Plan) := return (← outputOf [] native1a "x" "out") >>= Bld.plan

/-! F-e: a computed relation as columns. `Alg.arith` (`arithB`) on two literal columns answers a count register
    and buffers; the output is the one-row relation of lists `gu ↦ s`: each side's `.e` a computed buffer handed to
    `parts` (`pushPart`), its `.hi` the count register as a buffer (`enlistLong`), its `.lo` the literal `[0]`. -/

/-- The literal long payload of `xs`. -/
def longs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

/-- A list side of one row: `.lo` `[0]`, `.hi` `[m]`, `.e` the `m` longs `e`. -/
def listSide (m e : Nat) : Bld Side := do
  let one ← lit (.size 1)
  return [(".lo", ← colRegs .i64 0 one #[← lit (.bytes (Rel.one 0))]),
    (".hi", ← colRegs .i64 0 one #[← call1 (kernel% Kernel.enlistLong) #[m]]), (".e", ← colRegs .i64 0 m #[e])]

/-- `arith add` of `u` and `v` (a null, an overflow, a negative operand among the rows), written to `dir`. -/
def arithOut (dir : String) : Bld Unit := do
  let n ← lit (.size 5)
  let u ← lit (.bytes (longs [5, 7, Alg.nul, Int64.maxValue, -3]))
  let v ← lit (.bytes (longs [1, 2, 3, 1, 4]))
  let rs ← arithB Kernel.Ew.add n u v
  let (some r, some gu, some s) := (rs[0]?, rs[1]?, rs[3]?) | throw "arithB answers four registers"
  output dir (← listSide r gu, ← listSide r s)

-- six columns, each one `qlean_own_write`; the kept rows are those of `arith`: `5+1`, `7+2`, `-3+4` (null and overflow out)
#eval show IO Unit from do
  let (_, ws) ← IO.ofExcept ((← IO.ofExcept (Bld.plan (arithOut "out"))).run abiOf)
  unless ws.size == 6 do throw (IO.userError s!"arithOut writes {ws.size} columns, not six")

-- a column written by `ownWrite` and mapped back by `fileMap`: element 0 the header, element 1 the bytes written
#eval show IO Unit from do
  let (h, p) ← IO.FS.createTempFile
  h.flush
  let b := longs [3, -1, Alg.nul]
  Rel.Db.ownWrite p.toString QAtomicType.i64.code.toUInt8 0 0 3 "" #[b]
  let ps ← Rel.Db.fileMap p.toString
  IO.FS.removeFile p
  unless ps.size == 2 && (ps[1]?.map (·.data)) == some b.data do
    throw (IO.userError s!"fileMap of {p}: {ps.size} elements, part 0 not the {b.size} bytes written")

/-- The native gate's plan:`plan`'s output, then the computed relation's to `out/arith`. -/
def gatePlan : Lean.Meta.MetaM (Except String Plan) :=
  return (← outputOf [] native1a "x" "out") >>= fun b => Bld.plan (do b; arithOut "out/arith")

/-- `gatePlan` run outside Lean, in the environment of the modules on `LEAN_PATH` (as `lake env` sets it), where
    the elaborator's unifier finds the objects' constants (`Obj.named`). -/
def planIO : IO Plan := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Rel.Lang.TestNative }] {}
  let (r, _) ← gatePlan.run'.toIO { fileName := "relc-1a", fileMap := default } { env }
  IO.ofExcept r

-- two columns, each six `lit`s, a path `lit` and one `qlean_own_write`; nothing else is called
#eval show Lean.Meta.MetaM Unit from do
  let p ← match ← plan with | .ok p => pure p | .error e => throwError e
  unless p.main.length == 16 && p.main.all fun | .call s _ => s == "qlean_own_write" | .fail .. => false | _ => true do
    throwError "the plan has {p.main.length} instructions, not sixteen `lit`s and `qlean_own_write` calls"

/-! Stage 1b, `Code.groupIds` (`groupIdsF`): one code per kind of lane, so every branch of its `if`s runs. -/

/-- A code's four registers, as `lit`s. -/
def codeRegs (c : Alg.Code) : Bld (Array Nat) :=
  (codeVals c).mapM lit

/-- `groupIdsF` applied to each of `cs`; `main`'s last two registers are the last code's answer. -/
def gplan (cs : List Alg.Code) : Except String Plan := Bld.plan do
  let f ← groupIdsF
  for c in cs do discard <| apply f (← codeRegs c) 2

/-- A bitmap, bytes, longs, and ids at `2` bits (`idGroups`). -/
def codes : List Alg.Code :=
  [⟨1, 10, 2, ⟨#[0b1011001, 0b10]⟩⟩, ⟨8, 5, 256, ⟨#[3, 1, 3, 2, 1]⟩⟩,
   Alg.Code.ofLongs ⟨#[5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]⟩,
   ⟨2, 4, 3, ⟨#[0b10000100]⟩⟩]

/-- `Plan.run` of `gplan [c]` answers `c.groupIds`. -/
def agrees (c : Alg.Code) : IO Bool := do
  let (rs, _) ← IO.ofExcept ((← IO.ofExcept (gplan [c])).run abiOf)
  match rs[rs.size - 2]?, rs[rs.size - 1]? with
  | some (.bytes a), some (.bytes b) => pure (a.data == c.groupIds.1.data && b.data == c.groupIds.2.data)
  | _, _ => pure false

#eval show IO Unit from do for c in codes do unless ← agrees c do throw (IO.userError s!"groupIds plan differs at w = {c.w}")

end Rel.Lang.TestNative

open Rel.Lang.Plan Rel.Lang.TestNative in
/-- The `relc-1a` exe (`lakefile.lean`): `c FILE`, `lean DIR`, `plan DIR`, as the module doc says. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["c", file] => IO.FS.writeFile file (← IO.ofExcept (relc abiOf (← planIO)))
    | ["lean", dir] =>
      unless native1a.x.ok do throw (IO.userError "x: an op ran out of capacity")
      writeRel (System.FilePath.mk dir / "out").toString native1a.x.rel
    | ["plan", dir] => IO.Process.setCurrentDir dir; discard <| (← planIO).exec abiOf
    | ["g", file] => IO.FS.writeFile file (← IO.ofExcept (gplan codes >>= relc abiOf))
    | _ => throw (IO.userError "usage: relc-1a c FILE | lean DIR | plan DIR | g FILE")
    pure 0
  catch e => IO.eprintln e; pure 1
