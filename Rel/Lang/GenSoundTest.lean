import Rel.Lang.GenSound
import Rel.Run.Lang.Embed
import Rel.Programs.Blocks
import Rel.Programs.Chess
import Rel.Programs.Circuit
import Rel.Programs.CSP
import Rel.Programs.Detab
import Rel.Programs.Edit
import Rel.Programs.JobShop
import Rel.Programs.Knapsack
import Rel.Programs.Mss
import Rel.Programs.Party
import Rel.Programs.Prelude
import Rel.Programs.Quicksort
import Rel.Programs.Selsort
import Rel.Programs.SudokuAC
import Rel.Programs.SudokuPC
import Rel.Programs.SudokuPC9
import Rel.Programs.Wumpus
import Rel.Programs.Frame
import Rel.Programs.FrameGroup
import Rel.Programs.FrameJoin
-- the test modules holding a `rel_program`, as `test/TestCompile.lean` imports them
import Rel.Lang.TestAsc
import Rel.Lang.TestDemand
import Rel.Lang.TestFrame
import Rel.Lang.TestFrameCols
import Rel.Lang.TestFrameGroup
import Rel.Lang.TestFrameJoin
import Rel.Lang.TestFrameNull
import Rel.Lang.TestFramePos
import Rel.Lang.TestFrameScale
import Rel.Lang.TestFrameUnbounded
import Rel.Lang.TestGenericN
import Rel.Lang.TestNative
import Rel.Lang.TestPositions
import Rel.Lang.TestSchema
import Rel.Lang.TestSum
import Rel.Lang.TestUnbounded
import Rel.Lang.TestArcs
import Rel.Lang.TestChess
import Rel.Lang.TestGroups
import Rel.Lang.EmbedTest
import Rel.Lang.ModuleTest
import Rel.Lang.Test
import Rel.Lang.TestMss
import Rel.Lang.TestWumpus
import Rel.Lang.TestSelsort
import Rel.Lang.TestKnapsack
import Rel.Lang.TestCircuit
import Rel.Lang.TestHylo
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit

/-! `Tm.gen_sound` is not vacuous: each registered program re-read (`Expand.read`, at the homes and scope the
    registry recorded), the definitions with no `Tm.gap` node counted, and four of them, of 8 to 431 nodes, required
    to be among them. -/

namespace Rel.Lang.GenSoundTest

open Lean Elab Command Rel.Lang Rel.Lang.Embed

/-- What the registered program `n` reads, re-read at its recorded homes (`.chain`) and scopes (`.prog`) and with
    the registry's definitions elaborated once (`calls`), as `rel_program` reads it: a use of one is a `call` node
    holding its body at the call's objects (`Tm.den`, `Tm.gen` read the body), a use with no constant its
    expansion. The registry is the final one, not the one `n` was elaborated under: a key registered by a later
    program is one `n` would have built itself (`walk`'s `once`), with the same body; a key registered twice is
    read at its first `Once`, the second checked to be the same definition (`Registry.call?`). -/
def reread (n : Name) : CommandElabM (Except Err Expand.Read) := do
  let env ← getEnv; let opts ← getOptions
  let reg := Expand.relRegistry.getState env
  let progs ← ((reg.chains.lookup n).getD []).mapM fun m => return (m, ← programOf m)
  let resOf (h : Name) : String → Found := match reg.progs.find? (·.1 == h) with
    | some (_, ns, os) => (resolverAt env opts reg ns os).1
    | none => fun _ => .none
  let calls ← liftTermElabM reg.call?
  liftTermElabM (Expand.read calls progs (← programOf n) n resOf).run

run_cmd do
  let reg := Expand.relRegistry.getState (← getEnv)
  -- `call?` throws unless each key registered again has its first registration's body
  let _ ← liftTermElabM reg.call?
  logInfo m!"{(reg.again.map (·.key)).toList.eraseDups.length} keys registered more than once \
    ({reg.again.size} registrations after the first), each the same definition as its first"
  -- every definition: each program's, and each one elaborated once, by its constant: the registry's (which the
  -- re-read finds, so builds no other) and any the re-read builds
  let mut defs : List (String × Res) := []
  for (n, _, _) in reg.progs do
    match ← reread n with
    | .error e => throwError "GenSoundTest: re-reading {n}: {e}"
    | .ok (ds, _, _, _, fs) =>
      defs := defs ++ ds.map (fun (x, r) => (s!"{n}.{x}", r)) ++ fs.map fun o => (toString o.const, o.res)
  for c in (reg.calls.map (·.2.const)).eraseDups do
    if let some (_, o) := reg.calls.find? (·.2.const == c) then
      unless defs.any (·.1 == toString c) do defs := defs ++ [(toString c, o.res)]
  let mut ok : List String := []
  let mut ks : List (List String) := []
  let mut nonmono : List String := []
  -- the counted terms' largest `Tm.size`, every call's body unfolded in it
  let mut big := 0
  for (x, ⟨_, _, t⟩) in defs do
    -- `monoOK` false makes `LamLaws` false (`Tm.LamLawsAt.mono`, `Tm.monoOK_iff`): `gen_sound` says nothing
    if t.gap then
      ks := t.gapKinds.eraseDups :: ks
      logInfo m!"gap in `{x}`: {t.gapKinds.eraseDups}"
    else if t.monoOK then
      ok := ok ++ [x]
      big := max big t.size
    else nonmono := nonmono ++ [x]
  logInfo m!"{ok.length} of {defs.length} definitions of {reg.progs.size} programs have no gap node and pass \
    Tm.monoOK; the largest has {big} nodes, call bodies unfolded"
  logInfo m!"{nonmono.length} with no gap node fail Tm.monoOK (a fixed point's body not positive): {nonmono}"
  -- per gap kind: the definitions it blocks, and those it blocks alone (their only gap kind)
  let rows := ks.flatten.eraseDups.map fun k => (k, (ks.filter (·.contains k)).length, (ks.filter (· == [k])).length)
  for (k, b, a) in rows.mergeSort fun (_, b, a) (_, b', a') => a > a' || (a == a' && b ≥ b') do
    logInfo m!"gap `{k}`: blocks {b}, alone {a}"
  for x in ["Rel.Programs.chess.K", "Rel.Programs.chess.N", "Rel.Programs.blocks.r", "Rel.Programs.edit.ne"] do
    unless ok.contains x do throwError "GenSoundTest: {x} has a gap node or is no definition"

/-- Two modules' registrations of the keys `j` and `k`, as `a.*` and `b.*`: each `k` calls its own module's `j`. -/
def twice (k' : Tm .long .long) : Expand.Registry :=
  let o (k c : Name) (t : Tm .long .long) : Once :=
    { key := k, const := c, gen := [], params := [], forms := [], res := ⟨_, _, t⟩, tst := false, kf := false }
  [.call `j (o `j `a.j .id), .call `k (o `k `a.k (.call [] `a.j [] .id)),
   .call `j (o `j `b.j .id), .call `k (o `k `b.k k')].foldl Expand.Registry.add {}

-- the same body but for the name of the call's constant: one definition, read at its first constant
#guard_msgs in
run_meta do
  let f ← (twice (.call [] `b.j [] .id)).call?
  unless (f `k).map (·.const) == some `a.k do throwError "not the first registered"

/-- error: rel registry: the key `k` is held by `a.k` and by `b.k`, built by two modules neither importing the other, with different bodies: at call: its fields differ -/
#guard_msgs in
run_meta discard (twice (.call [] `b.k [] .id)).call?

end Rel.Lang.GenSoundTest
