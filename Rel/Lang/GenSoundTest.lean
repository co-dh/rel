import Rel.Lang.GenSound
import Rel.Run.Lang.Embed
import Rel.Lang.AllPrograms
import Rel.ObjOrder

/-! `Tm.gen_sound` is not vacuous: each registered program re-read (`Expand.read`, at the homes and scope the
    registry recorded), the definitions whose code has no error table (`Tm.hasCode`) counted, and four of them, of 8
    to 431 nodes, required to be among them. -/

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
    | .ok (ds, _, _, _, fs, _) =>
      defs := defs ++ ds.map (fun (x, r) => (s!"{n}.{x}", r)) ++ fs.map fun o => (toString o.const, o.res)
  for c in (reg.calls.map (·.2.const)).eraseDups do
    if let some (_, o) := reg.calls.find? (·.2.const == c) then
      unless defs.any (·.1 == toString c) do defs := defs ++ [(toString c, o.res)]
  let mut ok : List String := []
  let mut noCode : List String := []
  let mut nonmono : List String := []
  -- the counted terms' largest `Tm.size`, every call's body unfolded in it
  let mut big := 0
  for (x, ⟨_, _, t⟩) in defs do
    -- an error table represents every meaning, and `monoOK` false makes `LamLaws` false (`Tm.LamLawsAt.mono`,
    -- `Tm.monoOK_iff`): in either case `gen_sound` says nothing about a run
    if !t.hasCode then noCode := noCode ++ [x]
    else if t.monoOK then
      ok := ok ++ [x]
      big := max big t.size
    else nonmono := nonmono ++ [x]
  logInfo m!"{ok.length} of {defs.length} definitions of {reg.progs.size} programs have code at every node and pass \
    Tm.monoOK; the largest has {big} nodes, call bodies unfolded"
  logInfo m!"{noCode.length} have an error table at some node (Tm.hasCode): {noCode}"
  logInfo m!"{nonmono.length} with code fail Tm.monoOK (a fixed point's body not positive): {nonmono}"
  for x in ["Rel.Programs.chess.K", "Rel.Programs.chess.N", "Rel.Programs.blocks.r", "Rel.Programs.edit.ne"] do
    unless ok.contains x do throwError "GenSoundTest: {x} has an error table, fails Tm.monoOK, or is no definition"

/-- Whether `Obj.key` reads `A`'s elements as values: every atom but `general`, which keys as `[]` (all tie). A
    float's key merges NaNs and `±0`, as q's equality does. -/
def keyed : Obj → Bool
  | .atom t => t != .general
  | .prod a b | .sum a b => keyed a && keyed b
  | .arr b => keyed b

/-- `R`'s rows as a set of values: each row `Obj.key` of the pair (the order code q's `asc` sorts by, independent
    of row order and of the storage encoding), sorted, each once. -/
def rowsOf {A B : Obj} (R : Tab A B) : List (List Nat) :=
  ((R.toList.map fun (x, y) => (Obj.prod A B).key (x, y)).mergeSort fun a b => !decide (b < a)).eraseReps

/-! `Expand.tmE` round-trips: of the definitions with code and a keyed ok table, the smallest holding a constant, the
    smallest holding a fold and the smallest calling a generic definition (a call at objects), each rebuilt from its
    `Expr` is its term (`Tm.diffAt`) and runs (`Tm.code`) to the rows of the constant `rel_program` generated
    (`n.expanded`). -/
run_cmd do
  let reg := Expand.relRegistry.getState (← getEnv)
  let mut cands : Array (Nat × String × Res × Gen.Gv) := #[]
  for (n, _, _) in reg.progs do
    let gs ← unsafe IO.ofExcept ((← getEnv).evalConst (List (String × Gen.Gv)) (← getOptions) (n ++ `expanded))
    let (ds, _, _, _, _, _) ← match ← reread n with
      | .ok r => pure r
      | .error e => throwError "GenSoundTest: re-reading {n}: {e}"
    for (x, v@⟨A, B, c⟩) in gs do
      if let some r@⟨_, _, t⟩ := ds.lookup x then
        if t.hasCode && keyed A && keyed B && c matches .ok _ then cands := cands.push (t.size, s!"{n}.{x}", r, v)
  -- a constant whose payload `valsE` cannot rebuild (symbol, general, ALP) is counted, not sampled
  let (built, refused) := (cands.qsort (·.1 < ·.1)).toList.partitionMap fun (k, nm, r, v) =>
    match Expand.tmE #[] r.2.2 with | .ok e => .inl (k, nm, r, v, e) | .error m => .inr s!"`{nm}`: {m}"
  logInfo m!"Expand.tmE rebuilds {built.length} of {cands.size} definitions; refuses {refused.length}: {refused.take 3}"
  let has (p : Lean.Expr → Bool) (e : Lean.Expr) := (e.find? p).isSome
  let objs (i : Nat) (x : Lean.Expr) := x.getAppArgs[i]?.any fun o => !o.isAppOf ``List.nil
  let wants : List (String × (Lean.Expr → Bool)) :=
    [("a constant", has fun x => x.isAppOf ``Tm.val || x.isAppOf ``Tm.uni),
     ("a fold", has fun x => x.isAppOf ``Tm.fold || x.isAppOf ``Tm.foldr || x.isAppOf ``Tm.foldI),
     ("a call to a generic definition", has fun x =>
       (x.isAppOfArity ``Tm.call 6 && objs 4 x) || (x.isAppOfArity ``Tm.callCv 8 && objs 5 x))]
  for (what, p) in wants do
    let some (k, nm, ⟨A, B, t⟩, ⟨A', B', c⟩, e) := built.find? (p ·.2.2.2.2)
      | throwError "GenSoundTest: no definition with code and a keyed ok table holds {what}"
    unless A == A' && B == B' do throwError "GenSoundTest: `{nm}` is re-read at other objects than it is generated at"
    let t' ← liftTermElabM do unsafe Meta.evalExpr (Tm A B) (Expand.g ``Tm #[Expand.oE A, Expand.oE B]) e
    if let some d := Expand.Tm.diffAt id toString [] ⟨A, B, t⟩ ⟨A, B, t'⟩ then
      throwError "GenSoundTest: `{nm}` rebuilt from `Expand.tmE` is not its term: {d}"
    match c, (Tm.code Code.empty t').runE {} with
    | .ok T, .ok T' => unless rowsOf T == rowsOf T' do
        throwError "GenSoundTest: `{nm}` rebuilt runs to other rows than its generated constant"
    | _, .error m => throwError "GenSoundTest: `{nm}` rebuilt fails: {m}"
    | .error m, _ => throwError "GenSoundTest: `{nm}`'s generated constant fails: {m}"
    logInfo m!"{what}: `{nm}`, {k} nodes, round-trips"

/-- Two modules' registrations of the keys `j` and `k`, as `a.*` and `b.*`: each `k` calls its own module's `j`. -/
def twice (k' : Tm .long .long) : Expand.Registry :=
  let o (k c : Name) (t : Tm .long .long) : Once :=
    { key := k, const := c, gen := [], ph := [], params := [], forms := [], res := ⟨_, _, t⟩, tst := false, kf := false }
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

/-- The placeholders of a constant built where an object `F` is stored at `.f64` (no form declares one yet), and
    twelve call objects for its variables. -/
def phF : List Rel.QAtomicType := placeholdersOf [("F", { ty := .base "F", obj := .atom .f64 })]
def σ12 : List Obj := List.replicate 12 (.arr .long)

-- `F`'s atom is none of the constant's placeholders: `F` passes through `Obj.inst` unchanged, where the global
-- `varAtoms` took it for variable 6; each placeholder is its variable's object, and `.long` stays
#guard !phF.contains .f64 ∧ phF.length = 11
#guard (Obj.prod (.atom .f64) .long).inst phF σ12 == .prod (.atom .f64) .long
#guard (Obj.atom .f64).inst varAtoms σ12 == .arr .long
#guard phF.all fun t => (Obj.atom t).inst phF σ12 == .arr .long

end Rel.Lang.GenSoundTest
