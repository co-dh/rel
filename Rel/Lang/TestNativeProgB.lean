import Rel.Lang.TestNative
import Rel.Programs.SudokuAC
import Rel.Programs.SudokuPC
import Rel.Programs.Chess

/-! The native plans of the fixpoint programs `SudokuAC`, `SudokuPC`: each table-valued side of each `check`, opened
    from the program, is planned (`planOfIn`) and its plan's writes are those of the Lean value (`writesAgree`). They
    reach `μ`/`ν`/`hylo` (`tabB`) and the selection of `≫` and `\`: the plan takes the row path (`ldivSelB` over rows),
    which lists the same rows as the bit-matrix `Rel.bits` (`Tab.compBits_eq`, `Tab.ldivBits_eq`). `agree` logs the
    times.

    `Chess` (3×3, `natChess.mm`) is planned too: a closed definition is one global (`shareB`), so its plan holds each
    definition once, not a copy at every use. -/

namespace Rel.Lang.TestNativeProgB

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude Rel.Programs.csp Rel.Programs.sudokuac in
rel_program natAC where
    gv : Cell ⟶ D ≜ g
    sv : Cell ⟶ D ≜ s
    fp : Cell ⟶ D ≜ s₀ ∩ (peer\(s ≠))
    solv : Cell ⟶ D ≜ sol

open Rel.Programs.prelude Rel.Programs.csp Rel.Programs.sudokupc in
rel_program natPC where
    sv : Cell ⟶ D ≜ s
    sp : Cell ⟶ D ≜ s'

open Rel.Programs.prelude Rel.Programs.chess in
rel_program natChess where
    mm : Sq×Sq ⟶ Pc ≜ m

/-- `writesAgree` of the definition `x` of the program `m`, with its own heartbeat budget and its time printed. -/
def agree {A B : Obj} (m : Lean.Name) (x : String) (v : Except String (Tab A B)) : Lean.Meta.MetaM Unit := do
  let t ← IO.monoMsNow
  Lean.withCurrHeartbeats do
    let p ← planOfIn m x
    let t1 ← IO.monoMsNow
    writesAgree x p v
    Lean.logInfo m!"{m}.{x}: plan {t1 - t} ms, run {(← IO.monoMsNow) - t1} ms"

#eval show Lean.Meta.MetaM Unit from do
  agree ``natAC "gv" natAC.gv
  agree ``natAC "sv" natAC.sv
  agree ``natAC "fp" natAC.fp
  agree ``natAC "solv" natAC.solv
  agree ``natPC "sv" natPC.sv
  agree ``natPC "sp" natPC.sp
  agree ``natChess "mm" natChess.mm

end Rel.Lang.TestNativeProgB
