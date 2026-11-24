import Rel.Lang.TestNative
import Rel.Programs.Mss
import Rel.Programs.Selsort
import Rel.Programs.Quicksort
import Rel.Programs.Detab
import Rel.Programs.Edit

/-! The list programs `Mss`, `Selsort`, `Quicksort`, `Detab`, `Edit` (`Rel/Programs/`) planned: per program one
    `rel_program` opened on it with one definition per side of each table-valued `check`; the plan of each, run,
    writes the columns of the Lean value (`writesAgree`, the check the `rel-native` gate makes). A side left out
    is a plan gap, its error quoted beside the program. -/

namespace Rel.Lang.TestNativeProgL

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude Programs.mss in
rel_program natMss where
    xm : K ⟶ N ≜ x mss
    xs : K ⟶ N ≜ x scan
    xr : K ⟶ N ≜ {(a,14),(b,9),(c,0),(d,3),(e,0)}
    ash : [N] ⟶ N ≜ A shape
    afu : [N] ⟶ N ≜ A fused
    agr : [N] ⟶ N ≜ A greedy
    asc : [N] ⟶ N ≜ A scan
    ams : [N] ⟶ N ≜ A mss

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "xm" (← planOfIn ``natMss "xm") natMss.xm
  writesAgree "xs" (← planOfIn ``natMss "xs") natMss.xs
  writesAgree "xr" (← planOfIn ``natMss "xr") natMss.xr
  writesAgree "ash" (← planOfIn ``natMss "ash") natMss.ash
  writesAgree "afu" (← planOfIn ``natMss "afu") natMss.afu
  writesAgree "agr" (← planOfIn ``natMss "agr") natMss.agr
  writesAgree "asc" (← planOfIn ``natMss "asc") natMss.asc
  writesAgree "ams" (← planOfIn ``natMss "ams") natMss.ams

/- Selsort: every side of `Programs.selsort` (`x perm ordered(≤)`, `x X`, `C X`, `C perm ordered(≤)`, ...) is refused
   alike, since `outputOf` reads the whole chain (`Expand.read (fun _ => none)`) and the home's `X` fails there:
   "in the program `Rel.Programs.selsort`, line 28, col 36: the converse of `add` does not run on demand, so R° reads
   R whole: [N] has no universe; compose a set of its elements before it (§a)". Left out. -/

open Rel.Programs.prelude Programs.quicksort in
rel_program natQuick where
    Cp : [N] ⟶ [N] ≜ C perm ordered(≤)
    -- `x sort'`, `y sort'`, `z sort'`, `e sort'`, `C sort'` (the hylo `sort'`): the plan's run stops with
    -- "kscan: row 0 is null, and a null names no row"; `x split` and `x c` plan and agree.

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "Cp" (← planOfIn ``natQuick "Cp") natQuick.Cp

open Rel.Programs.prelude Programs.detab in
rel_program natDetab where
    xd : 1 ⟶ [Ch] ≜ x detab
    xde : 1 ⟶ [Ch] ≜ x detab entab
    pe : 1 ⟶ [Ch] ≜ p entab
    qe : 1 ⟶ [Ch] ≜ q entab
    ye : 1 ⟶ [Ch] ≜ y entab
    De : [Ch] ⟶ [Ch] ≜ D entab
    Ded : [Ch] ⟶ [Ch] ≜ D entab detab
    -- `p Λ(H)est(R)`, `q …`, `y …`, `D Λ(H)est(R)`: "the plan of `pH` writes 4 of 4 columns, not those of its
    -- Lean value"; `p Λ(H)` agrees, `est(R)` leaves a longer payload column `val.e` (8205 cells, the value's 6564)

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "xd" (← planOfIn ``natDetab "xd") natDetab.xd
  writesAgree "xde" (← planOfIn ``natDetab "xde") natDetab.xde
  writesAgree "pe" (← planOfIn ``natDetab "pe") natDetab.pe
  writesAgree "qe" (← planOfIn ``natDetab "qe") natDetab.qe
  writesAgree "ye" (← planOfIn ``natDetab "ye") natDetab.ye
  writesAgree "De" (← planOfIn ``natDetab "De") natDetab.De
  writesAgree "Ded" (← planOfIn ``natDetab "Ded") natDetab.Ded

open Rel.Programs.prelude Programs.edit in
rel_program natEdit where
    Dml : [A]×[A] ⟶ N ≜ D mle length 𝟙(N)
    Dsl : [A]×[A] ⟶ N ≜ spec length 𝟙(N)
    -- `D mle`, `spec`: "the plan of `Dm` writes 13 of 13 columns, not those of its Lean value": the payload columns
    -- `val.e.*` hold 52 cells where the value's hold 26

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "Dml" (← planOfIn ``natEdit "Dml") natEdit.Dml
  writesAgree "Dsl" (← planOfIn ``natEdit "Dsl") natEdit.Dsl

end Rel.Lang.TestNativeProgL
