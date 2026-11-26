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

open Rel.Programs.prelude Programs.selsort in
rel_program natSel where
    xo : 1 ⟶ [N] ≜ x perm ordered(≤)
    yo : 1 ⟶ [N] ≜ y perm ordered(≤)
    zo : 1 ⟶ [N] ≜ z perm ordered(≤)
    eo : 1 ⟶ [N] ≜ e perm ordered(≤)
    xX : 1 ⟶ [N] ≜ x X
    yX : 1 ⟶ [N] ≜ y X
    zX : 1 ⟶ [N] ≜ z X
    eX : 1 ⟶ [N] ≜ e X
    CX : [N] ⟶ [N] ≜ C X
    Co : [N] ⟶ [N] ≜ C perm ordered(≤)

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "xo" (← planOfIn ``natSel "xo") natSel.xo
  writesAgree "yo" (← planOfIn ``natSel "yo") natSel.yo
  writesAgree "zo" (← planOfIn ``natSel "zo") natSel.zo
  writesAgree "eo" (← planOfIn ``natSel "eo") natSel.eo
  writesAgree "xX" (← planOfIn ``natSel "xX") natSel.xX
  writesAgree "yX" (← planOfIn ``natSel "yX") natSel.yX
  writesAgree "zX" (← planOfIn ``natSel "zX") natSel.zX
  writesAgree "eX" (← planOfIn ``natSel "eX") natSel.eX
  writesAgree "CX" (← planOfIn ``natSel "CX") natSel.CX
  writesAgree "Co" (← planOfIn ``natSel "Co") natSel.Co

open Rel.Programs.prelude Programs.quicksort in
rel_program natQuick where
    Cp : [N] ⟶ [N] ≜ C perm ordered(≤)
    ec : 1 ⟶ 1+(([N]×N)×[N]) ≜ e c
    xc : 1 ⟶ 1+(([N]×N)×[N]) ≜ x c
    xs : 1 ⟶ [N] ≜ x sort'
    ys : 1 ⟶ [N] ≜ y sort'
    zs : 1 ⟶ [N] ≜ z sort'
    es : 1 ⟶ [N] ≜ e sort'
    Cs : [N] ⟶ [N] ≜ C sort'

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "Cp" (← planOfIn ``natQuick "Cp") natQuick.Cp
  writesAgree "ec" (← planOfIn ``natQuick "ec") natQuick.ec
  writesAgree "xc" (← planOfIn ``natQuick "xc") natQuick.xc
  writesAgree "xs" (← planOfIn ``natQuick "xs") natQuick.xs
  writesAgree "ys" (← planOfIn ``natQuick "ys") natQuick.ys
  writesAgree "zs" (← planOfIn ``natQuick "zs") natQuick.zs
  writesAgree "es" (← planOfIn ``natQuick "es") natQuick.es
  writesAgree "Cs" (← planOfIn ``natQuick "Cs") natQuick.Cs

open Rel.Programs.prelude Programs.detab in
rel_program natDetab where
    xd : 1 ⟶ [Ch] ≜ x detab
    xde : 1 ⟶ [Ch] ≜ x detab entab
    pe : 1 ⟶ [Ch] ≜ p entab
    qe : 1 ⟶ [Ch] ≜ q entab
    ye : 1 ⟶ [Ch] ≜ y entab
    De : [Ch] ⟶ [Ch] ≜ D entab
    Ded : [Ch] ⟶ [Ch] ≜ D entab detab
    pLe : 1 ⟶ [Ch] ≜ p ((𝟙÷∋)E(H))est(R)
    qLe : 1 ⟶ [Ch] ≜ q ((𝟙÷∋)E(H))est(R)
    yLe : 1 ⟶ [Ch] ≜ y ((𝟙÷∋)E(H))est(R)
    DLe : [Ch] ⟶ [Ch] ≜ D ((𝟙÷∋)E(H))est(R)

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "xd" (← planOfIn ``natDetab "xd") natDetab.xd
  writesAgree "xde" (← planOfIn ``natDetab "xde") natDetab.xde
  writesAgree "pe" (← planOfIn ``natDetab "pe") natDetab.pe
  writesAgree "qe" (← planOfIn ``natDetab "qe") natDetab.qe
  writesAgree "ye" (← planOfIn ``natDetab "ye") natDetab.ye
  writesAgree "De" (← planOfIn ``natDetab "De") natDetab.De
  writesAgree "Ded" (← planOfIn ``natDetab "Ded") natDetab.Ded

#eval show Lean.Meta.MetaM Unit from do writesAgree "pLe" (← planOfIn ``natDetab "pLe") natDetab.pLe
#eval show Lean.Meta.MetaM Unit from do writesAgree "qLe" (← planOfIn ``natDetab "qLe") natDetab.qLe
#eval show Lean.Meta.MetaM Unit from do writesAgree "yLe" (← planOfIn ``natDetab "yLe") natDetab.yLe
#eval show Lean.Meta.MetaM Unit from do writesAgree "DLe" (← planOfIn ``natDetab "DLe") natDetab.DLe

open Rel.Programs.prelude Programs.edit in
rel_program natEdit where
    Dml : [A]×[A] ⟶ N ≜ D mle length 𝟙(N)
    Dsl : [A]×[A] ⟶ N ≜ spec length 𝟙(N)
    Dm : [A]×[A] ⟶ [A+(A+A)] ≜ D mle
    Sp : [A]×[A] ⟶ [A+(A+A)] ≜ spec

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "Dml" (← planOfIn ``natEdit "Dml") natEdit.Dml
  writesAgree "Dsl" (← planOfIn ``natEdit "Dsl") natEdit.Dsl

#eval show Lean.Meta.MetaM Unit from do writesAgree "Dm" (← planOfIn ``natEdit "Dm") natEdit.Dm
#eval show Lean.Meta.MetaM Unit from do writesAgree "Sp" (← planOfIn ``natEdit "Sp") natEdit.Sp

end Rel.Lang.TestNativeProgL
