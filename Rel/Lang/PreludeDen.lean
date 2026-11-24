module

public import Rel.Lang.PreludePrefix
public import Rel.Lang.PreludeSuffix
public import Rel.Lang.PreludeFilter
public import Rel.Lang.PreludeTakewhile
public import Rel.Lang.PreludeConcat
public import Rel.Lang.PreludeTails
public import Rel.Lang.PreludeSetify
public import Rel.Lang.PreludeTau
public import Rel.Lang.PreludeInits
public import Rel.Lang.PreludeLoop
public import Rel.Lang.PreludeStar
public import Rel.Lang.PreludeDfn
public import Rel.Lang.PreludeOrd
public import Rel.Lang.PreludeThinL
public import Rel.Lang.PreludePositions
public import Rel.Lang.PreludeMerge
public import Rel.Lang.PreludeCat
public import Rel.Lang.PreludeSnoc
import Lean
meta import Rel.Run.Lang.Syntax

@[expose] public section

/-! Every row of `prims` that carries a `prelude` definition has a theorem `Tm.<sym>Def_den`, "the definition's
    `Tm.den` is the row's `rowDens` term" (B10b), or is listed in `unproved`. The check enumerates the rows of
    `prims`, the obligations, and not the theorems: a row with neither fails, and so does an `unproved` name that
    is no such row or already has its theorem (delete it from the list). The theorem's type must also mention the
    row's body constant `<prelude>.body`, so a theorem of the right name about another term fails. -/

namespace Rel.Lang

/-- The rows with a `prelude` definition and no theorem `Tm.<sym>Def_den` yet. -/
meta def unproved : List String := []

/-- The name of the theorem that row `r`'s definition means the row. -/
meta def Prim.defDenName (r : Prim) : Lean.Name := .str `Rel.Lang.Tm (r.sym ++ "Def_den")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let rows := prims.filter (·.prelude.isSome)
  let bare := rows.filter fun r => !unproved.contains r.sym && !env.contains r.defDenName
  unless bare.isEmpty do
    throwError "prelude rows with neither a theorem `Tm.<sym>Def_den` nor an entry in `unproved`: {bare.map (·.sym)}"
  -- A theorem of that name that never mentions the row's body is about something else: the type must use `<prelude>.body`.
  let off := rows.filterMap fun r => do
    let ci ← env.find? r.defDenName
    let body := (← r.prelude).str "body"
    if ci.type.getUsedConstants.contains body then none else some s!"{r.sym}: `{r.defDenName}` does not mention `{body}`"
  unless off.isEmpty do
    throwError "prelude rows whose theorem `Tm.<sym>Def_den` is not about the row's body: {off}"
  let stale := unproved.filter fun s => !rows.any (·.sym == s) || env.contains (Prim.defDenName { sym := s, sig := ([], .var {} "A", .var {} "A") })
  unless stale.isEmpty do
    throwError "`unproved` names that are no prelude row or already have their theorem: {stale}"

end Rel.Lang
