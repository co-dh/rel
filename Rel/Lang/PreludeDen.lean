module

public import Rel.Lang.PreludePrefix
public import Rel.Lang.PreludeSuffix
public import Rel.Lang.PreludeFilter
public import Rel.Lang.PreludeTakewhile
public import Rel.Lang.PreludeConcat
public import Rel.Lang.PreludeTails
public import Rel.Lang.PreludeStar
public import Rel.Lang.PreludeDfn
import Lean
meta import Rel.Run.Lang.Syntax

@[expose] public section

/-! Every row of `prims` that carries a `prelude` definition has a theorem `Tm.<sym>Def_den`, "the definition's
    `Tm.den` is the row's `rowDens` term" (B10b), or is listed in `unproved`. The check enumerates the rows of
    `prims`, the obligations, and not the theorems: a row with neither fails, and so does an `unproved` name that
    is no such row or already has its theorem (delete it from the list). -/

namespace Rel.Lang

/-- The rows with a `prelude` definition and no theorem `Tm.<sym>Def_den` yet. -/
-- tails: its body seeds `ran(uni ≫ nil ≫ τ)` and reads the head by `call head` over a `Tm.val` table literal
-- (`Gen.relV`); no lemma gives `Tm.den` of a generated `val`/`uni` literal, so body = `Tm.tailsDef` does not close.
-- length, sum: seed column `Gen.atom` ≠ `zeroCol` unshown (`Enc.wf?` returns some under `Enc.WF` is missing; PreludeDfn, end)
meta def unproved : List String := ["tails", "length", "sum"]

/-- The name of the theorem that row `r`'s definition means the row. -/
meta def Prim.defDenName (r : Prim) : Lean.Name := .str `Rel.Lang.Tm (r.sym ++ "Def_den")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let rows := prims.filter (·.prelude.isSome)
  let bare := rows.filter fun r => !unproved.contains r.sym && !env.contains r.defDenName
  unless bare.isEmpty do
    throwError "prelude rows with neither a theorem `Tm.<sym>Def_den` nor an entry in `unproved`: {bare.map (·.sym)}"
  let stale := unproved.filter fun s => !rows.any (·.sym == s) || env.contains (Prim.defDenName { sym := s, sig := ([], .var {} "A", .var {} "A") })
  unless stale.isEmpty do
    throwError "`unproved` names that are no prelude row or already have their theorem: {stale}"

end Rel.Lang
