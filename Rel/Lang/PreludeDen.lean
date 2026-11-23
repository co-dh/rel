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
-- tails, length, sum: each body reads the literal `0` as `Gen.atom .i64 1 <hex> ""`. `Gen.atom_eq` (DfnLaw) turns it
-- into `wordsFoR #[0]` given `Enc.foR (unhex <hex>) (unhex "") = wordsFoR #[0]`, which a `module` cannot evaluate:
-- `String.toUTF8` of a literal and `Std.Range.forIn'` are not exposed (a non-module file closes it by `rfl`).
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
