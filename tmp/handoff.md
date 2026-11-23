# B10cd-asc-gen handoff

Green: Rel.Lang.DfnLaw, PreludeDfn, PreludeOrd (new generic `Tm.ascDef_den`, `Tm.leDef_den`), PreludeDen,
Test.Orders, TestAsc, Test.Prelude (they built before lake stopped on TestCmpMeet; re-run to confirm).
Doc row `asc(P)` of doc/tm-minimal-design.zh.typ updated, PDF recompiled.

Red: Rel/Lang/TestCmpMeet.lean:46 `#guard cmpMeet3.failures ...` — `count(ran(R0 ∩ ≥))` on `obj M = 0…99999`
now expands cross products ("a product of 1001 × 100000 values (Vals.cross) expanded to 100100000 rows").
Cause: Elab.lean `build` `.prim` case now builds a row's text at a placeholder (`if us.any … phVar … then return ←
build δ q`), so the prelude constants `≥`, `le` (and any generic constant reading `<`/`≤`) are built generic over
their object with the `lt` text inside; a call at a number object instantiates the text (`Tm.instObj`) instead of
the fused row cut to the meet (`GenK.cmpRel`). Before, `once` fell back to `.long` and the call ran the row.

Open design choice (needs a decision, not a patch):
A. `Tm.instObj` (or `callTm`) rewrites `Tm.cmpDef c U`, `c` the prelude `lt`/`le` text, to the row
   `Tm.lt U`/`Tm.leq U` where the object becomes an integer-stored atom; theorem: `Tm.cmpDef_lt_den` + `Tm.ltDef_den`.
B. `once` keeps two forms of a constant (number-object row form and generic text form) and `callTm` picks by the
   call's object.
C. Make only `asc`'s body generic (rejected by the brief: not general).
