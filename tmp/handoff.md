# nullband2 handoff (branch nullband2, base 52f6cd8 + merge of nullband 339f9b0)

Done
- `Obj.one` constructor (Rel/Run/Core.lean): `El = Unit`, `dflt = ()`, `Vals .one n = Unit`, `Vals.row = ()`,
  `rowsImpl = Array.replicate n ()`.
- `Obj.key .one () = []` and `Obj.key_prefix` case (Rel/ObjOrder.lean): `inr ()` keys `[1]`, after every `inl`, so
  null sorts last.

Open design point found (step 1)
- `encVals` (Rel/Run/Table.lean:157) reads a side's count from its first column part; `.one` stores no column, so the
  count of a `.one` side has no source. Inside a sum the count `r` of a `.one` summand is irrelevant to `Vals.row`
  (`Obj.one.dflt = ()`), but a top-level `.one` side (a relation `A ⟶ 1` written to an own file) needs it.
  Candidate: a `.one` side writes one part of count `n` and no bytes.

Elaborator switch (not started)
- `obj 1 = {∗}` (Rel/Programs/Prelude.lean:6) is an `ObjDef.elems` of one word; `objInfo` (Rel/Run/Lang/Expand.lean:26)
  stores every elems object at `.long`. Rule: an elems object of ONE element is stored at `.one`.
- Then: `uniOf` `.base` (Elab.lean ~317) returns `⟨.long, …⟩` from `ObjInfo.uni : Arr .i64`; `litCol` leaf
  (Elab.lean ~1776) builds a long column of codes; `showEl`/`cmpEl` (Expand.lean ~68-95); `csvLeaves` match
  (Expand.lean ~571) `.sum (.atom a) (.atom _)` -> `.sum (.atom a) .one`; TestIO csvNullIO readback type
  `.sum .long (.atom .u8)` -> `.sum .long .one`, `Sum.inr 0` -> `Sum.inr ()`.

Left: steps 2-5 of the brief (in-band `atom + one` layout, nullable foR writer, kernels, decode-allow).
