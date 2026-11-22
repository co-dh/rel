# nullband2 handoff (branch nullband2, base 52f6cd8 + `merge --no-ff 339f9b0` nullband)

Done (commits on nullband2)
- `Obj.one` (Rel/Run/Core.lean): `El = Unit`, `dflt = ()`, `Vals .one n = Unit`, `row`, `rowsImpl`.
- `.one` cases: `Obj.key` = `[]` and `key_prefix` (ObjOrder.lean; `inr ()` keys `[1]`, null last), `Vals.gather`,
  `Vals.concat`, `Vals.none`, `Vals.cols` (no column), `Vals.pack`, `Obj.ascBad`, `Tab.sums` refusals, `Plan.cols`,
  `readVals`/`encVals` (no file/part; count 0, a sum reads every position of `1` as `()`), `Obj.atoms`, `Obj.inst`,
  `valsE`, `valsEq`, `showEl` (the element's name).
- Elaborator: `objInfo` `.elems ws` with one element stores at `.one` (Expand.lean:26), `seg := false`; `uniOf` `.base`
  at `.one` gives `⟨1, ()⟩` (Elab.lean ~317); `litCol` leaf at a `.one` object gives `()` after `code` checks each word.
- CSV nullable column 4 parts -> 3 (null payload dropped; the right side is `1`): `CsvShape.parts/atoms`, `layout`,
  `fieldAt` (tag 1 reads `[]` whatever the position), Table `toCsv`/`triples`/`ofCsv` at `.sum a .one`,
  `csvLeaves` match `.sum (.atom a) .one`; csv.rs `nparts`, `counts`, `fill` (arm `(SH_NULL, 3)` removed), `at`
  (tag 1 Ok). TestIO csvNullIO expects `.sum .long .one`, `Sum.inr ()`.
- doc §0 `Obj` block + K card line; PLAN P8 line.

Failing (build3, /data/tmp/job/nullband2-build3.log)
- Rel/Kernel/Db/CsvTest.lean test data still has 4 parts per null column: lines 146-158 (`writeCases`: v1 cases with
  `#[..]` 4th array; 152 "position 0 past the 0 values of its right side" case is now Ok -> delete or change to Ok),
  163 (`[#[], #[], #[], #[]]` -> 3), 217-225 (`readCases`: `vsParts`, 219 has 7 empty arrays -> 6), `vsParts`,
  `vsParts'` (~line 370-384, `poke ... 6` index shifts by one), the error text "stored as 7" -> 6 at 147.
  Errors: `CsvTest.lean:167:2 decide proved that the proposition ... false`, `228:105`, `448:0 csvWrite [v, s] of 2500
  rows: the extern writes 5079648 bytes, the body writes 15460 bytes`.
- Downstream of CsvTest not yet compiled: rest of Rel/Run/Lang (Elab 20 sum matches, TmGen, Syntax), Rel/Rep*,
  Rel/Lang/GenKBits, GenSoundTest, RepCanon, RepTabDiv, RepCols, RepOrder (each `induction`/match on `Obj` needs a
  `.one` case).

Left: steps 2-5 of the brief (`Vals (.sum (.atom t) .one)` = one `Arr t n` in band; nullable foR writer; kernels on
the flag; decode-allow shrink); CSV then goes 3 parts -> 1.
