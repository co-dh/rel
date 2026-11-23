# 8.2 dense sum: handoff

Design (done in code): `Vals (.sum a b) n` (non-band) = `Arr .u1 n × Vals a n × Vals b n`, `SumV.gen h tag x y`,
`Vals.ofGen h tag x y`; row i = `if tag i then inr (row y i) else inl (row x i)`; filler of the unowned side is
`Vals.zeros` (= `Obj.dflt` rows; band sum filler = `Opt.nuls`). `Vals.WF` sum clause: `WF x ∧ WF y ∧
(∀ i, tag i = false → row y i = b.dflt) ∧ (∀ i, tag i = true → row x i = a.dflt)`.

## Green (built)
Rel.Run.{Core,Gather,Cols,Canon,List,Struct,Table}, Rel.Run.Lang.{Plan,Expand,Gen}, Rel.RepCanon, Rel.RepOrder,
Rel.RepCols (concat_wf moved after concat_row), Rel.RepChecks.Canon (`sumTab ts`, `sumOn` removed).

## Open (not built / not ported)
- Rel/RepStruct.lean: `Vals.none_wf` (now `Vals.zeros A n`, needs `zeros_wf` + `row (zeros) i = A.dflt`, case by case),
  `injCols_ok` (now `tagCol`; every tag `s`), inl/inr WF + holds (lines ~173, 182, 500-525), inlConv/inrConv
  (now `whereCol` of tag / negated tag, gather X and the summand, `canon`; lines ~532, 606).
- Not yet built after the change: Rel/RepWF.lean (116, 129, 218), Rel/RepTabDiv.lean (621, 630),
  Rel/Lang/GenKBits.lean (1352, 1416), Rel/Lang/GenSound (via GenK), tests TestTable/TestIO/TestNullband and any
  `sumOn` user; every `rcases s.view with ... | ⟨hb, l, r, tag, idx, x, y⟩` becomes `⟨hb, tag, x, y⟩`.
- `Vals.cellsOk` sum gen case is `false` (a literal dense sum is refused): the WF filler clause is not decided
  for literals; `readVals`/`encVals` (Table.lean) read tag/l/r with equal counts but do NOT check the filler.
  Decision needed: check the filler on read (kernel-side, per block) or normalise on read by masking.
- Unused now, delete when no caller: `Arr.clampShift`, `Vals.catSide`, `Vals.catSummand`, `summandPos`, `tagCount`,
  `Vals.summandCols`, `clampFin`, `Vals.gather_clamp`, `Vals.summand_row`, `Vals.summandCols_ok`, `lastCount`/`colPrefix`
  users (if only these used them). PLAN.md 8.2 not updated; own-file part names are now `.tag/.l/.r` (no `.idx`).
- `inlConv`/`inrConv` use one `canon` (sort) of the selected rows, not zero sorts: `idU X` dedups arbitrary X.
