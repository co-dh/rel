nullband3g6 handoff

DONE, green (`lake build Rel.Run.Cols Rel.Run.SetOps Rel.Run.Bits Rel.Run.Comp Rel.Run.Div Rel.Run.List`):
 - Run/Cols.lean: `Opt.concat n x y` = ONE `kscan .first false t t n none [(n₁, x.enc), (n₂, y.enc)]` (guards: `n₁+n₂ = n`,
   `foROk` of both sources, `t.width`), `Arr.concat n x y` = `Opt.concat` of `Opt.ofArr`s read back as an `Arr`
   (`hasNul` test; never fails by `streamEnc_plain`), `catRows n₁ n₂ : Except String USize` replaces `catPlan`,
   `foROk_valid`, `streamEnc_plain`. `Vals.concat`/`Vals.catSummand` lost `off`; `cat : (m) → Vals → Vals → …`.
 - Run/SetOps `Tab.concat`/`Tab.tagged`, Run/Bits `colCat`/`Vals.code2`, Run/Comp, Run/Div, Run/List use `catRows`;
   `tagged`, `colCat`, `code2` still build `off` with `shiftCol n₂ n₁.toUInt64` where they gather/scatter through it.
   `shiftCol` is kept: `Arr.pos`, `Tab.index`, `Tab.ldivTabMat` use it (not only concat).
 - RepChecks/Cols.lean: `concatKeeps` on `catRows`; new `concatNulKeeps` `#guard`s (nulls first only, second only, both,
   neither, and sizes 1024/1023+1025/5+2048) -- written, NOT yet built.

RED / NOT DONE (Rel/RepCols.lean, then RepSetOps, then RepBits/RepTabDiv/RepWF/RepTabComp/RepStruct/GenKBits sites):
 - Delete `shiftCol_raw` no: still used by `Arr.pos_get`; keep. Delete `catPlan_ok`, `Arr.concat_get`, `Opt.concat_get`;
   `catRows_ok : catRows n₁ n₂ = .ok n → n.toNat = n₁.toNat + n₂.toNat` replaces `catPlan_ok` (the `off` half
   moves to `tagged_ok`/`colCat_raw`/`code2_spec` via `shiftCol_raw`).
 - Read law plan (Valid of both sources comes from the `foROk` guard of `Opt.concat`, of `z` from `wordsFoR_nul`):
   `Opt.get_eq_of_raw z src (hx: Valid z) (hy: Valid src) (S+k) k hf h` with
     hf: `foRNuls_wordsFoR` + `bitAt_stream` + `joined_get` (`kscan_stream_get`'s `e1`) + `foRNuls_bit`;
     h: `raw_wordsFoR_of_bit` gives `a = cutBit t (raw t src)[k]`; then `atomOfBits_mod` (t ≠ u1, `raw_foR` at `t`
        and `.i64`, w = 8) or `atom_of_cut` (u1); `pos` source: `raw t = raw .i64`.
   Opt law: `Opt.get (concat x y) c = if c < n₁ then x.get c else y.get (c − n₁)` via `es = [(n₁,x),(n₂,y)]`,
   j = 0/1, `es.take 1` sums to `n₁`. Arr law from it by `Opt.get_ofArr`.
 - `Arr.concat_valid`: sources `Valid` from the `foROk` guard (unfold `Opt.concat`, `split`), via `foROk_valid`.
 - `Vals.concat_wf`, `Vals.concat_row`, `Vals.catSummand_wf/_row`, `Tab.concat_wf` (RepSetOps), `tagged_ok`: drop `off`/`hoff`
   from every signature, `hn` from `catRows_ok`; `cat : (m) → Vals → Vals → …` in `hcat`.
 - Not run: `lake build Rel.RepCols Rel.RepSetOps Rel.Lang.TestFrameApp` (line 149 untested), `Rel.RepChecks.Cols` guards.
