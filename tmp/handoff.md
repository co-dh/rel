# MRG-2 handoff: `Tab.mergeDiff_holds` is NOT yet proved

Green and committed in Rel/RepMerge.lean (`lake build +Rel.RepMerge` passes, no sorry):
- `Vals.cmpRows_spec` gained a 5th conjunct: `c = 0 → e = 0 → A.lt (T.row i) (P.row i)` (rows trichotomy);
  `Vals.rank_spec` gained a 4th: `r[i] ≤ j → h[i] = 0 → A.lt (T.row i) (X.row j)` (a miss is below every row from the cut on).
- `Vals.cmpRows_plain`, `Vals.rank_plain`: `hasNul r = false ∧ hasNul h = false` (needed by `kgather_word`; not an `i`-indexed fact).
- `Vals.rank_cut`: `r[i] ≤ n ∧ ∀ j, A.lt (X.row j) (T.row i) ↔ j < r[i]`.
- `Tab.canon_lt`: `R.canon = .ok U`, `R.WF` => U strictly ascending in `(Obj.prod k v).lt` on rows.
- `cntLe d t i` (= #{j<d | t j ≤ i}), `cntLe_mono/_le/_lt`, `le_cntLe`, `mpos n d t q` (X row i -> i + cntLe, U row j -> j + t j),
  `mpos_inj` (into [0,n+d), injective), `surj_of_inj` (pigeonhole), `merge_sorted` (abstract: rows placed by `mpos` are ascending
  given xr<ur iff i < t j; surjectivity inside).

Left: the kernel-word part of `Tab.mergeDiff_holds`. `tmp/mg_skel.lean` unfolds `mergeDiff` correctly (18 binds, state printed by
`trace_state`; check with `env LEAN_PATH=<wt>/.lake/build/lib/lean lean tmp/mg_skel.lean`). Hypotheses names: hTc hrk hnm hwh hgk hgv hrD
hposD hones hcnt hkg hc hposX hN hix1 hix2 hcc hVv; `(r,hh).snd` etc. need `dsimp only at *`.
Statement to prove (hs uses `X.key.row i`, `X.val.row i`):
`(∀ a b, V.Holds a b ↔ X.Holds a b ∨ T.Holds a b) ∧ (∀ a b, U.Holds a b ↔ T.Holds a b ∧ ¬X.Holds a b) ∧ V.WF ∧ U.WF ∧ V asc ∧ U asc`.

Plan (each step names its lemma):
1. Tc: `Tab.canon_wf`, `Tab.canon_holds`, `Tab.canon_lt`; `Vals.rank_spec/rank_cut/rank_plain` on `(X.key,X.val)`, `(Tc.key,Tc.val)`.
2. `hnm`: `colMap_raw hnm (hF := Or.inr (nulFree₂ hNh hNh))`, `Op.eval .not _ x = x ^^^ 1`, `bit01` (h<2): `nm[i] ≠ 0 ↔ hh[i] = 0`.
3. `hwh`: `whereCol_spec` (list = filter, Pairwise < gives `selN` strictly mono), `whereCol_mem` (sel hits exactly the nm≠0 rows), `whereCol_size`.
   U row j = Tc row (selN j): `ValsB.gather_row`; WF: `Vals.gather_wf`.
4. `tt j := (raw rD)[j].toNat = r[selN j]`: `kgather_word hrD hNr`. `posD[j] = tt j + j`: `colArr_ok`, `colMap_raw`, `raw_pos_word`.
5. `cnt`: `kscatter_words hcnt (kscatter_plain hones rfl)` + `scatterWords_fold (f := (· + ·))` + `colConst_raw hones`:
   `cnt[g] = (countP (tt j = g) (range d)).toUInt64`. `kg[G] = cnt[G]`: `kgather_word` + `raw_pos_word`.
   `c[i] = (cntLe d tt i).toUInt64`: `colPrefix_add_sum` with `wN g = countP (tt j = g)` and
   `Σ_{g<i+1} countP (tt j = g) (range d) = countP (tt j ≤ i)` (induction on i, `List.countP_cons` per element).
   `posX[i] = cntLe + i`.
6. `ix1[p] = mpos n d tt p` (p<N=n+d): `Arr.concat_get`/`ColB.concat_get`, `Arr.get_i64`; `ix2`: `raw_scatter N ix1.enc .pos N 0 ix2 rfl hix2`,
   `mpos_inj` (injective) gives `ix2[mpos q] = q`; `surj_of_inj` gives every g<N is some `mpos q`.
7. V row (mpos q) = cc row q = if q<n then X row q else U row (q-n): `ValsB.gather_row`, `Vals.concat_row`, `Vals.concat_wf`.
8. Conclusions: Holds by the two directions (hit: `h=1 ↔ ∃ j, X.row j = Tc.row s`; miss: `h=0`, s in sel); V sorted by
   `merge_sorted` (hxu from `rank_cut`, hux from `rank_spec` 4th conjunct, hus from `canon_lt` + selN mono, tt mono from
   `canon_lt` + `rank_cut`... tt j = r[selN j] is monotone since selN is and `A.lt (X.row i) (Tc s)` is monotone in s by `canon_lt` transitivity).
   U sorted: selN mono + `canon_lt`.
After it: add `Tab.mergeDiff_holds` doc line in doc/rel-architecture.zh.typ ~line 629 (remove "待证", say 已证), recompile PDF,
build `Rel.RepMerge Rel.MergeTest`, commit "MRG-2: Tab.mergeDiff_holds".
Note: `hasNul`-free `Op` facts: `Op.eval .add a x = .ok (a + x)`, `.last _ x = .ok x`; `lockstep`/`nulfree` autoparams may need explicit `hF`.
