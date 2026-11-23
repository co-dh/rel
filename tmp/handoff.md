nullband3g8 handoff (WIP, GenKBits not yet green)

Done in Rel/Lang/GenKBits.lean: `(by lockstep)` added to every colMap_plain/closed at the listed lines; `kscan_post_ok`/`kscan_ok`
restated on `(c :: cs).map (n, ·)` with new hyps `hpl : ∀ x ∈ c :: cs, hasNul x = false` and `hst : kscanStream … = false`
(kscan now runs `noNul` on every non-stream source); `colMap_ok` takes `ha hb` (plain) + trailing `ho : op ≠ .first`;
`whereCol_ok` takes `hbN : hasNul b = false` (after `sb`); `Tab.ofBits_ok` takes `hoN : hasNul o = false` (after `hos`);
hf generalised to any op/xs (also proves the null-flag fold of kscan, `hnl`).

Left: callers of `Tab.ofBits_ok` / `whereCol_ok` in later modules need the new plainness hyps; remaining errors from
`lake build Rel.Lang.GenKBits` (see /data/tmp/nb3g8b.log style); modules after GenKBits not reached; then the temporary
`#eval`s of the failing guards (Kern9 87/89 ... TestFrameApp 101) for the report.
