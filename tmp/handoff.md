perf11d handoff (checkpoint at 40 calls; base cd3523e + merge of perf11c 2e9cc10)

Done (not yet built): Bits colIota, keepBits (3), compTabMat, ldivTabMat (on, vac, p1) moved to post steps in
Rel/Run/Bits.lean; GenKBits proofs edited: colIota_raw, colMap_lt_const (now stated over `colMap .first n e e
.i64 .i64 [] [(.gt, N)]`, no colConst hyp), keepBits_law, compTabMat_law/wf, ldivTabMat_spec (vac, on, erm).
Still to check: ldivTabMat_reads (~1580) bind count; build Rel.Lang.GenKBits.

Left: SetOps sumTail/sumsOn, List.sumOn (Rel/RepSums.lean, badWord_spec RepTabDiv ~1074); item 3 inspection;
gate; kernel counts (/data/tmp/perf11b/count.sh, before = /data/tmp/perf11b/after.tsv).
Sandbox note: every Bash call needs dangerouslyDisableSandbox (sandbox arg list too long).
