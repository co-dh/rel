# foronly2 handoff (checkpoint)

Work list: /data/tmp/typedbase/foronly-notes.md. Merged f37e1fd; PLAN 8.3 rewritten to the final text.
Done: Run/Core.lean long/float bytes+alp lemmas deleted, `Arr.ofBytes` = `Arr.mk (Enc.ofBytes ..)`,
`toList_answer_int` -> `toList_ofBytes_int` (hc : x.enc = Enc.ofBytes 4 b).
Left: Run/Core tests l3/ta/tsum, ss/es (syms/enum), blank_WF; ValEq; KernelWF/Read; RepCanon; Gather; Expand.atomE;
KernelSpec; kernel tests; OwnTest; crate own.rs tests + scan.rs enc_dense; Rust ALP; syms/enum deletion; doc.
Build: `CAP_JOB=foronly2-build CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <wt> -R build ...`; output in
/data/tmp/job/foronly2-build.log (cap redirects there when CAP_JOB is set). lake has no -k.
