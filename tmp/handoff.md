# foronly3 handoff (checkpoint)

Done (committed on this worktree branch): merge of 86e262e; OwnTest re-pinned to v5 and every refusal test re-aimed at
the kind-2 `good` file (352 bytes) so each still hits its own refusal; extern and body agree on every line;
`Rel.Kernel.Db.OwnTest Rel.KernelSpec.Own` build green (/data/tmp/job/foronly3-own.log). PLAN 8.3: Rust ALP internals
and syms/enum moved to 留下. Gates green: `sh crate/build.sh syms`, `cargo test --features std` (87 passed).
Running: full build, `CAP_JOB=foronly3-build` (/data/tmp/job/foronly3-build.log).
Left: full build result; `make decode-allow panic-allow bang-allow pointfree`; `lake -R lean test/TestCompile.lean`;
`make native`; fast-forward branch `foronly`.
