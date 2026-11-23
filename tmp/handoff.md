# 8.4b handoff (branch worktree-agent-a7a5914d98588afe1, head 03c4b3a, base 7ed706e)

## Done
- 7a29a88 step 1: `QValue.marking` deleted (no user). RelRun green. PLAN 8.4 line notes it.
- 7504b85 + 03c4b3a step 3 (own format v7), partly:
  - Header v7: bytes 0..8 `qleancol`, 8 version (7), 9 type code, 10 kind, 11 part count (u8), 12..16 zero (keeps the
    count 8-aligned), 16..24 u64 count, then the part table at 24 and the parts. `attr` and the domain name are gone.
  - Rust `crate/src/own.rs` (`write_head`, `write`, `head`, `Mapped`, `map`, tests) and `crate/src/ffi/own.rs`
    (`qlean_own_write(path, code, kind, count, parts)`; `qlean_own_map` ctor: object `parts`, scalars count, code, kind).
    `cargo test --release --features std own`: 7 passed (before the `hdr` field removal; re-run).
  - Lean: `Rel/Kernel/Db/ObjectFile.lean` (`OwnFile {code kind count parts}`, `ownVersion 7`, `ownImage`, `ownWrite`,
    `ownParse`), `Db/Own.lean`, `Run/Table.lean` (domain check removed), `Run/Lang/Plan.lean` (`ownFile`, `litSide`
    registers now 4), `Lang/EmitC.lean` (`Reg Db.OwnFile`), `Lang/TestNative.lean` (got-pattern), `KernelSpec/Own.lean`
    (`ownParse_ownImage` re-proved). `lake build Rel.KernelSpec.Own Rel.Run.Table Rel.Run.Lang.Plan Rel.Lang.EmitC` green.

## Left
1. `Rel/Kernel/Db/OwnTest.lean`: every `ownWrite` call drops the `attr` and `domain` args (`ownWrite p 7 6 5 #[]`);
   `key`/`say` drop `attr`/`domain`; expected texts: "byte 11:" -> "byte 10:", refusal "a column of kind and part count
   2:2 or 5:0, given kind K with N parts"; the hand-built files (lines ~95-260) must be rebuilt in the v7 layout above;
   the domain-name cases (NUL, UTF-8, "domain `dom`") are deleted; the version error text gained "version 7 removed the
   attribute byte and the domain name, ". Then build `Rel.Kernel.Db.OwnTest Rel.Lang.TestNative`.
2. Native inputs test/native/in/{t,f,k} (files t/px t/qty f/px f/w k/key/px k/val/qty): v6 -> v7 is bytes 8..16 only
   (domain was empty, so offsets are unchanged): old `06 cc 00 kk np 00 00 00` -> new `07 cc kk np 00 00 00 00`.
   Rewrite with `printf` + `dd conv=notrunc bs=1 seek=8`, then `sh crate/build.sh syms`, `lake build rel-native`, run
   `.lake/build/native/rel-native` in a dir with empty `out/`, compare with `lake exe relc plan DIR`.
3. PLAN 8.4 line: own header v7.
4. Step 2 (delete `QAtomicType.general`, `Enc.gen`, `QValue`/`QTable`/`IndexCell`, `Carrier .general`, `Run/ValEq.lean`)
   not started. Scale: every `t ≠ .general` hypothesis goes (atomOfBits, nullAtom, Carrier.null, Column.ofAtoms,
   Cast.decEq, ne_general_of_width and the Rep*/KernelSpec lemmas that thread `hg`: RepCanon, RepCols, RepSums,
   RepTabArith, RepOrder, ObjOrder, KernelSpec/Asc, Elementwise), plus `.general` arms in Sort, Coc, Csv, Elab, EmitC,
   Run/Core (`Arr.get`, `gen_size`, `gs` test), Monadic's Inhabited instance; `Enc` stops being mutual (foR, pos), which
   shifts `pos`'s ctor index: check `crate/src/blocks.rs` `POS`. The kernel tests that use `.gen #[]` as a non-foR
   input (AscTest, SeenTest, ScatterTest, GatherTest, BitRowsTest) need another non-foR input or deletion. qlean
   `require`s this package and builds its values on `Ext.QValue X`: deleting it moves that type into qlean.
