B5a4 handoff (branch worktree-agent-ac2cd20153d892fcb; decisions 1-3 of /data/tmp/b5a3-handoff.md stand)

Done:
- merged ea28997 (B5a3 WIP) and 7ed706e (master's Core/Table fix for 8.4 Arr); no conflicts.
- Step 1 green (job b5a4-5): ConvSpec `arg` case (Rel/Lang/ConvSpec.lean ~:220): `convTm`'s match on `f'` is
  dependent, `split` cannot see it; now `cases f' <;> (have hu := Except.ok.inj hu; subst hu) <;> first | ...`.
  The instObj copy (~:617) goes through with `simp only [hf, bind_ok_iff] at hu; obtain ⟨_, ⟨⟩, hu⟩ := hu; split`.
  Built green: ConvSpec GenSound Test.{Folds,Fixpoints,Arith,Blocks,Chs,Prelude} TestMss Programs.{Blocks,Mss,Prelude}.
- Decision 1 expandNote: no change needed. The lazy converse forced over a universe is `.conv (U ≫ t')`; `U` comes from
  `uniTm` → `uniPart`: a declared universe is its literal (already rows, no expansion), a product universe goes
  through `Tm.prodUni` → `⊤`/CROSS → `Vals.cross`, which calls `Rel.expandNote`. The force itself is `GenK.compT`
  of U's table with the lazy row: output rows ≤ |U| × row fan-out, no expansion step of its own.
- Decision 3 (job b5a4-6): deleted Tab.arith, Tab.succ (Run/Arith), Tab.succ_holds, Tab.arith_holds and the private
  Checks section (arithOk/succOk) (RepTabArith), arith_wf/succ_wf (RepWFOps), domAt/succB/arithT (EmitC; nodeB no
  longer calls them after the merge). Kept: succCol, succCol_row, stepColsAt*, Lang.arithDen_iff (DfnLaw uses it).

Left: decision 2 (not started). Sites: Tm.lean (Tm.leq/Tm.lt ctor, dem/size/mapMSz/fv/subst/pol), Den (leqDen,
ltDen, leq_le :691, lt_le :694, den cases), GenSound, TmGen (gen/hasCode/tmE), GenK.leq/lt (:270/:272, keep
GenK.cmp's K.pairs path), Elab :309-310 (instObj), :610, :1081, :1168, :1994-1995 (convTm), :2487-2493 (max/min,
`.leq`/`.lt` build). Open design point: the language's `≤`/`<` are relations N ⟶ N, cmpRow is a coreflexive on
N×N; `≤ = ⟨U, ⊤U⟩ ≫ (U×U) le ≫ π₂` reads CROSS when only one side is known, so the TmGen pattern for
`(U×U) ≫ cmpRow r` in a meet (the K.pairs path) is what keeps pc9-time (6 s) green. Then PLAN B5 paragraph.
