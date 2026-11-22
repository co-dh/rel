nativetm3a handoff (checkpoint 40)
- Done (WIP commit, not yet built): Rel/Lang/EmitC.lean — groupsB (compGroups), codeB/code2B/colCatB/csrB/bitMatrixB/ofBitsB,
  ldivOfB, ldivB, ldivBitsB, bitsWinB, iteT, ldivSelB, convB, rdivB; tabB .ldiv/.rdiv; Env + sideArg; argB binds call
  arguments lazily (dem or not closed-buildable); kbitrows in `abi`.
- Left: TestNative native1a defs ld (x \ x), l1 (a1 \ a2 count path), rd (x° / x°), gc (g(succ)) + semOuts;
  build `lake build Rel.Lang.TestNative relc`; `make native`; full build; PLAN.md I11 line.
