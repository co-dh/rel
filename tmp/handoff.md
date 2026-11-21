# s73c handoff (branch s73c)

Done (commit 6976529):
- `Rel/Run/Lang/TmGen.lean`: `tmE sh` (a share slot by its constant), `Code.program : List Res → List Res × Array Res`,
  `noCode` (moved from test/TestCompile.lean), and the emission moved here: `emit`, `ioE`, `ioGo`, `ioOut`, `ioReach`,
  `sigT`, `sigE`, `liftE`, `objsE`, `tabRel`, `bindIO`. `emit` numbers ds/ps/cs and reached run-time bodies with
  `Code.program`, emits `n.c.t<k> : Tm`, `n.shares : Code := Code.shares #[...]`, `n.x := runE (Tm.gen n.shares ⌜t⌝)`.
- Deleted from Expand.lean: `number`, `kernelTwin`, `RM`, mutual `code/share/spine/body/node`, `lams`; from GenK.lean
  `Tm.kernelNode`, `Tm.offKernel`, `Tm.onKernel`. Embed imports TmGen.
- Kept `primFit`/`primsFit`/`primMemo`: used by `once` (object-variable classification) and `rowGens`.

Left: full build (job s73c-build), compile-diff run, allowlists, rel-native gate, PLAN 7.3.
