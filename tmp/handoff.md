# nativetm5 handoff

Done:
- Step 1: `funT` (Rel/Lang/EmitC.lean, before `groupsB`) builds a recipe as a plan function and `apply`s it; an equal
  `Fun` (derived `BEq` on `Val`, `Instr`, `Fun` in Rel/Run/Lang/Plan.lean) is reused, so one C function per table
  shape. `compSelB`, `compB`, `ldivSelB` go through it. `rel-native.c` 7.8 MB -> 4.5 MB (4.7 MB with `fm`),
  `cc1 -O2` peak 1.35-1.47 GB; `make native` exit 0.
- Step 2: `fm ≜ lm F(rt)` is byte-equal (plan = native = Lean) and in `semOuts`. The "0 images" failure was `hy`,
  not `fm`: `hylo`'s `μY` starts from `Y = 𝟘`, so `F(Y)` gives no image to an element, where `Tab.map`
  (Rel/Run/Fix.lean:122) runs its left fold `foldRounds peelL (fun acc el => snoc (acc.pair (el.comp R)))`.

Left:
- `Tab.map`'s fold branch in `cellsMapB`, then `hy` into `semOuts`. Needs plan recipes for `uncons` (`peelL`),
  `snoc`, `pair` on array sides, and `Tab.foldRounds` (Rel/Run/Fix.lean:44) on `Instr.loop` (`loop` in
  Rel/Run/Lang/Plan.lean; `fixB` in EmitC is the model: state = count + `regsOf`, `withRegs` to read back).
  `cellsMapB` should `iteT` between the one-pass form and the fold on the bit it now `guard`s.
- `est`, `thin` (`Tab.est`, `Tab.thin`), `fold`/`foldr`/`foldI` (`GenK.fold`, Rel/Run/Lang/GenK.lean ~345): all on
  `foldRounds`, so the same loop recipe serves them. Each a `native1a` def plus a `semOuts` entry.
