merge ROW-DFN handoff. DONE (compiles, no sorry), Rel/Lang/PreludeMerge.lean:
- `mstep`, `miter`, `mstep_inv`, `mstep_iter`, `loopDen_merge` (loopDen T (((x,y),[]), x ++ y) c <-> c = (([],[]), merge x y le)
  given `hT : ∀ s e w, T (s, e) w ↔ (s.1.1 ≠ [] ∨ s.1.2 ≠ []) ∧ w = mstep le s`), `Prim.den_loop`, `Prim.den_merge`,
  `Tm.zeroLit`, `Tm.headAt`, `Tm.headAt_den`, `Tm.mergeTail`, `Tm.mergeTail_den` (tail xs ys <-> ∃ a, xs = a :: ys).
- Prelude text added after takewhile (builds), row `merge` has `prelude := `Rel.Programs.prelude.merge`.
- PreludeDen: imports PreludeMerge, `unproved := ["merge"]` until `Tm.mergeDef_den` exists (delete the entry then).

LEFT: `Tm.mergeDef_row` and `Tm.mergeDef_den`. Method (as `Tm.estDef_den`): `obtain rfl : Tm.mergeDef (.var 1) = t' := Except.ok.inj ht`
(defeq with the evaluated body; `Rel.Programs.prelude.merge.body` printed by `#print` in a scratch file imports PreludeRows + Programs.Prelude).
The body is let-lifted calls; its exact shape (B generic, Q : Tm B B), to be defined as `Tm.mergeDef` and checked by that `obtain`:

  .arg (.arg (.call [2,1] `a none [] (.arg (.arg (.arg (.call [3,2,1] `b none []
      (.arg (.arg (.arg (.arg (.call [6,3,2,1] `l none [] MAIN) L_DEF) (.var 3)) (.var 2)) (.var 1))) B_DEF) (.var 2)) (.var 1))) A_DEF) Q
  A_DEF = .comp (.comp .outl .outl) Tm.headAt        B_DEF = .comp (.comp .outl .outr) Tm.headAt
  L_DEF = .join (.dom (.comp (.pair (.var 2) (.var 3)) (.arg (.call [2] `Rel.Programs.prelude.cor (some `Rel.Programs.prelude.cor.conv) [B, B]
            (.dom (.meet (.comp .outl (.var 2)) .outr))) (.var 1)))) (.diff (.dom (.var 2)) (.dom (.var 3)))
  MAIN  = .comp (.comp (.pair (.pair .id Tm.nil) (.prim (rowOf "cat"))) (.arg (.prim (rowOf "loop")) (.comp .outl X))) .outr
  X     = .join (.comp (.var 6) A_PART) (.comp (.diff .id (.var 6)) B_PART)
  A_PART = .pair (.pair (.comp (.comp .outl .outl) (Tm.mergeTail B)) (.comp .outl .outr)) (.comp (.pair .outr (.var 2)) (.prim (rowOf "snoc")))
  B_PART = .pair (.pair (.comp .outl .outl) (.comp (.comp .outl .outr) (Tm.mergeTail B))) (.comp (.pair .outr (.var 3)) (.prim (rowOf "snoc")))
(the printed tree was read from the `#print`; the association of `.comp` in MAIN/tail is the one thing to confirm by the `obtain`.)

Proof of `Tm.mergeDef_row ρ Q p ys : (Tm.mergeDef Q).den ρ p ys ↔ (Tm.arg (.prim (rowOf "merge")) (pairTest Q)).den ρ p ys`:
1. `simp only [Tm.mergeDef, Tm.den, Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, and_self, Prim.den_loop, Prim.den_merge]`
   (this set reduced every Val.bind cast on the real body; `Tm.mergeTail`/`Tm.headAt` stay folded so `Tm.mergeTail_den`/`Tm.headAt_den` rewrite them).
2. `refine (loopDen_merge (fun a b => decide (Q.den ρ a b)) _ ?hT x y ys).trans ?_`-shaped step: T is unified from the goal.
3. `?hT`: cases xs, ys; each is `Tm.mergeTail_den`, `Tm.dom_den'`, `Prim.den_snoc`, `Tm.headAt_den` and the call `cor` = `dom(π₁Q ∩ π₂)` read at `ρ 1`;
   the pair test `(pairTest Q).den ρ (a,b) (a,b) ↔ Q.den ρ a b` is `hτ` in `Tm.frontDef_row`.
Then `Tm.mergeDef_den` as `Tm.estDef_den`; then delete `"merge"` from `unproved` in PreludeDen.lean.
