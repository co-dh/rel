/-! # The point-free filter of B&dM §1.7 (`AOP/A1_7_Pointfree.lean`), in Rel: no row ported

`filter_pointfree` is `⟨𝟙, list(p)⟩ zip filter(π₂) list(π₁) = filter(p)` for a boolean relation `p : A ⟶ Bool`, with
`filter(q) = concat list(q → τ, nil)`. Three things it names are not in the Prelude program:
- `zip : [α]×[β] ⟶ [α×β]` is a row of `doc/rel-rows.md` (a `loop`), but the Prelude defines no `zip` a program can write,
  and it is not a fold `⦇[e,S]⦈` (it reads two lists at once), so a program cannot define it either;
- the conditional `(q → R, S)` needs a boolean object `q : X ⟶ Bool`; the Prelude has none;
- the Prelude's `filter(p : α ⟶ α)` keeps the elements in `dom(p)`: it is not freyd's conditional filter, so
  `filter(π₂)` at `α×Bool` would keep every pair.
Each of the ten calculation steps (1.4)-(1.12) is a rewrite by a rule of the list relator or of `concat`, and rests on
`zip`, so none can be stated without it. -/

-- not ported: nil_list (Freyd.Alg.RelSet.Pointfree.nil_list, 01-programs.typ:23): needs the constant `nil` at a boolean-tested conditional; the instance `nil F(R) = nil` does not match the elaborated cast-prim form (A5_5_TypeFunctor)
-- not ported: zip_natural (Freyd.Alg.RelSet.Pointfree.zip_natural, 01-programs.typ:23): no `zip` in the Prelude program (see above)
-- not ported: conditional_comp (Freyd.Alg.RelSet.Pointfree.conditional_comp, 01-programs.typ:23): no boolean object for `q`
-- not ported: pair_conditional (Freyd.Alg.RelSet.Pointfree.pair_conditional, 01-programs.typ:23): no boolean object, no `zip`
-- not ported: zip_laxNatural_left, zip_laxNatural_right, conditional_τ_laxNatural, conditional_outl_τ_laxNatural, filter_outr_laxNatural (Freyd.Alg.RelSet.Pointfree.*, 01-programs.typ:23): laxNatural over a relator (A5_7: not portable), and no `zip`
-- not ported: filter_pointfree_step1 .. filter_pointfree_step10 (Freyd.Alg.RelSet.Pointfree.filter_pointfree_step*, 01-programs.typ:23): each is one rewrite of the calculation below, and each side mentions `zip` and the conditional filter
-- not ported: filter_pointfree (Freyd.Alg.RelSet.Pointfree.filter_pointfree, 01-programs.typ:23): the 可写 row; blocked by `zip`, the boolean object and the conditional filter above; needs a point-free `zip` with its list-level loop proof (budget an opus agent)
