/-! # Structural recursion by currying (`AOP/A3_5_Currying.lean`), in Rel: no row ported

`structural_recursion` is a law of a cartesian closed category `𝒞` with an initial algebra of an endofunctor `F`: a
`G`-algebra on `A ^^ B` built from a natural `φ` gives the unique `f` with `(B × α) f = φ G(f) h`. It quantifies over the
functors `F`, `G`, the natural transformation `φ`, and uses the exponential `A ^^ B` and `eval`. Rel's objects are closed
under `×`, `+` and `[ ]` only: there is no exponential object and no functor parameter (the relator `F` is not a
parameter, A5_1), so the row has no statement. -/

-- not ported: structural_recursion (Freyd.structural_recursion, 03-applications.typ:189): exponential `A ^^ B`, an initial algebra of a variable functor `F` and a natural `φ` (∀ over functors); not a Rel object or parameter
