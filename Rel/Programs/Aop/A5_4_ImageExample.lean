/-! # The image example of B&dM §5.4 (`AOP/A5_4_ImageExample.lean`), in Rel: no row ported

`ImageExample` fixes two enumerated types `A = {1,2,3}`, `B = {a,b,c}` and a relation `R : A ⟶ B`, then checks the
tables of `existsImage` (`E`) and `powerRel` (`P`) on every subset of `A` by `decide` over host lists. Rel has no
user-declared enumeration types (`Obj` is closed, A10_3), and `powerRel` has no closed term (`A5_4.lean`), so neither
table is a relation statement; the rows are `∀ row ∈ <host list>` facts about `List`, not `⊑` or `=`. -/

-- not ported: E_column (Freyd.Alg.ImageExample.E_column, 05-datatypes.typ:323): a table over host lists of an enumerated type `A`, `B`; `∀ row ∈ [...]` is not a relation equation or inclusion
-- not ported: P_column (Freyd.Alg.ImageExample.P_column, 05-datatypes.typ:324): same, and `powerRel` has no closed Rel term (Rel/Programs/Aop/A5_4.lean)
