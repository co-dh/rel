import Rel.Programs.Detab

/-! # Companion rows of freyd §10.2 (`AOP/A10_2_Detab.lean`), in Rel

The `run_*` rows are `check`s on the program `Programs.detab` (tab width 4, `book4`), whose definitions this program
reads. Each carries the freyd declaration and the companion position (chapter file : line). -/

namespace Rel.Programs

open Rel.Programs.prelude Rel.Programs.detab in
rel_program aopA10_2_Detab where
    check x = {(∗,a b TB c BL d)}                                                   -- run_input, 10-greedy.typ:273
    check x detab = {(∗,a b BL BL c BL d)}                                          -- run_detab, 10-greedy.typ:277
    check x detab entab = {(∗,a b TB c BL d)}                                       -- run_entab, 10-greedy.typ:289

-- not ported: Q_eq (Freyd.Alg.RelSet.Detab.Q_eq, 10-greedy.typ:108): `Q` is a relation by cases on `F(String)`; written `𝟙+(V×U)` it is its own definition, a syntactic identity
-- not ported: detab_cata (10-greedy.typ:87): identifies the fold `⦇[nil,expand]⦈` with `graph detabFn`, a host function with no relation in Rel; needs the snoc-list relator F
-- not ported: detab_V_R, expand_V (10-greedy.typ:49,48): need `fill`, `V` and the `fill V° = fill`, `snoc V° ⊑ snoc ∪ π₁V°` laws over `col mod n`, proved by induction on the input; no proof attempted at unbounded N (Programs.detab has N = 0…24)
-- not ported: detab_prefix_false (10-greedy.typ:167): a negation `¬(detab prefix ⊑ R° detab)`; a theorem states an equation or inclusion, and the witness needs tab width 8, beyond the program's N
-- not ported: detab_tupled, outl_loop (10-greedy.typ:187,203): need `loop'` and the host `loop` on lists; `loop` is a prelude definition over `foldI` that every proof must unfold, and the tupling law of two folds has no lemma in rel
-- not ported: entab_branch, entab_laws_prefixed, entab_mono, entab_thin_condition (10-greedy.typ:178,153,164,162): instances of Theorem 10.1 / Proposition 10.1 at the snoc-list relator F; need a generic relator F (design pending)
-- not ported: entab_triple (10-greedy.typ:259): `entab` is defined in Programs.detab as exactly `triple assocl π₁ (𝟙×blanks) cat`, a syntactic identity
-- not ported: tbc_col_fold, triple_fold (10-greedy.typ:235,247): `tbc`, `unfill` have no relational definition here and the tupling of folds has no lemma in rel
-- not ported: rel_cands, rel_estC (10-greedy.typ:270,271): equate a host List enumeration with `expand°` and `Λ(expand°)est(V×U)`; the relation side is the only one in Rel
-- not ported: detab_len_of_short, entab_unfill, expand_recip_snoc, fill_exists_iff, tbc_nil, tbc_snoc, detab_V, entab_laws, entab_V (host Nat/List statements or element quantifiers; rewrite needs `fill`, `unfill`, `tbc` as relations)
-- not ported: run_cands, run_estC (10-greedy.typ:281,285): `cands`/`estC` are host List functions; `V×U` and `Λ(expand°)` are not defined in Programs.detab

end Rel.Programs
