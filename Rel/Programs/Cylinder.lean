import Rel.Programs.Prelude
import Rel.Lang.Laws.Cylinder

/-! # Shortest paths on a cylinder

B&dM §7.4 (diag/aop/07-optimisation.typ, "Shortest paths on a cylinder", the `Vec` version): a matrix of `m` columns of
`n` squares is `[[N]]`, a path is `[N]`, the `p` candidate paths into a row are `[[N]]`; every count is the array's
length, so `τ` and `cons` of the book's sum functor are `τ` and `cons` of the prelude. `gen` extends every candidate
path by one column; `Q` keeps one path per square. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program cylinder where
    obj N = 0…40                                  -- the squares and their sums, non-negative

    /- The moves of a row: rotate it up, leave it, rotate it down (`moves(x) = (up(x), x, down(x))`, a 3×n matrix), and
       the transpose `trans`, a left fold of `zip`/`snoc` from the first row's singletons. -/

    up : [α] ⟶ [α] ≜ ⟨tail, head τ⟩cat
    down : [α] ⟶ [α] ≜ ⟨last τ, init⟩cat
    moves : [α] ⟶ [[α]] ≜ ⟨up τ, ⟨τ, down τ⟩cat⟩cat
    trans : [[α]] ⟶ [[α]] ≜ ⟨head F(τ), tail⟩loop(zip F(snoc))
    cp : α×[β] ⟶ [α×β] ≜ ⟨⟨π₁,nil⟩,π₂⟩loop(⟨π₁π₁,⟨π₁π₂,⟨π₁π₁,π₂⟩⟩snoc⟩)π₂

    /- `gen` (table `vec-defn-cyl`): the new column's squares each in front of every candidate path of their three
       neighbours. `⦇gen⦈` and `⦇Q⦈` are folds over the non-empty array of columns, from the last column (one
       one-square path per square, `F(τ τ)`, `F(τ)`: the step on the empty accumulator) to the first. -/

    gen : [α]×[[[α]]] ⟶ [[[α]]] ≜ (𝟙×(moves trans F(concat)))zip F(cp F(cons))
    genStep : [α]×[[[α]]] ⟶ [[[α]]] ≜ (dom(π₂ head)gen) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ τ))
    genFold : [[α]] ⟶ [[[α]]] ≜ ⦇[nil, genStep]⦈ʳ
    paths : [[α]] ⟶ [[α]] ≜ genFold concat

    R : [N] ⟶ [N] ≜ sum ≤ sum°                    -- a path is R-below another when its cost is at most the other's
    Q : [N]×[[N]] ⟶ [[N]] ≜ (𝟙×(moves trans F(est(R))))zip F(cons)
    qStep : [N]×[[N]] ⟶ [[N]] ≜ (dom(π₂ head)Q) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ))
    qFold : [[N]] ⟶ [[N]] ≜ ⦇[nil, qStep]⦈ʳ

    /- The run of the book on the columns `1 2 3 4` and `5 6 7 8` (m = 2, n = 4, p = 3). -/

    obj K = {a}
    row : K ⟶ [N] ≜ {(a,5 6 7 8)}
    check row moves = {(a,[6 7 8 5] [5 6 7 8] [8 5 6 7])}
    check row moves trans = {(a,[6 5 8] [7 6 5] [8 7 6] [5 8 7])}

    x : K ⟶ [[N]] ≜ {(a,[1 2 3 4] [5 6 7 8])}
    y : K ⟶ [[N]] ≜ {(a,[[5 6 7 8]])}

    /- `vec-fold-step`: the last column alone, each square its own one-square path. -/

    check y genFold = {(a,[[5]] [[6]] [[7]] [[8]])}
    check y qFold = {(a,[5] [6] [7] [8])}

    /- `vec-step`: one `gen` on the column `1 2 3 4` and that fold, stage by stage. -/

    c : K ⟶ [[[N]]] ≜ y genFold
    w : K ⟶ [N]×[[[N]]] ≜ ⟨x head, c⟩
    check c moves = {(a,[[[6]] [[7]] [[8]] [[5]]] [[[5]] [[6]] [[7]] [[8]]] [[[8]] [[5]] [[6]] [[7]]])}
    check c moves trans = {(a,[[[6]] [[5]] [[8]]] [[[7]] [[6]] [[5]]] [[[8]] [[7]] [[6]]] [[[5]] [[8]] [[7]]])}
    check w π₂ moves trans F(concat) = {(a,[[6] [5] [8]] [[7] [6] [5]] [[8] [7] [6]] [[5] [8] [7]])}
    check w gen = {(a,[[1 6] [1 5] [1 8]] [[2 7] [2 6] [2 5]] [[3 8] [3 7] [3 6]] [[4 5] [4 8] [4 7]])}

    /- The defining equation of the folds at the first column (`cons_genFold`), and the whole fold. -/

    check x genFold = x ⟨head, tail genFold⟩gen
    check x qFold = x ⟨head, tail qFold⟩Q
    check x genFold = {(a,[[1 6] [1 5] [1 8]] [[2 7] [2 6] [2 5]] [[3 8] [3 7] [3 6]] [[4 5] [4 8] [4 7]])}
    check x paths = {(a,[1 6] [1 5] [1 8] [2 7] [2 6] [2 5] [3 8] [3 7] [3 6] [4 5] [4 8] [4 7])}

    /- `vec-q-step`: the greedy fold keeps one path per square (`run_kept`), the cheapest of those costs 6 (`run_cyl`). -/

    check x qFold = {(a,[1 5] [2 5] [3 6] [4 5])}
    check x qFold est(R) = {(a,1 5)}
    check x qFold est(R) sum = {(a,6)}
    check x paths est(R) = {(a,1 5)}

    /- B&dM p.182, the three laws behind `cyl_laws`: the greedy path is among the generated (`Qfold_le_genFold`), and a
       cheapest of the rows' cheapest is a cheapest of the laid end to end (`est_concat`, `R` transitive). -/

    theorem qfoldLe if (𝟙×F(est(R)))qStep ⊑ genStep F(est(R)) : qFold ⊑ genFold F(est(R)) by Rel.Lang.Tm.qfoldLe_den
    theorem estConcat(S : α ⟶ α) if S S ⊑ S : F(est(S)) est(S) ⊑ concat est(S) by Rel.Lang.Tm.estConcat_den
    check x qFold ⊑ x genFold F(est(R))
    check c F(est(R)) est(R) ⊑ c concat est(R)

    /- B&dM p.183 (7.13) on `Vec`: the new square in front of each of the candidates and then the cheapest of them is
       beaten by the cheapest first (`cyl_7_13`); with `zip`, `trans` and `moves` lax natural it is `fusion`. -/

    theorem cons713 if (𝟙×R) ⊑ cons R cons° : (𝟙×est(R))cons ⊑ cp F(cons) est(R) by Rel.Lang.Tm.cons713_den
    check w (𝟙×F(est(R)))Q ⊑ w gen F(est(R))

    /- The laws `fusion` cites besides `cons713` and `estConcat`: `×` and `F` are functors, and `moves`, `trans`, `zip`
       are lax natural (a natural function `η` has `F(S) η ⊑ η G(S)`). -/

    theorem prodComp(A : α ⟶ β, B : β ⟶ γ) : (𝟙×A)(𝟙×B) = (𝟙×(A B)) by Rel.Lang.Tm.prodComp_den
    theorem Fcomp(A : α ⟶ β, B : β ⟶ γ) : F(A)F(B) = F(A B) by Rel.Lang.Tm.Fcomp_den
    theorem movesLax(S : α ⟶ β) : F(S) moves ⊑ moves F(F(S)) by Rel.Lang.Tm.movesLax_den
    theorem transLax(S : α ⟶ β) : F(F(S)) trans ⊑ trans F(F(S)) by Rel.Lang.Tm.transLax_den
    theorem zipLax(S : α ⟶ β) : (𝟙×F(S)) zip ⊑ zip F(𝟙×S) by Rel.Lang.Tm.zipLax_den

    theorem fusion if (𝟙×R) ⊑ cons R cons°, R R ⊑ R : (𝟙×F(est(R)))Q ⊑ gen F(est(R)) := calc
      (𝟙×F(est(R)))Q
        := ≜ Q
      (𝟙×F(est(R))) (𝟙×(moves trans F(est(R)))) zip F(cons)
        = := prodComp(F(est(R)), moves trans F(est(R)))
      (𝟙×(F(est(R)) moves trans F(est(R)))) zip F(cons)
        ⊑ := movesLax(est(R))
      (𝟙×(moves F(F(est(R))) trans F(est(R)))) zip F(cons)
        ⊑ := transLax(est(R))
      (𝟙×(moves trans F(F(est(R))) F(est(R)))) zip F(cons)
        = := Fcomp(F(est(R)), est(R))
      (𝟙×(moves trans F(F(est(R)) est(R)))) zip F(cons)
        ⊑ := estConcat(R)
      (𝟙×(moves trans F(concat est(R)))) zip F(cons)
        = := Fcomp(concat, est(R))
      (𝟙×(moves trans F(concat) F(est(R)))) zip F(cons)
        = := prodComp(moves trans F(concat), F(est(R)))
      (𝟙×(moves trans F(concat)))(𝟙×F(est(R))) zip F(cons)
        ⊑ := zipLax(est(R))
      (𝟙×(moves trans F(concat))) zip F(𝟙×est(R)) F(cons)
        = := Fcomp(𝟙×est(R), cons)
      (𝟙×(moves trans F(concat))) zip F((𝟙×est(R))cons)
        ⊑ := cons713
      (𝟙×(moves trans F(concat))) zip F(cp F(cons) est(R))
        = := Fcomp(cp F(cons), est(R))
      (𝟙×(moves trans F(concat))) zip F(cp F(cons)) F(est(R))
        = := ≜ gen
      gen F(est(R))

    /- The step of the fold: the `dom(π₂ head)` branch is `Q` (`gen`), the other starts from the singletons. `F(S)` keeps
       the length of the accumulator, so the branch test and `π₁` pass through `(𝟙×F(S))`; `F(τ) ⊑ F(τ τ) F(est(S))`
       as `est` of a singleton is its member; composition distributes over `∪`. -/

    theorem compUnion(X : α ⟶ β, A : β ⟶ γ, B : β ⟶ γ) : X (A ∪ B) = (X A) ∪ (X B) by Rel.Lang.Tm.compUnion_den
    theorem unionComp(A : α ⟶ β, B : α ⟶ β, X : β ⟶ γ) : (A ∪ B) X = (A X) ∪ (B X) by Rel.Lang.Tm.unionComp_den
    theorem domLax(S : α ⟶ β) : (𝟙×F(S)) dom(π₂ head) ⊑ dom(π₂ head) (𝟙×F(S)) by Rel.Lang.Tm.domLax_den
    theorem diffLax(S : α ⟶ β) : (𝟙×F(S)) (𝟙 − dom(π₂ head)) ⊑ (𝟙 − dom(π₂ head)) (𝟙×F(S)) by Rel.Lang.Tm.diffLax_den
    theorem pi1Lax(T : α ⟶ β) : (𝟙×T) π₁ ⊑ π₁ by Rel.Lang.Tm.pi1Lax_den
    theorem tauEst(S : [α] ⟶ [α]) : F(τ) ⊑ F(τ τ) F(est(S)) by Rel.Lang.Tm.tauEst_den

    theorem stepFuse if (𝟙×R) ⊑ cons R cons°, R R ⊑ R : (𝟙×F(est(R))) qStep ⊑ genStep F(est(R)) := calc
      (𝟙×F(est(R))) qStep
        := ≜ qStep
      (𝟙×F(est(R))) ((dom(π₂ head)Q) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ)))
        = := compUnion(𝟙×F(est(R)), dom(π₂ head)Q, (𝟙 − dom(π₂ head))π₁ F(τ))
      ((𝟙×F(est(R))) (dom(π₂ head)Q)) ∪ ((𝟙×F(est(R))) ((𝟙 − dom(π₂ head))π₁ F(τ)))
        ⊑ := domLax(est(R))
      (dom(π₂ head)(𝟙×F(est(R)))Q) ∪ ((𝟙×F(est(R))) ((𝟙 − dom(π₂ head))π₁ F(τ)))
        ⊑ := diffLax(est(R))
      (dom(π₂ head)(𝟙×F(est(R)))Q) ∪ ((𝟙 − dom(π₂ head))(𝟙×F(est(R)))π₁ F(τ))
        ⊑ := pi1Lax(F(est(R)))
      (dom(π₂ head)(𝟙×F(est(R)))Q) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ))
        ⊑ := fusion
      (dom(π₂ head)gen F(est(R))) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ))
        ⊑ := tauEst(R)
      (dom(π₂ head)gen F(est(R))) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ τ) F(est(R)))
        = := unionComp(dom(π₂ head)gen, (𝟙 − dom(π₂ head))π₁ F(τ τ), F(est(R)))
      ((dom(π₂ head)gen) ∪ ((𝟙 − dom(π₂ head))π₁ F(τ τ))) F(est(R))
        = := ≜ genStep
      genStep F(est(R))

    -- `qfoldLe`'s `if` is `stepFuse`, under the hypotheses `fusion` and `estConcat` take of `R`
    theorem cylLaws if (𝟙×R) ⊑ cons R cons°, R R ⊑ R : qFold est(R) ⊑ paths est(R) := calc
      qFold est(R)
        ⊑ := qfoldLe
      genFold F(est(R)) est(R)
        ⊑ := estConcat(R)
      genFold concat est(R)
        = := ≜ paths
      paths est(R)
    check x qFold est(R) ⊑ x paths est(R)

#guard cylinder.ok

end Rel.Programs
