import Rel.Programs.Frame

/-! # The dataframe library, part 2: sorting and grouping (`doc/dataframe-design.zh.typ` §3.1, rewritten forms of
    `/data/tmp/dfplan/plan.md` §a). A group is numbered by the first occurrence of its key, in position order. -/

namespace Rel.Programs

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameGroup where
    -- q's grades: the pairs `(a, i)` numbered in lexicographic order, then `i`; ties keep position order (stable)
    iasc(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ ν ≜ nth(lex(>, >), ran(⟨x a, 𝟙⟩)) π₂
    idesc(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ ν ≜ nth(lex(<, >), ran(⟨x a, 𝟙⟩)) π₂
    sortBy(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ iasc(a, x) x
    topBy(n : 1 ⟶ ν, a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ take(n, sortBy(a, x))

    -- `head` of the ascending image is the first position of each key: no self-join
    firstOcc(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ ν ≜ nth(>, ran(agg((x a)°, head)))
    g(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ ν ≜ x a (firstOcc(a, x) x a)°
    lastOcc(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ ν ≜ agg(g(a, x)°, last)
    distinct(x : ν ⟶ β) : ν ⟶ β ≜ firstOcc(𝟙, x) x

    aggregate(a : β ⟶ γ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ γ×δ ≜ ⟨firstOcc(a, x) x a, agg(g(a, x)°, f)⟩
    collect(a : β ⟶ γ, c : β ⟶ δ, x : ν ⟶ β) : ν ⟶ γ×[δ] ≜ aggregate(a, F(x c), x)
    valueCounts(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ γ×ν ≜ aggregate(a, length, x)
    countDistinct(x : ν ⟶ β) : 1 ⟶ ν ≜ count(distinct(x))
    -- the most frequent value; among ties the first to occur (`idesc` is stable)
    mode(a : β ⟶ γ, x : ν ⟶ β) : 1 ⟶ γ ≜ summarize(head, s) s where s ≜ idesc(π₂, valueCounts(a, x)) valueCounts(a, x) π₁
    -- the mean of the middle sorted rows, those with `count − 2 ≤ 2i ≤ count` (one row or two), in integers
    median(a : β ⟶ γ, x : ν ⟶ β) : 1 ⟶ γ ≜ summarize(F(m a) ⟨sum, length⟩div, m) where m ≜ dom(⟨𝟙,𝟙⟩plus ≤ count(x)°) dom(⟨𝟙,𝟙⟩plus succ succ ≥ count(x)°) sortBy(a, x)

end Rel.Programs
