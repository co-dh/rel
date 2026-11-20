import Rel.Programs.Frame

/-! # The dataframe library, part 2: sorting and grouping (`doc/dataframe-design.zh.typ` §3.1, rewritten forms of
    `/data/tmp/dfplan/plan.md` §a). A column `c : ν ⟶ γ` is the frame composed with a field (`x a`); a group is
    numbered by the first occurrence of its key, in position order. -/

namespace Rel.Programs

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameGroup where
    -- q's idesc, stable: `asc` on (value, m−1−i) read from its end, so `r : i ↦ m−1−i` on both sides
    idesc(c : ν ⟶ γ) : ν ⟶ ν ≜ r asc(ran(⟨c, r⟩)) π₂ r where r ≜ dom(c) ⟨⊤ count(c), succ⟩minus
    sortBy(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ dom(x) iasc(x a) x
    topBy(n : 1 ⟶ ν, a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ take(n, sortBy(a, x))
    sortByDesc(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ dom(x) idesc(x a) x
    -- the `n` rows of largest `a`, ties in position order (`bottomK` is `topBy`)
    topK(n : 1 ⟶ ν, a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ β ≜ take(n, sortByDesc(a, x))

    -- `head` of the ascending image is the first position of each key: no self-join
    firstOcc(c : ν ⟶ γ) : ν ⟶ ν ≜ dom(c) asc(ran(agg(c°, head)))
    -- q's group as a relation: group number ↦ the positions holding its key
    group(c : ν ⟶ γ) : ν ⟶ ν ≜ firstOcc(c) c c°
    lastOcc(c : ν ⟶ γ) : ν ⟶ ν ≜ agg(group(c), last)
    distinct(x : ν ⟶ β) : ν ⟶ β ≜ firstOcc(x) x

    aggregate(a : β ⟶ γ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ γ×δ ≜ ⟨firstOcc(x a) x a, agg(group(x a), f)⟩
    collect(a : β ⟶ γ, c : β ⟶ δ, x : ν ⟶ β) : ν ⟶ γ×[δ] ≜ aggregate(a, F(x c), x)
    valueCounts(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ γ×ν ≜ aggregate(a, length, x)
    countDistinct(x : ν ⟶ β) : 1 ⟶ ν ≜ count(distinct(x))
    -- the most frequent value; among ties the first to occur (`idesc` is stable)
    mode(a : β ⟶ γ, x : ν ⟶ β) : 1 ⟶ γ ≜ summarize(head, s) s where s ≜ idesc(valueCounts(a, x) π₂) valueCounts(a, x) π₁

end Rel.Programs
