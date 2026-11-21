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

/-! Real-valued statistics (q's names), always in `F`, never an integer quotient: values are cast to `F` before they
    are summed or multiplied, so integer and `f64` columns both work. `F` is declared, not an object variable fixed
    by each use: `dev ≜ var sqrt` with a result variable is refused (its check instantiates the variable at `i64`).
    `Z` is the object a day count lives in. A program of its own:
    its objects take part in reading every literal of a program that opens it. -/
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup in
rel_program frameStat where
    obj F : f64
    obj Z : i64
    -- on the array of a column's values, like prim `sum`: `summarize(F(c) avg, c)` for a column,
    -- `aggregate(a, F(x c) avg, x)` per group. Values are cast to `F` once, here and in `cov`: a sum or product in
    -- the column's own object would leave it (a bounded one) or be an integer (q's `avg` of longs is a float)
    avg : [γ] ⟶ F ≜ F(𝟙 $ F) ⟨sum, length $ F⟩%
    -- `var` and `svar` are `cov`, `scov` of a column with itself; `scov` scales by n/(n−1), none at one row
    cov : [γ×γ] ⟶ F ≜ F(⟨π₁ $ F, π₂ $ F⟩) ⟨F(times) avg, ⟨F(π₁) avg, F(π₂) avg⟩times⟩minus
    scov : [γ×γ] ⟶ F ≜ ⟨cov, ⟨length $ F, tail length $ F⟩%⟩times
    var : [γ] ⟶ F ≜ F(⟨𝟙, 𝟙⟩) cov
    svar : [γ] ⟶ F ≜ F(⟨𝟙, 𝟙⟩) scov
    dev : [γ] ⟶ F ≜ var sqrt
    sdev : [γ] ⟶ F ≜ svar sqrt
    -- q calls it `cor`; named `corr` because the prelude's `cor` is already the coreflexive of a relation's pairs
    corr : [γ×γ] ⟶ F ≜ ⟨cov, ⟨F(π₁) dev, F(π₂) dev⟩times⟩%
    -- skewness, population (DataHaskell's `skewness'`, g1 = m3/m2^1.5): m3 = E[x³] − 3μσ² − μ³ over σ²·σ; each value
    -- is cast to `F` before it is cubed, never a cube in γ
    skewness : [γ] ⟶ F ≜ ⟨⟨F(𝟙 $ F ⟨⟨𝟙, 𝟙⟩times, 𝟙⟩times) avg, ⟨avg, ⟨⟨var, ⟨var, var⟩plus⟩plus, ⟨avg, avg⟩times⟩plus⟩times⟩minus, ⟨var, dev⟩times⟩%
    -- linear interpolation (DataHaskell `quantiles'`, polars "linear"): at h = p·(n−1) on `c` sorted, the rows `i` with
    -- |i − h| < 1 weighted 1 − |i − h|, i.e. lower + frac·(upper − lower); q's `med` is p = 0.5; no row unless 0 ≤ p ≤ 1
    quantile(p : 1 ⟶ F, c : ν ⟶ γ) : 1 ⟶ F ≜ summarize(F(q) sum, q) where h ≜ dom(⟨{(∗,0.0)}, p⟩ cor(≤)) dom(⟨p, {(∗,1.0)}⟩ cor(≤)) ⟨p, ⟨count(c) $ F, {(∗,1.0)}⟩minus⟩times, d ≜ ⟨dom(c) $ F, ⊤ h⟩minus, w ≜ ⟨⊤ {(∗,1.0)}, ⟨d, ⟨⊤ {(∗,0.0)}, d⟩minus⟩max⟩minus, q ≜ dom(⟨⊤ {(∗,0.0)}, w⟩ cor(<)) ⟨w, sortBy(𝟙, c) $ F⟩times
    -- per row (x − mean)/std, the sample std as DataHaskell's `variance'` (n − 1); none at one row
    zScore(c : ν ⟶ γ) : ν ⟶ F ≜ ⟨⟨c $ F, ⊤ m⟩minus, ⊤ s⟩% where m ≜ summarize(F(c) avg, c), s ≜ summarize(F(c) sdev, c)
    valueProportions(a : β ⟶ γ, x : ν ⟶ β) : ν ⟶ γ×F ≜ valueCounts(a, x) ⟨π₁, ⟨π₂ $ F, ⊤ count(x) $ F⟩%⟩
    -- count, mean, std (pandas: the sample one, null at one row), min, max of a column
    describe(c : ν ⟶ γ) : 1 ⟶ ν×(F×((F+1)×(γ×γ))) ≜ ⟨count(c), ⟨summarize(F(c) avg, c), ⟨tot(summarize(F(c) sdev, c)), ⟨summarize(F(c) Λ(∋) head, c), summarize(F(c) Λ(∋) last, c)⟩⟩⟩⟩
    -- the days from `b` to `a`, at any date object `δ`: each date read as its day count
    daysBetween(a : ν ⟶ δ, b : ν ⟶ δ) : ν ⟶ Z ≜ ⟨a $ Z, b $ Z⟩minus

end Rel.Programs
