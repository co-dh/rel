import Rel.Programs.Prelude

/-! The rows `inl°`, `inr°` (the injections' converses) and the case `[R,S] = inl°R ∪ inr°S` they elaborate, on a
    sum with both summands, on one with only left rows, and with either part empty. Expected rows worked by hand. -/

namespace Rel.Lang.TestSum

open Rel.Programs.prelude in
rel_program sumT where
    obj N = 0…5
    r : N ⟶ N ≜ {(1,2),(2,3)}
    s : N ⟶ N ≜ {(3,4),(4,4)}
    il : N ⟶ N+N ≜ r inl
    ir : N ⟶ N+N ≜ s inr
    sm : N ⟶ N+N ≜ il ∪ ir
    f : N ⟶ N ≜ {(2,0),(3,1)}
    g : N ⟶ N ≜ {(4,5)}
    e : N ⟶ N ≜ r 𝟘
    lc : N ⟶ N ≜ sm inl°
    rc : N ⟶ N ≜ sm inr°
    lr : N ⟶ N ≜ il inr°
    rl : N ⟶ N ≜ ir inl°
    both : N ⟶ N ≜ sm [f, g]
    rEmpty : N ⟶ N ≜ sm [e, g]
    sEmpty : N ⟶ N ≜ sm [f, e]
    lOnly : N ⟶ N ≜ il [f, g]
    jc : N+N ⟶ N ≜ [f, g]
    whole : N ⟶ N ≜ sm jc
    check lc = {(1,2),(2,3)}
    check rc = {(3,4),(4,4)}
    check lr = 𝟘
    check rl = 𝟘
    check both = {(1,0),(2,1),(3,5),(4,5)}
    check rEmpty = {(3,5),(4,5)}
    check sEmpty = {(1,0),(2,1)}
    check lOnly = {(1,0),(2,1)}
    check whole = {(1,0),(2,1),(3,5),(4,5)}

-- by hand: `sm` is `1 ↦ inl 2`, `2 ↦ inl 3`, `3 ↦ inr 4`, `4 ↦ inr 4`. `inl°` keeps the left rows with their payload
-- (`lc` = `r`), `inr°` the right ones (`rc` = `s`); `il` has no right row and `ir` no left one, so `lr`, `rl` are
-- empty. `[f,g]`: `inl 2 ↦ f(2) = 0`, `inl 3 ↦ 1`, `inr 4 ↦ g(4) = 5` twice. With `e = 𝟘` in place of `f` only the
-- right rows answer, in place of `g` only the left ones; `il [f,g]` reads the left part only (its right payload is
-- empty). `jc` is the case closed at the top level, run on `sm`'s values by composition: the same rows as `both`.
#guard sumT.ok

end Rel.Lang.TestSum
