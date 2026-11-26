import Rel.Programs.Prelude
import Rel.Run.Lang.EmitC

/-! Stage 1 of `doc/dataframe-design.zh.typ` (§6): a two-column frame filtered, grouped by its key and summed per
    group, in the design's position form (§1.2, §2, §3.1), positions `P` standing for `N` below `m = 8`.

    `frame` is the program as the design writes it: the frame `x` is an `input` typed by the schema `S` (D.9), each
    column read as `x col S "…"` (D.11), and the `check` gives `x` its table by `where`. -/

namespace Rel.Lang.TestFrame

-- F10: the list form's `groups(k)` through `strₗ`, which the language does not have
/-- error: line 21, col 36: unknown name 'str' -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program frameSpec where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(>{(2,∗)})
    sel(k : γ ⟶ K) : K×[γ] ⟶ [γ] ≜ strₗ filter(cor(k°)) F(π₂)
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) ^(⟨∋π₁, 𝟙⟩⟨π₁, sel(π₁)⟩) F(𝟙 × (F(π₂) sum))

open Rel.Programs.prelude in
rel_program frame where
    obj K = {A,B,C}
    obj N = 0…40
    obj P = 0…7
    schema S = {k : K, v : N}
    input x : P ⟶ S from "frame"
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    keep : P ⟶ P ≜ dom(x col S "v" big)
    groups : K ⟶ P ≜ (keep x col S "k")°
    out : K ⟶ N ≜ dom(groups) ^(groups) F(x col S "v") sum
    check out = {(A,13),(B,10)} where x ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3))}

-- by hand: `keep` is the positions 0 1 2 4 7; A's are 1 4 7 (3+7+3), B's 0 2 (5+5), C has none. B's two rows both
-- hold 5: the sum runs over positions, so they count twice.
#guard frame.ok

end Rel.Lang.TestFrame
