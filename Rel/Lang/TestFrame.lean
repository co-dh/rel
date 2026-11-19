import Rel.Programs.Prelude
import Rel.Lang.EmitC

/-! Stage 1 of `doc/dataframe-design.zh.typ` (§6): a two-column frame filtered, grouped by its key and summed per
    group, in the design's position form (§1.2, §2, §3.1), positions `P` standing for `N` below `m = 8`.

    - `frameSchema` is the program as the design writes it, typed by the schema `S`; it is refused (pinned below).
    - `frame` is the nearest spelling that runs: the columns `k`, `v` are the program's own maps out of `P`, so each
      `x ≫ col S "…"` is written as the column it reads. -/

namespace Rel.Lang.TestFrame

-- F10: the list form's `groups(k)` through `strₗ`, which the language does not have
/-- error: line 23, col 36: unknown name 'str' -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program frameSpec where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(>{(2,∗)})
    sel(k : γ ⟶ K) : K×[γ] ⟶ [γ] ≜ strₗ filter(cor(k°)) F(π₂)
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) Λ(⟨∋π₁, 𝟙⟩⟨π₁, sel(π₁)⟩) F(𝟙 × (F(π₂) sum))

/-- error: line 35, col 13: expected an object, found 'S' -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program frameSchema where
    obj K = {A,B,C}
    obj N = 0…40
    obj P = 0…7
    k : P ⟶ K ≜ {(0,B),(1,A),(2,B),(3,C),(4,A),(5,C),(6,B),(7,A)}
    v : P ⟶ N ≜ {(0,5),(1,3),(2,5),(3,1),(4,7),(5,2),(6,1),(7,3)}
    x : P ⟶ S.obj ≜ ⟨k, v⟩
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    keep : P ⟶ P ≜ dom(x col(S, v) big)
    groups : K ⟶ P ≜ (keep x col(S, k))°
    out : K ⟶ N ≜ dom(groups) Λ(groups) F(v) sum
-- `S` is not declared here: a program declares it `schema S = {k : K, v : N}` and reads `col S "v"`
-- (`TestSchema.kvProg`).

open Rel.Programs.prelude in
rel_program frame where
    obj K = {A,B,C}
    obj N = 0…40
    obj P = 0…7
    k : P ⟶ K ≜ {(0,B),(1,A),(2,B),(3,C),(4,A),(5,C),(6,B),(7,A)}
    v : P ⟶ N ≜ {(0,5),(1,3),(2,5),(3,1),(4,7),(5,2),(6,1),(7,3)}
    x : P ⟶ K×N ≜ ⟨k, v⟩
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    keep : P ⟶ P ≜ dom(v big)
    groups : K ⟶ P ≜ (keep k)°
    out : K ⟶ N ≜ dom(groups) Λ(groups) F(v) sum
    check out = {(A,13),(B,10)}

-- by hand: `keep` is the positions 0 1 2 4 7; A's are 1 4 7 (3+7+3), B's 0 2 (5+5), C has none. B's two rows both
-- hold 5: the sum runs over positions, so they count twice.
#guard frame.ok
-- `out`'s term, read as `outputOf` reads it, and the first place the denotation has no rule for it: none, since `Λ`
-- and `E` at a canonical element object (`K` is stored `.i64`) have `lam_sound` (D.8)
/-- info: none -/

#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  let r ← (Rel.Lang.Expand.read (fun _ => none) [(`Rel.Programs.prelude, Rel.Programs.prelude)] frame).run
  let (ds, _) ← match r with | .ok v => pure v | .error e => throwError "{repr e}"
  let some ⟨_, _, t⟩ := ds.lookup "out" | throwError "frame has no closed `out`"
  Lean.logInfo m!"{t.gap}"

end Rel.Lang.TestFrame
