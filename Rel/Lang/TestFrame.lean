import Rel.Programs.Prelude
import Rel.Lang.EmitC
import Rel.Lang.Rows

/-! Stage 1 of `doc/dataframe-design.zh.typ` (§6): a two-column frame filtered, grouped by its key and summed per
    group, `out ≜ filter(dom(π₂ big)) ≫ Λ(groups(π₁)) ≫ F(𝟙 × (F(π₂) ≫ sum))`.

    - `frameSpec` is the program as the design writes it: `groups(k) = ⟨∋ k, 𝟙⟩ ≫ ⟨π₁, selᴷ(k)⟩` with
      `selᴷ(k) = strₗ ≫ filter(cor(k°)) ≫ F(π₂)`. The language has no `strₗ` (not in `prims`, and the fold that
      carries the key, `foldI`, is a gap), so it is refused.
    - `frame` is the nearest spelling the language has: `sel`, the sub-list of each key, is a left fold whose carrier
      holds the key, seeded once per key of `K` (`⟨⊤(1,K), nil⟩`), and `groups` keeps the keys that occur. -/

namespace Rel.Lang.TestFrame

/-- error: line 24, col 36: unknown name 'str' -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program frameSpec where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(>{(2,∗)})
    sel(k : γ ⟶ K) : K×[γ] ⟶ [γ] ≜ strₗ filter(cor(k°)) F(π₂)
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) Λ(⟨∋π₁, 𝟙⟩⟨π₁, sel(π₁)⟩) F(𝟙 × (F(π₂) sum))

-- `filter` reaches the term as the prelude's fold (`prims` keeps its row only as the run form of that definition)
open Rel.Programs.prelude in
rel_program frame where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    eqK : (K×[K×N])×(K×N) ⟶ (K×[K×N])×(K×N) ≜ dom(⟨π₁π₁,π₂π₁⟩ dom(π₁ ∩ π₂))
    sel : [K×N] ⟶ K×[K×N] ≜ ⦇[⟨⊤(1,K),nil⟩, (eqK ⟨π₁π₁, ⟨π₁π₂,π₂⟩snoc⟩) ∪ ((𝟙 − eqK)π₁)]⦈
    groups : [K×N] ⟶ K×[K×N] ≜ ⟨∋π₁, sel⟩ dom(⟨π₁,π₂π₁⟩ dom(π₁ ∩ π₂)) π₂
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) Λ(groups) F(𝟙 × (F(π₂) sum))
    print 𝟙(1,1) out

-- by hand: `big` keeps (B,5) (A,3) (B,5) (A,7) (A,3); A sums 3+7+3, B 5+5, C has no row; keys ascending. The
-- duplicate rows count twice: a frame is a list, not the set of its rows.
#guard frame.ok && frame.prints == ["𝟙(1, 1) out = {(∗, (A, 13) (B, 10))}"]

/-! Stage 1b. `out`'s term has no node a recipe is keyed on: `filter` is the prelude's fold, and `Λ(groups)` is `Λ` of
    the key-seeded fold `sel`, not `Λ(groups(k))`, which the language cannot write. So `Plan.ofTm` is not extended; the
    recipes are built here on `x`'s element columns, `big` as its mask (`x > 2`), and checked against `out`. -/

open Rel.Lang.Plan Rel.Kernel in
/-- WHERE on `big`'s mask, then CODE and SEGFOLD: the registers of the group count, the keys, the sums. -/
def gsB : Bld (Array Nat) := do
  let some #[.size n, _, _, .bytes k, .bytes v] := valsRegs _ frame.x.rel.val
    | throw "frame.x: its element columns are not dense"
  let n ← lit (.size n); let k ← lit (.bytes k); let v ← lit (.bytes v)
  let big ← maskB (kernel% Kernel.Ew.cmp)
    #[← lit (.u8 Ew.gt), ← lit (.u8 Ew.i64), ← lit (.u8 Ew.va), v, ← lit (.bytes (Rel.one 2)), n] n
  let (m, cs) ← whereB n big #[k, v]
  let #[k, v] := cs | throw "whereB: two columns in, two out"
  groupSumB m k v

open Rel.Lang.Plan in
def gsPlan : Except String Plan := Bld.plan (discard gsB)

open Rel.Lang.Plan in
/-- `Plan.run` of `gsPlan` answers `out`'s count, keys and sums, byte for byte. -/
def gsAgrees : Except String Bool := do
  let (rs, _) ← gsPlan >>= (·.run abiOf)
  let (out, _) ← gsB.run (#[], 0, #[], #[])
  let some #[.size g, _, _, .bytes ks, .bytes ss] := valsRegs _ frame.out.rel.val | throw "frame.out: not dense"
  match out.toList.map fun (i : Nat) => (rs[i]? : Option Plan.Val) with
  | [some (.size r), some (.bytes a), some (.bytes b)] => pure (r == g && a.data == ks.data && b.data == ss.data)
  | _ => throw "gsPlan: its result registers are not a size and two buffers"

#eval show IO Unit from do unless ← IO.ofExcept gsAgrees do throw (IO.userError "gsPlan: its registers differ from frame.out")


-- `out`'s term, read as `planOf` reads it, and the first place the denotation has no rule for it
/-- info: some (Λ, E, thin: the list a set is held as waits for D2's canonical tables (§7.1)) -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  let r ← (Rel.Lang.Expand.read (fun _ => none) [(`Rel.Programs.prelude, Rel.Programs.prelude)] frame).run
  let (ds, _) ← match r with | .ok v => pure v | .error e => throwError "{repr e}"
  let some ⟨_, _, _, t⟩ := ds.lookup "out" | throwError "frame has no closed `out`"
  Lean.logInfo m!"{t.gap}"

end Rel.Lang.TestFrame
