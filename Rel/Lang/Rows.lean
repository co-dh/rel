import Rel.Lang.GenSpec
import Rel.Run.Lang.Compile

/-! The rows of `prims` with their meanings and lemmas (`doc/rel-denotation-design.md` §1.3): each row's code
    (`RowCode`, in `Compile`) beside the relation it computes, the proof type-checked where the row is written. -/

namespace Rel.Lang

open Tab Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc


/-- The code `c` computes the meaning `s`, the two at the same objects (a meaning at other objects would let a row
    read its code at one pair of objects and its meaning at another). -/
def Code.Sound (c : Code) (s : Sem) : Prop :=
  ∀ X Y e (f : Fn e X Y), c = ⟨X, Y, e, f⟩ → ∃ T, s = ⟨X, Y, T⟩ ∧ Gen.Sound f T


/-- The codes `cs` compute the meanings `ss`, position by position. -/
def Code.Sounds : List Code → List Sem → Prop
  | [], [] => True
  | c :: cs, s :: ss => Code.Sound c s ∧ Code.Sounds cs ss
  | _, _ => False

/-- The lemma of the row `rowDens[i]`, at its object variables `σ`: given arguments whose codes compute their
    meanings, the row's code computes its meaning (the one `Tm.den` reads). -/
structure Row where
  i : Fin rowDens.length
  sound : ∀ σ (cs : List Code) (ss : List Sem), Code.Sounds cs ss →
    ∀ f, rowDens[i].1.run σ cs = some f → Gen.Sound f (rowDens[i].2 σ ss)

/-- A row with no relation argument is sound where its code is, at every `σ`. -/
theorem RowCode.plain_sound {sym : String} {ty : List Obj → Obj × Obj} {f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2}
    {T : (σ : List Obj) → Den (ty σ).1 (ty σ).2} (h : ∀ σ, Gen.Sound (f σ) (T σ)) (σ : List Obj) (cs : List Code)
    (ss : List Sem) (_ : Code.Sounds cs ss) (g : Fn true (ty σ).1 (ty σ).2)
    (hg : (RowCode.plain sym ty f).run σ cs = some g) : Gen.Sound g (T σ) := by
  simp only [RowCode.plain] at hg
  split at hg
  · cases hg; exact h σ
  · cases hg

/-- A row with no relation argument, the lemma `h` of its meaning `T`. -/
def Row.plain (i : Fin rowDens.length) {sym : String} {ty : List Obj → Obj × Obj}
    {f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2} {T : (σ : List Obj) → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.plain sym ty f, fun σ _ => T σ⟩) (h : ∀ σ, Gen.Sound (f σ) (T σ)) : Row :=
  ⟨i, by rw [e]; exact fun σ cs ss hs => RowCode.plain_sound h σ cs ss hs⟩

/-- A row with one relation argument is sound where its code is sound given its argument's. -/
theorem RowCode.unary_sound {sym : String} {ty par : List Obj → Obj × Obj}
    {f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (par σ).1 (par σ).2 → Den (ty σ).1 (ty σ).2}
    (h : ∀ σ e (R : Fn e (par σ).1 (par σ).2) T, Gen.Sound R T → Gen.Sound (f σ e R) (D σ T)) (σ : List Obj) :
    ∀ (cs : List Code) (ss : List Sem), Code.Sounds cs ss → ∀ (g : Fn true (ty σ).1 (ty σ).2),
      (RowCode.unary sym ty par f).run σ cs = some g → Gen.Sound g (Sem.one (D σ) ss)
  | [⟨X, Y, e, R⟩], [_], ⟨hc, _⟩, g, hg => by
    obtain ⟨T, rfl, hR⟩ := hc X Y e R rfl
    simp only [RowCode.unary, Code.at] at hg
    split at hg
    · rename_i hXY; obtain ⟨rfl, rfl⟩ := hXY
      cases hg; simpa [Sem.one] using h σ e R T hR
    · cases hg
  | [], _, _, _, hg | _ :: _ :: _, _, _, _, hg => by simp [RowCode.unary] at hg
  | [_], [], hs, _, _ | [_], _ :: _ :: _, hs, _, _ => by simp [Code.Sounds] at hs

/-- A row with one relation argument, the lemma `h` of its meaning `D` of the argument's. -/
def Row.unary (i : Fin rowDens.length) {sym : String} {ty par : List Obj → Obj × Obj}
    {f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (par σ).1 (par σ).2 → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.unary sym ty par f, fun σ => Sem.one (D σ)⟩)
    (h : ∀ σ e (R : Fn e (par σ).1 (par σ).2) T, Gen.Sound R T → Gen.Sound (f σ e R) (D σ T)) : Row :=
  ⟨i, by rw [e]; exact fun σ => RowCode.unary_sound h σ⟩

/-- A row whose argument is a pair test, the lemma `h` of its meaning `D` of the test's at a test run on demand
    (one not on demand has no code: `RowCode.test`). -/
def Row.test (i : Fin rowDens.length) {sym : String} {ty : List Obj → Obj × Obj}
    {f : (σ : List Obj) → Fn true (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.test sym ty f, fun σ => Sem.one (D σ)⟩)
    (h : ∀ σ Q T, Gen.Sound Q T → Gen.Sound (f σ Q) (D σ T)) : Row :=
  .unary i e fun σ e Q T hQ => by
    cases e
    · exact fun _ => trivial
    · exact h σ Q T hQ

/-- Every row of `prims` with a lemma, by its index in `rowDens`. `rowGaps` lists the rest. -/
def rows : List Row :=
  [.plain ⟨0, by decide⟩ rfl fun _ => τ_sound, .plain ⟨1, by decide⟩ rfl fun _ => cons_sound,
   .plain ⟨2, by decide⟩ rfl fun _ => mem_sound, .plain ⟨3, by decide⟩ rfl fun _ => inl_sound,
   .plain ⟨4, by decide⟩ rfl fun _ => inr_sound, .unary ⟨5, by decide⟩ rfl fun _ _ _ _ => map_sound,
   .unary ⟨6, by decide⟩ rfl fun _ _ _ _ => filter_sound, .unary ⟨7, by decide⟩ rfl fun _ _ _ _ => takewhile_sound,
   .test ⟨8, by decide⟩ rfl fun _ _ _ => thinL_sound, .test ⟨9, by decide⟩ rfl fun _ _ _ => merge_sound,
   .unary ⟨10, by decide⟩ rfl fun _ _ _ _ => loop_sound, .plain ⟨11, by decide⟩ rfl fun _ => uncons_sound,
   .plain ⟨12, by decide⟩ rfl fun _ => length_sound, .plain ⟨13, by decide⟩ rfl fun _ => sum_sound,
   .plain ⟨14, by decide⟩ rfl fun _ => inits_sound, .plain ⟨15, by decide⟩ rfl fun _ => tails_sound,
   .plain ⟨16, by decide⟩ rfl fun _ => prefix_sound, .plain ⟨17, by decide⟩ rfl fun _ => suffix_sound,
   .plain ⟨18, by decide⟩ rfl fun _ => concat_sound, .plain ⟨19, by decide⟩ rfl fun _ => cat_sound,
   .plain ⟨20, by decide⟩ rfl fun _ => uncat_sound, .plain ⟨21, by decide⟩ rfl fun _ => zip_sound,
   .plain ⟨22, by decide⟩ rfl fun _ => snoc_sound, .plain ⟨23, by decide⟩ rfl fun _ => unsnoc_sound,
   .plain ⟨25, by decide⟩ rfl fun _ => distinct_sound, .plain ⟨27, by decide⟩ rfl fun _ => tic_sound]

/-- The rows of `prims` with no `Row`: `setify` and `asc`. Each one's meaning is the composition `perm ≫ ord` of
    the permutations with the coreflexive of the ordered lists (`setify` after `distinct`), but `rep_setify` and
    `rep_asc` give it only at an object with `Obj.Ordered` (a float atom is not: NaN), and only one way: they state
    the table's lists are sorted permutations, not that every sorted permutation is in the table, so the `↔` of
    `Gen.Sound` also needs the sorted permutation unique (antisymmetry of `¬ lt`), which no lemma states. -/
def rowGaps : List String := ["setify", "asc"]

/-- The first node of `t` that `compile_sound` has no case for, with why (`doc/rel-denotation-design.md` §7);
    `none` where every node has one. -/
def Tm.gap : {A B : Obj} → {d : Bool} → Tm A B d → Option String
  | _, _, _, .lam _ | _, _, _, .E _ | _, _, _, .thin _ =>
    some "Λ, E, thin: the list a set is held as waits for D2's canonical tables (§7.1)"
  | _, _, _, .hylo .. => some "hylo: its rounds equal lfp only by den_local, which is not proved (§7.2)"
  | _, _, _, .call .. => some "call: a generic definition's term waits for stage 5"
  | _, _, _, .prim r => if rowGaps.contains r.sym then some s!"{r.sym}: the row has no lemma (rowGaps)" else none
  | _, _, _, .mu k _ _ b =>
    if b.pol true k then b.gap else some s!"μ: the body is not positive in its variable {k} (D8 = R, §7.3)"
  | _, _, _, .nu k S b =>
    if b.pol true k then S.gap <|> b.gap else some s!"ν: the body is not positive in its variable {k} (D8 = R, §7.3)"
  | _, _, _, .foldI .. => some "foldI: Gen.foldI has no lemma (foldI_sound) yet"
  -- `share` is a part computed once and reused (numbered by `Expand.number`, its code memoised by `Out.memo`, left
  -- alone by `Tm.subst`), so the part must be closed: the meaning reads `Val.empty` and a part with a free variable
  -- is the code's fault, recomputed under each binding, never a meaning that should read `ρ`
  | _, _, _, .share _ R => if R.fv.isEmpty then R.gap else some "share: its part is not closed"
  | _, _, _, .top R | _, _, _, .conv R | _, _, _, .dom R | _, _, _, .ran R | _, _, _, .est R | _, _, _, .own R
  | _, _, _, .succ R | _, _, _, .arith _ R | _, _, _, .leq R | _, _, _, .lt R
  | _, _, _, .flat R => R.gap
  | _, _, _, .comp R S | _, _, _, .meet R S | _, _, _, .join R S | _, _, _, .diff R S | _, _, _, .pair R S
  | _, _, _, .prod R S | _, _, _, .junc R S | _, _, _, .juncD R S | _, _, _, .foldr R S | _, _, _, .fold R S
  | _, _, _, .arg R S =>
    R.gap <|> S.gap
  | _, _, _, .ldiv R S U V | _, _, _, .rdiv R S U V => R.gap <|> S.gap <|> U.gap <|> V.gap
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .zero | _, _, _, .id | _, _, _, .outl | _, _, _, .outr
  | _, _, _, .nil | _, _, _, .atPos _ | _, _, _, .var _ => none

-- every entry of `rowDens` has its `Row` or is a gap, never both: the obligations are the indices of `rowDens`, not `rows`
example : ((List.range rowDens.length).all fun i =>
    (rows.any (·.i.val == i)) != rowGaps.contains ((rowDens[i]?.map (·.1.sym)).getD "")) = true := by decide

end Rel.Lang
