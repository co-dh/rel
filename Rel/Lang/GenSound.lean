import Rel.Lang.GenKFold
import Rel.RepWhere
import Rel.RepAsc
import Rel.RepSums
import Rel.Lang.GenKEst
import Rel.Lang.GenKFix
import Rel.Lang.GenKHylo
import Rel.Lang.Den
import Rel.Run.Lang.TmGen
import Rel.RepCast

/-! `Tm.gen`: `Expand.node` as a Lean function from a term to its `GenK` code, one `GenK` op per constructor with
    `Expand.node`'s argument order, and `Tm.code` as `Expand.code` (a closed part memoised, `GenK.memo`). Then
    `Tm.gen_sound`: on every term, under `Sound`, the code represents `Tm.den` in every context (an error table
    represents anything: where `Tm.hasCode` is false the run fails), each case one `GenK.*_sound` (`GenKSpec`, `GenKBits`). A bit matrix the code passes on is `Rel.Wf`
    (`Tm.gen_wf`) (`Tab.ofBits` reads back what `compSelM`, `compTabMat`, `ldivTabMat` build); the order law of each
    `Λ` is a theorem (`Vals.lamLaw`: `kasc`'s order is `Obj.lt`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Every bit matrix `η` holds is `Rel.Wf`: each variable's code at every objects, and each slot's. -/
def Code.Wf (η : Code) : Prop := (∀ k A B, (η k A B).Wf) ∧ ∀ x ∈ η.sh, x.2.2.Wf

/-- The code environment `η` represents the meaning environment `ρ`, at every variable and object, in every
    context, and every bit matrix it holds is `Rel.Wf`. -/
def Sound (η : Code) (ρ : Val) : Prop := (∀ k A B K, (η k A B).Reps K (ρ k A B)) ∧ η.Wf

/-- The slot `k` of the table `σ` at `A ⟶ B`, where it has one, represents the meaning of the closed part `R`
    numbered `k`: what `Tm.gen_sound` asks at each `share k R` (`Tm.GenHyp`), since a slot is computed once, apart
    from the terms that read it (`Code.shares`). -/
def Codes.Shares (σ : Codes) {A B : Obj} (k : Nat) (R : Tm A B) : Prop :=
  ∀ r, σ.at k A B = some r → ∀ K, r.Reps K (R.den Val.empty)

/-- A slot of a table of `Wf` codes is `Wf`. -/
theorem Codes.at_wf {xs : Codes} (hw : ∀ x ∈ xs, x.2.2.Wf) {i : Nat} {X Y : Obj} {r : Rel X Y}
    (h : xs.at i X Y = some r) : r.Wf := by
  unfold Codes.at at h
  split at h
  · rename_i X' Y' x hx
    split at h
    · rename_i ho; obtain ⟨rfl, rfl⟩ := ho; cases h; exact hw _ (List.mem_of_getElem? hx)
    · cases h
  · cases h

/-- `Code.args` keeps `η`'s table. -/
theorem Code.args_sh (η : Code) : ∀ (ks : List Nat) (xs : Codes), (Code.args η ks xs).sh = η.sh
  | k :: ks, ⟨_, _, _⟩ :: xs => Code.args_sh η ks xs
  | [], _ | _ :: _, [] => rfl

/-- `η` with `k` bound to a `Wf` code `r` that represents `X` represents `ρ` with `k` bound to `X`: a fixed point's
    round (`GenK.const` of its table) or a call's argument (`Sound.args`). -/
theorem Sound.bind {η : Code} {ρ : Val} (hs : Sound η ρ) (k : Nat) {A B : Obj} {r : Rel A B} {X : Den A B}
    (hr : ∀ K, r.Reps K X) (hw : r.Wf) : Sound (η.bind k r) (ρ.bind k X) := by
  refine ⟨fun j A' B' K => ?_, fun j A' B' => ?_, hs.2.2⟩
  · by_cases hj : j = k
    · simp only [Code.bind, Val.bind, hj, if_true]
      by_cases ho : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := ho
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]; exact hr K
      · rw [dif_neg ho, dif_neg ho]; exact GenK.zero_sound K
    · simp only [Code.bind, Val.bind, hj, if_false]; exact hs.1 j A' B' K
  · by_cases hj : j = k
    · simp only [Code.bind, hj, if_true]
      by_cases ho : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := ho; rw [dif_pos ⟨rfl, rfl⟩]; exact hw
      · rw [dif_neg ho]; trivial
    · simp only [Code.bind, hj, if_false]; exact hs.2.1 j A' B'

/-- **A program's run-time names bound in statement order** (IO design A.3, the environment `n.io` computes in):
    each `(k, A, B, r, X)` of `bs` bound in turn, `r` a `Wf` code that represents `X` (an input's table,
    `GenK.val_sound`; a run-time definition's code, `Tm.gen_sound` of its body at the names before it), leaves the
    environment sound; then `Tm.gen_sound` of an output's term gives that its table represents its meaning. -/
theorem Sound.inputs {η : Code} {ρ : Val} (hs : Sound η ρ) :
    ∀ bs : List (Nat × (A : Obj) × (B : Obj) × (Rel A B × Den A B)),
      (∀ b ∈ bs, (∀ K, b.2.2.2.1.Reps K b.2.2.2.2) ∧ b.2.2.2.1.Wf) →
      Sound (bs.foldl (fun η b => η.bind b.1 b.2.2.2.1) η) (bs.foldl (fun ρ b => ρ.bind b.1 b.2.2.2.2) ρ)
  | [], _ => hs
  | b :: bs, h => Sound.inputs (hs.bind b.1 (h b (.head _)).1 (h b (.head _)).2) bs fun c hc => h c (.tail _ hc)

/-- `Code.args` over a `Wf` `η` is `Wf` when every argument is. -/
theorem Code.args_wf {η : Code} (hη : η.Wf) :
    ∀ (ks : List Nat) (xs : Codes), (∀ x ∈ xs, x.2.2.Wf) → (Code.args η ks xs).Wf
  | k :: ks, ⟨X, Y, x⟩ :: xs, hw => by
    have ih := Code.args_wf hη ks xs fun y hy => hw y (List.mem_cons_of_mem _ hy)
    refine ⟨fun j A' B' => ?_, ih.2⟩
    simp only [Code.args, Code.bind]
    split
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hw _ List.mem_cons_self
      · trivial
    · exact ih.1 j A' B'
  | [], _, _ | _ :: _, [], _ => ⟨fun _ _ _ => trivial, hη.2⟩

/-- The rows whose case of `Tm.gen_sound` is proved (`rowsProved_ok`); `rowGens_proved` checks every row of
    `rowGens` is one. -/
def rowsProved : List String :=
  ["∋", "inl", "inr", "τ", "setify", "snoc", "cons", "cat", "uncat", "prefix", "suffix", "uncons", "unsnoc", "inits",
   "zip", "length", "sum", "loop", "filter", "concat", "merge", "thinL", "F", "positions", "asc", "inl°", "inr°",
   "tails", "takewhile", "sums", "flat", "$"] ++ floatOps.map (·.1)

/-- What `Tm.gen_sound` asks of `t`: the body of each fixed point positive in its variable (`Tm.pol`, which
    `Tm.den_mono` reads), and `P k R` at each `share k R` (its slot, `Codes.Shares`). `Λ`'s order law asks nothing,
    since it is a theorem (`Vals.lamLaw`). -/
def Tm.GenHyp (P : {A B : Obj} → Nat → Tm A B → Prop) : {A B : Obj} → Tm A B → Prop
  | _, _, .share k R => P k R ∧ R.GenHyp P
  | _, _, .lam R | _, _, .E R | _, _, .thin R | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R
  | _, _, .own R | _, _, .succ R | _, _, .arith _ _ R | _, _, .leq _ R | _, _, .lt _ R | _, _, .est R
  | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.GenHyp P
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .arg R S => R.GenHyp P ∧ S.GenHyp P
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.GenHyp P ∧ S.GenHyp P ∧ U.GenHyp P ∧ V.GenHyp P
  | _, _, .nu k S b => b.pol true k = true ∧ S.GenHyp P ∧ b.GenHyp P
  -- the children's term asks no more than the body (`Tm.genHyp_kids`)
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k = true ∧ b.GenHyp P
  -- every other constructor spelled out: a catch-all's equation lemmas time `simp` out
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. | _, _, .prim _ => True

/-- `Tm.GenHyp` with nothing asked at a `share` (`Tm.monoOK_iff`): what `GenSoundTest` evaluates beside
    `Tm.hasCode`. -/
def Tm.monoOK : {A B : Obj} → Tm A B → Bool
  | _, _, .lam R | _, _, .E R | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ _ R | _, _, .leq _ R | _, _, .lt _ R | _, _, .share _ R
  | _, _, .est R | _, _, .thin R | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.monoOK
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .arg R S => R.monoOK && S.monoOK
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.monoOK && S.monoOK && U.monoOK && V.monoOK
  | _, _, .nu k S b => b.pol true k && S.monoOK && b.monoOK
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k && b.monoOK
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. | _, _, .prim _ => true

theorem Tm.monoOK_iff {A B : Obj} (t : Tm A B) : t.monoOK = true ↔ t.GenHyp fun _ _ => True := by
  induction t <;> simp [Tm.monoOK, Tm.GenHyp, and_assoc, *]

/-- The children's term of `t` (`Tm.kids`) asks no more than `t`: `kids` builds it of `t`'s parts, `𝟙`, `𝟘`, `∪`,
    `juncD` and `∋`, none of which asks anything. -/
theorem Tm.genHyp_kids {P : {A B : Obj} → Nat → Tm A B → Prop} (k : Nat) (A : Obj)
    {C D : Obj} (t : Tm C D) (h : t.GenHyp P) : ((t.kids k A).getD .zero).GenHyp P := by
  induction t
  case arg f x _ _ =>
    cases f <;> unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;>
      simp_all (config := {decide := true}) [Tm.GenHyp, memRow]
  all_goals unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> (try subst_vars) <;>
    simp_all [Tm.GenHyp]

namespace GenK

theorem memo_sound {A B : Obj} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.memo A B R).Reps K X := fun K => by
  cases R with
  | tab t => exact hR K
  | lazy f =>
    simp only [GenK.memo]; split
    next t h =>
      refine (reps_iff _ _ _).2 fun t' h' x y _ _ _ => ?_
      cases h'; exact (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl trivial
    next => exact hR K
  | bits => exact (reps_iff _ _ _).2 fun t h x y _ _ _ => (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl trivial

theorem memo_wf {A B : Obj} {R : Rel A B} (h : R.Wf) : (GenK.memo A B R).Wf := by
  cases R with
  | lazy f => simp only [GenK.memo]; split <;> first | trivial | exact h
  | _ => trivial

end GenK

theorem Tm.code_of {η : Code} {A B : Obj} {t : Tm A B} {X : Core.Rel A.El B.El} (h : ∀ K, (t.gen η).Reps K X) :
    ∀ K, (t.code η).Reps K X := by
  unfold Tm.code
  -- the condition held abstract: `split` would split the `matches` inside it
  suffices ∀ (c : Prop) [Decidable c], ∀ K, (if c then GenK.memo A B (t.gen η) else t.gen η).Reps K X from this _
  intro c _; split
  all_goals first | exact GenK.memo_sound h | exact h

/-! ### The rows: `Prim.den` unfolded once, then one `Tab` law per row -/

/-- The codes `xs` represent the meanings `ss`, one for one at the same objects, in every context. -/
def CodesRep : Codes → List Sem → Prop
  | [], [] => True
  | ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss =>
    (if h : X' = X ∧ Y' = Y then ∀ K, x.Reps K (h.1 ▸ h.2 ▸ T) else False) ∧ CodesRep xs ss
  | _, _ => False

/-- `Wf` codes `xs` that represent `ss`, bound at `ks`, represent `ss` bound at `ks`: what a call's body is built
    and read under (`Sound.bind` per argument). -/
theorem Sound.args {η : Code} {ρ : Val} (hs : Sound η ρ) : ∀ (ks : List Nat) (xs : Codes) (ss : List Sem),
    (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss → Sound (Code.args η ks xs) (Val.args ks ss)
  | k :: ks, ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss, hw, hr => by
    simp only [CodesRep] at hr
    split at hr
    · rename_i h; obtain ⟨rfl, rfl⟩ := h
      exact (Sound.args hs ks xs ss (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hr.2).bind k hr.1
        (hw _ List.mem_cons_self)
    · exact hr.1.elim
  | [], _, _, _, _ | _ :: _, [], [], _, _ => ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial, hs.2.2⟩
  | _ :: _, [], _ :: _, _, hr | _ :: _, _ :: _, [], _, hr => by simp [CodesRep] at hr

/-- Row `s`'s cases of `Tm.gen_wf` and `Tm.gen_sound`: at every objects, given as many relation codes `xs` as it
    takes, each `Wf`, its code is `Wf`, and represents its meaning of any `ss` that `xs` represent. -/
def RowOK (s : String) : Prop := ∀ (r : Prim) (A B : Obj) (xs : Codes), r.sym = s → xs.length = rowArity s →
  (∀ x ∈ xs, x.2.2.Wf) → (primGen r A B xs).Wf ∧ ∀ ss, CodesRep xs ss →
    ∀ K, (primGen r A B xs).Reps K (Prim.den r A B ss)

/-- `Prim.den` and `primGen` unfolded through the `rowDens` and `rowGens` lookups: a row is `RowOK` when its
    generated code at each `σ` and `xs` is `Wf`, and at the row's objects `c.ty σ` represents its meaning `D σ ss`
    of the `ss` that `xs` represent. -/
theorem rowOK_args {s : String} {c : RowCode} {D : RowDen c}
    {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (xs : Codes) (A B : Obj) (v : Rel A B), r.sym = s → xs.length = rowArity s →
      (∀ x ∈ xs, x.2.2.Wf) → f σ xs = some ⟨A, B, v⟩ → v.Wf ∧ ∀ ss, CodesRep xs ss →
        ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, v.Reps K (hc.1 ▸ hc.2 ▸ D σ ss)) : RowOK s := by
  intro r A B xs hs hn hw
  have err (e : String) (X : List Sem → Den A B) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss,
      CodesRep xs ss → ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K (X ss) :=
    ⟨trivial, fun _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
  unfold primGen Prim.den; rw [hs, if_neg fun h => h hn, hf, hD]
  cases hσ : r.objs A B with
  | none => exact err _ _
  | some σ =>
    dsimp only; split
    · next A' B' v hv =>
      split
      · next he =>
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hw, hR⟩ := h r σ xs A' B' v hs hn hw hv
        refine ⟨hw, fun ss hss K => ?_⟩
        obtain ⟨hc, hR⟩ := hR ss hss
        rw [dif_pos hc]; exact hR K
      · exact err _ _
    · exact err _ _

/-- `rowOK_args` for a row given no relation (`rowArity s = 0`): only `xs = ss = []`. -/
theorem rowOK_of {s : String} {c : RowCode} {D : RowDen c} {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (A B : Obj) (v : Rel A B), r.sym = s → f σ [] = some ⟨A, B, v⟩ → v.Wf ∧
      ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, v.Reps K (hc.1 ▸ hc.2 ▸ D σ []))
    (h0 : rowArity s = 0 := by decide) : RowOK s :=
  rowOK_args hD hf fun r σ xs A B v hs hn _ hv => by
    cases xs with
    | cons => simp [h0] at hn
    | nil =>
      obtain ⟨hw, hR⟩ := h r σ A B v hs hv
      refine ⟨hw, fun ss hss => ?_⟩
      cases ss with
      | nil => exact hR
      | cons => simp [CodesRep] at hss

theorem rowOK_mem : RowOK "∋" := rowOK_of (c := RowCode.mem) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h⟩⟩

theorem rowOK_inl : RowOK "inl" := rowOK_of (c := RowCode.inl) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inl_holds h⟩⟩

theorem rowOK_inr : RowOK "inr" := rowOK_of (c := RowCode.inr) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inr_holds h⟩⟩

theorem rowOK_inlC : RowOK "inl°" := rowOK_of (c := RowCode.inlC) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inlConv_holds h⟩⟩

theorem rowOK_inrC : RowOK "inr°" := rowOK_of (c := RowCode.inrC) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inrConv_holds h⟩⟩

theorem rowOK_tau : RowOK "τ" := rowOK_of (c := RowCode.tau) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tau_den h⟩

theorem rowOK_setify : RowOK "setify" := rowOK_of (c := RowCode.setify) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.setify_den h⟩

/-- An array is below itself extended by a non-empty one (`Obj.lt` on `[B]`: a proper prefix first). -/
theorem arr_lt_append (B : Obj) : ∀ (xs ys : List B.El), ys ≠ [] → (Obj.arr B).lt xs (xs ++ ys)
  | [], [], h => (h rfl).elim
  | [], y :: ys, _ => Obj.lt_nil_cons B y ys
  | x :: xs, ys, h => (Obj.lt_cons B x x xs (xs ++ ys)).2 (Or.inr ⟨rfl, arr_lt_append B xs ys h⟩)

/-- A shorter prefix of `xs` is below a longer one (`Obj.lt` on `[B]`). -/
theorem arr_lt_take (B : Obj) (xs : List B.El) {i j : Nat} (hij : i < j) (hj : j ≤ xs.length) :
    (Obj.arr B).lt (xs.take i) (xs.take j) := by
  have h := arr_lt_append B (xs.take i) ((xs.take j).drop i) fun h0 => by
    have := congrArg List.length h0; simp at this; omega
  have e : xs.take i ++ (xs.take j).drop i = xs.take j := by
    have t := List.take_append_drop i (xs.take j)
    rwa [List.take_take, Nat.min_eq_left (by omega)] at t
  rwa [e] at h

/-- **`Λ(T)` at `a` is `L`** when `L` ascends strictly in `Obj.lt` and its members are the image of `a` under `T`. -/
theorem lamDen_eq {A B : Obj} {T : Den A B} {a : A.El} {L : List B.El} (hL : L.Pairwise B.lt)
    (hm : ∀ b, b ∈ L ↔ T a b) (zs : List B.El) : lamDen T a zs ↔ zs = L :=
  ⟨fun ⟨hp, hz⟩ => pairwise_eq_of_mem (Obj.lt_irrefl _) (fun _ _ => Obj.lt_asymm _) hp hL
    fun b => (hz b).trans (hm b).symm, fun h => h ▸ ⟨hL, hm⟩⟩

/-- **`Λ(cat°)` at `xs`**: the one list strictly ascending in `Obj.lt` of the splits `(p₁, p₂)` of `xs` is the splits by
increasing split point, since a shorter first part is a proper prefix of a longer one. -/
theorem lamDen_splits {B : Obj} {T : Den (.arr B) (.prod (.arr B) (.arr B))} (xs : List B.El)
    (hT : ∀ p, T xs p ↔ xs = p.1 ++ p.2) (zs : List (Obj.prod (.arr B) (.arr B)).El) :
    lamDen T xs zs ↔ zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) :=
  lamDen_eq ((pairwise_map_range_iff _ _ _).2 fun _ _ hij hj =>
    (Obj.lt_prod _ _ _ _ _ _).2 (Or.inl (arr_lt_take B xs hij (by omega)))) (fun p => by
    rw [hT, List.mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩; exact (List.take_append_drop k xs).symm
    · intro h; subst h; exact ⟨p.1.length, by simp; omega, by simp⟩) zs

/-- **`Λ(prefix)` at `xs`**: the one list strictly ascending in `Obj.lt` of the prefixes of `xs` is its prefixes by
increasing length. -/
theorem lamDen_inits {B : Obj} {T : Den (.arr B) (.arr B)} (xs : List B.El) (hT : ∀ ys, T xs ys ↔ ys <+: xs)
    (zs : List (List B.El)) : lamDen T xs zs ↔ zs = (List.range (xs.length + 1)).map fun k => xs.take k :=
  lamDen_eq ((pairwise_map_range_iff _ _ _).2 fun _ _ hij hj => arr_lt_take B xs hij (by omega)) (fun ys => by
    rw [hT, List.mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩; exact List.take_prefix k xs
    · intro h
      exact ⟨ys.length, List.mem_range.2 (Nat.lt_succ_of_le h.length_le), (List.prefix_iff_eq_take.1 h).symm⟩) zs

/-- **`tails` on the cells `X`** (`Tab.tails`) = `Λ(cat°) ≫ F(π₂)`: each array of `X` to its suffixes by decreasing
length. -/
theorem Tab.tails_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.tails X = .ok T) (xs : List B.El)
    (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  unfold Tab.tails at h
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨L, hL, h⟩ := GenK.bind_ok h
  rcases L with ⟨N, key, m, lo, hi, f⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- the cells of `⟨m, lo, hi, f.2⟩` are those of `⟨m, lo, hi, f⟩` mapped by `Prod.snd`
  have hrow : ∀ i, Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, f.2⟩ i =
      (Vals.row (A := .arr (.prod (.arr B) (.arr B))) ⟨m, lo, hi, f⟩ i).map Prod.snd := fun i => by
    rw [Vals.row_arr, Vals.row_arr, List.map_map]
    congr 1; funext k; simp only [Function.comp_apply, apply_dite Prod.snd]; rfl
  have hs : ∀ (hx : ∃ i, X.row i = xs) zs, lamDen U.Holds xs zs ↔
      zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) :=
    fun hx => lamDen_splits xs fun p => (Tab.uncat_holds hU xs p).trans (and_iff_right hx)
  constructor
  · rintro ⟨i, hk, hv⟩
    obtain ⟨hx, hd⟩ := (Tab.lam_den hL xs _).1 ⟨i, hk, rfl⟩
    refine ⟨hx, ?_⟩
    rw [← hv, hrow, (hs hx _).1 hd, List.map_map]; rfl
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hk, hv⟩ := (Tab.lam_den hL xs _).2 ⟨hx, (hs hx _).2 rfl⟩
    exact ⟨i, hk, by rw [hrow]; simp only at hv; rw [hv, List.map_map]; rfl⟩

theorem rowOK_tails : RowOK "tails" := rowOK_of (c := RowCode.tails) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tails_den h⟩

/-- A row run after the keys (`GenK.after`) represents `P` when `f D`, on the keys' coreflexive `D`, holds `D ≫ P`. -/
theorem GenK.after_row_sound {A B : Obj} {f : {K : Obj} → Tab K A → Except String (Tab K B)}
    {P : Core.Rel A.El B.El}
    (hf : ∀ {K : Obj} (D : Tab K A) t, f D = .ok t → ∀ k b, t.Holds k b ↔ ∃ a, D.Holds k a ∧ P a b) :
    ∀ K, (GenK.after A B f).Reps K P :=
  GenK.ofVals_row_sound fun _ X t h a b => by
    cases hD : Tab.idU X with
    | error e => rw [hD] at h; exact nomatch h
    | ok D =>
    rw [hD] at h
    rw [hf D t h]
    constructor
    · rintro ⟨a', ha', hp⟩; obtain ⟨rfl, hx⟩ := (Tab.idU_holds hD a a').1 ha'; exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩; exact ⟨a, (Tab.idU_holds hD a a).2 ⟨rfl, hx⟩, hp⟩

theorem rowOK_snoc : RowOK "snoc" := rowOK_of (c := RowCode.snoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.snoc_holds h⟩⟩

theorem rowOK_cons : RowOK "cons" := rowOK_of (c := RowCode.cons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.cons_holds h⟩⟩

theorem rowOK_cat : RowOK "cat" := rowOK_of (c := RowCode.cat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.cat_holds h⟩⟩

theorem rowOK_uncat : RowOK "uncat" := rowOK_of (c := RowCode.uncat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.uncat_holds h⟩⟩

/-- **`cat° ≫ graph f`** on the cells `X` (`Tab.prefix`, `Tab.suffix`): `uncat`'s splits composed with a table `g` of
them that holds `graph f`. -/
theorem Tab.uncat_comp_holds {B : Obj} {n : USize} {X : Vals (.arr B) n}
    {g : {m : USize} → Vals (.prod (.arr B) (.arr B)) m → Except String (Tab (.prod (.arr B) (.arr B)) (.arr B))}
    {f : (Obj.prod (.arr B) (.arr B)).El → List B.El}
    (hg : ∀ m (P : Vals (.prod (.arr B) (.arr B)) m) t, g P = .ok t → ∀ p ys,
      t.Holds p ys ↔ (∃ i, P.row i = p) ∧ Core.Rel.graph f p ys)
    {T : Tab (.arr B) (.arr B)} (h : (do let u ← Tab.uncat X; u.comp (← g u.val)) = .ok T) (xs ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ∃ p : (Obj.prod (.arr B) (.arr B)).El, xs = p.1 ++ p.2 ∧ ys = f p := by
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨G, hG, h⟩ := GenK.bind_ok h
  rw [Tab.comp_holds h]
  constructor
  · rintro ⟨p, hp, hq⟩
    exact ⟨((Tab.uncat_holds hU xs p).1 hp).1, p, ((Tab.uncat_holds hU xs p).1 hp).2, ((hg _ _ _ hG p ys).1 hq).2⟩
  · rintro ⟨hx, p, he, rfl⟩
    have hp := (Tab.uncat_holds hU xs p).2 ⟨hx, he⟩
    obtain ⟨i, -, hv⟩ := hp
    exact ⟨p, (Tab.uncat_holds hU xs p).2 ⟨hx, he⟩, (hg _ _ _ hG p _).2 ⟨⟨i, hv⟩, rfl⟩⟩

/-- **`prefix`** (`Tab.prefix`) = `cat° ≫ π₁`: each array of `X` to its initial segments. -/
theorem Tab.prefix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.prefix X = .ok T) (xs ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <+: xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outl P) (f := Prod.fst) (fun _ _ _ h => Tab.outl_holds h) h]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.2, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(ys, t), ht.symm, rfl⟩⟩

/-- **`suffix`** (`Tab.suffix`) = `cat° ≫ π₂`: each array of `X` to its final segments. -/
theorem Tab.suffix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.suffix X = .ok T) (xs ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <:+ xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outr P) (f := Prod.snd) (fun _ _ _ h => Tab.outr_holds h) h]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.1, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(t, ys), ht.symm, rfl⟩⟩

theorem rowOK_prefix : RowOK "prefix" := rowOK_of (c := RowCode.prefix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.prefix_holds h⟩⟩

theorem rowOK_suffix : RowOK "suffix" := rowOK_of (c := RowCode.suffix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.suffix_holds h⟩⟩

theorem rowOK_uncons : RowOK "uncons" := rowOK_of (c := RowCode.uncons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.uncons_holds h⟩⟩

theorem rowOK_unsnoc : RowOK "unsnoc" := rowOK_of (c := RowCode.unsnoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.unsnoc_holds h⟩⟩

/-- **`inits` on the cells `X`** (`Tab.inits`) = `Λ(prefix)`: each array of `X` to its prefixes by increasing length. -/
theorem Tab.inits_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.inits X = .ok T) (xs : List B.El) (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  unfold Tab.inits at h
  obtain ⟨P, hP, h⟩ := GenK.bind_ok h
  rw [Tab.lam_den h]
  exact and_congr_right fun hx => lamDen_inits xs (fun ys => (Tab.prefix_holds hP xs ys).trans (and_iff_right hx)) yss

theorem rowOK_inits : RowOK "inits" := rowOK_of (c := RowCode.inits) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inits_den h⟩

theorem rowOK_zip : RowOK "zip" := rowOK_of (c := RowCode.zip) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.zip_holds h⟩⟩

theorem rowOK_concat : RowOK "concat" := rowOK_of (c := RowCode.concat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.flatten_holds h⟩⟩

theorem rowOK_length : RowOK "length" := rowOK_of (c := RowCode.length) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.length_holds h⟩⟩

/-- `$` at the objects `σ` names: the graph `castDen`, no ordering hypothesis. -/
theorem rowOK_cast : RowOK "$" := rowOK_of (c := RowCode.cast) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.cast_den h⟩⟩

/-- A `floatOps` row at the object `σ` names: the graph `floatDen` of its `Op`, one case per row. -/
theorem rowOK_float {s : String} (hs : s ∈ floatOps.map (·.1)) : RowOK s := by
  simp only [floatOps, List.map, List.mem_cons, List.not_mem_nil, or_false] at hs
  repeat' (rcases hs with rfl | hs)
  all_goals first | (subst hs) | skip
  -- a row whose `Op` reads one operand runs from `F`, one reading two from `F×F` (`rowDens`)
  all_goals first
    | exact rowOK_of (c := ⟨_, fun σ => (σ₁ σ, σ₂ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
        cases hv
        rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
          exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.floatOp_den rfl h⟩⟩
    | exact rowOK_of (c := ⟨_, fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₂ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
        cases hv
        rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
          exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.floatOp_den rfl h⟩⟩

theorem rowOK_sum : RowOK "sum" := rowOK_of (c := RowCode.sum) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.sum_holds h⟩⟩

theorem rowOK_loop : RowOK "loop" := rowOK_args (c := RowCode.loop) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "loop" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.stepAfter GenK.after; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.loop_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_filter : RowOK "filter" := rowOK_args (c := RowCode.filter) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "filter" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.filter_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_takewhile : RowOK "takewhile" :=
  rowOK_args (c := RowCode.takewhile) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "takewhile" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.takewhile_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_positions : RowOK "positions" :=
  rowOK_args (c := RowCode.positions) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "positions" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.positions_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_asc : RowOK "asc" :=
  rowOK_args (c := RowCode.asc) rfl rfl fun _ σ xs _ _ _ hs hn _ hv => by
  have h1 : rowArity "asc" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.ofRel; exact GenK.lift1_wf _, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss fun _ _ h hr => by subst hr; exact Tab.asc_holds h
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_sums : RowOK "sums" :=
  rowOK_args (c := RowCode.sums) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "sums" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, σ⟩⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.ofRel; exact GenK.lift1_wf _, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss fun _ _ h hr => by subst hr; exact Tab.sums_den h
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_F : RowOK "F" := rowOK_args (c := RowCode.map) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "F" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.map_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `merge(Q)`, `Expand.primE`'s fit of the row (`testAfter`, `Tab.merge`): each `(x, y)` in demand to
`List.merge x y` under `Q`'s meaning `TQ` as the test, `Q` run on the pairs of heads it is asked about (`est`'s rule). -/
theorem GenK.merge_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ) :
    ∀ K, (GenK.testAfter B (.prod (.arr B) (.arr B)) (.arr B) Q fun q P => Tab.merge q P).Reps K
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.after_row_sound fun _ _ h k zs => Tab.merge_holds (fun D _ hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl trivial)
    h k zs

theorem rowOK_merge : RowOK "merge" := rowOK_args (c := RowCode.merge) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "merge" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.testAfter GenK.after; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.merge_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `thinL(Q)`, `Expand.primE`'s fit of the row (`testVals`, `Tab.thinL`): each array in demand to `thinLDen` under
`Q`'s meaning `TQ` as the test, `Q` run on the pairs it is asked about (`est`'s rule). -/
theorem GenK.thinL_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ) :
    ∀ K, (GenK.testVals B (.arr B) (.arr B) Q fun q X => Tab.thinL q X).Reps K
      (thinLDen fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.ofVals_row_sound fun _ _ _ h xs w => Tab.thinL_holds (fun D _ hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl trivial)
    h xs w

theorem rowOK_thinL : RowOK "thinL" := rowOK_args (c := RowCode.thinL) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "thinL" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.testVals; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.thinL_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

/-- `Rᴵ`, `Expand.primE`'s fit of the row (`onKeys`, `Tab.flat`): the `(a', b)` of `R` at the key of each pair in
demand, kept where `a'` is its source, `R` run on the keys in demand. -/
theorem GenK.flat_sound {I A B : Obj} {d : Bool} {R : Rel I (.prod A B)} {X : Core.Rel I.El (Obj.prod A B).El}
    (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.onKeys I A B (.prod A B) d R fun X r => Tab.flat X r).Reps K (flatDen X) :=
  GenK.ofVals_sound fun _ _ Xs _ hK h p b hp _ _ => by
    obtain ⟨r, hr, ht⟩ := GenK.bind_ok h
    have er := (GenK.reps_iff _ _ _).1 (hR _) r hr
    obtain ⟨i, rfl⟩ := (GenK.side_some hK p).1 hp
    exact (Tab.flat_holds ht _ b).trans ((and_iff_right ⟨i, rfl⟩).trans
      (er _ _ ((GenK.side_some rfl _).2 ⟨i, rfl⟩) rfl trivial))

theorem rowOK_flat : RowOK "flat" := rowOK_args (c := RowCode.flat) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "flat" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, σ⟩⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.onKeys; exact GenK.ofVals_wf, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.flat_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

/-- Every row of `rowsProved` is `RowOK`: the obligations enumerated from the list `rowGens_proved` checks. -/
theorem rowsProved_ok (r : Prim) (h : r.sym ∈ rowsProved) : RowOK r.sym := by
  by_cases h1 : r.sym = "∋"; · rw [h1]; exact rowOK_mem
  by_cases h2 : r.sym = "inl"; · rw [h2]; exact rowOK_inl
  by_cases h3 : r.sym = "inr"; · rw [h3]; exact rowOK_inr
  by_cases h4 : r.sym = "τ"; · rw [h4]; exact rowOK_tau
  by_cases h5 : r.sym = "setify"; · rw [h5]; exact rowOK_setify
  by_cases h6 : r.sym = "snoc"; · rw [h6]; exact rowOK_snoc
  by_cases h7 : r.sym = "cons"; · rw [h7]; exact rowOK_cons
  by_cases h8 : r.sym = "cat"; · rw [h8]; exact rowOK_cat
  by_cases h9 : r.sym = "uncat"; · rw [h9]; exact rowOK_uncat
  by_cases h10 : r.sym = "zip"; · rw [h10]; exact rowOK_zip
  by_cases h11 : r.sym = "length"; · rw [h11]; exact rowOK_length
  by_cases h12 : r.sym = "loop"; · rw [h12]; exact rowOK_loop
  by_cases h13 : r.sym = "filter"; · rw [h13]; exact rowOK_filter
  by_cases h14 : r.sym = "concat"; · rw [h14]; exact rowOK_concat
  by_cases h15 : r.sym = "merge"; · rw [h15]; exact rowOK_merge
  by_cases h16 : r.sym = "thinL"; · rw [h16]; exact rowOK_thinL
  by_cases h17 : r.sym = "tails"; · rw [h17]; exact rowOK_tails
  by_cases h18 : r.sym = "sum"; · rw [h18]; exact rowOK_sum
  by_cases h19 : r.sym = "F"; · rw [h19]; exact rowOK_F
  by_cases h20 : r.sym = "positions"; · rw [h20]; exact rowOK_positions
  by_cases h21 : r.sym = "asc"; · rw [h21]; exact rowOK_asc
  by_cases h22 : r.sym = "inl°"; · rw [h22]; exact rowOK_inlC
  by_cases h23 : r.sym = "inr°"; · rw [h23]; exact rowOK_inrC
  by_cases h24 : r.sym = "prefix"; · rw [h24]; exact rowOK_prefix
  by_cases h25 : r.sym = "suffix"; · rw [h25]; exact rowOK_suffix
  by_cases h26 : r.sym = "uncons"; · rw [h26]; exact rowOK_uncons
  by_cases h27 : r.sym = "unsnoc"; · rw [h27]; exact rowOK_unsnoc
  by_cases h28 : r.sym = "inits"; · rw [h28]; exact rowOK_inits
  by_cases h29 : r.sym = "takewhile"; · rw [h29]; exact rowOK_takewhile
  by_cases h30 : r.sym = "sums"; · rw [h30]; exact rowOK_sums
  by_cases h31 : r.sym = "flat"; · rw [h31]; exact rowOK_flat
  by_cases h32 : r.sym = "$"; · rw [h32]; exact rowOK_cast
  by_cases hu : r.sym ∈ floatOps.map (·.1); · exact rowOK_float hu
  simp [rowsProved, hu, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32] at h

/-- Every row `rowGens` has a code for is in `rowsProved`. -/
theorem rowGens_proved {s : String} {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (h : rowGens.lookup s = some f) : s ∈ rowsProved := by
  suffices ∀ l : List (String × (List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B))),
      (∀ p ∈ l, p.1 ∈ rowsProved) → l.lookup s = some f → s ∈ rowsProved from
    this _ (by decide) h
  intro l; induction l with
  | nil => intro _ h; nomatch h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    intro hl h
    simp only [List.lookup] at h
    split at h
    · next he => rw [beq_iff_eq.1 he]; exact hl _ List.mem_cons_self
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h

/-- Every row's code given `Wf` codes is `Wf` and represents its meaning: `RowOK` where it is given as many
    relations as it takes and `rowGens` has it (`rowGens_proved`), an error table elsewhere. -/
theorem primGen_ok (r : Prim) (A B : Obj) (xs : Codes) (hw : ∀ x ∈ xs, x.2.2.Wf) : (primGen r A B xs).Wf ∧
    ∀ ss, CodesRep xs ss → ∀ K, (primGen r A B xs).Reps K (Prim.den r A B ss) := by
  have err (e : String) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss, CodesRep xs ss →
      ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K (Prim.den r A B ss) :=
    ⟨trivial, fun _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
  by_cases hn : xs.length = rowArity r.sym
  · cases hg : rowGens.lookup r.sym with
    | some f => exact rowsProved_ok r (rowGens_proved hg) r A B xs rfl hn hw
    | none => unfold primGen; rw [if_neg fun h => h hn, hg]; exact err _
  · unfold primGen; rw [if_pos hn]; exact err _

theorem Tm.code_wf {η : Code} {A B : Obj} {t : Tm A B} (h : (t.gen η).Wf) : (t.code η).Wf := by
  unfold Tm.code
  -- the condition held abstract: `split` would split the `matches` inside it
  suffices ∀ (c : Prop) [Decidable c], (if c then GenK.memo A B (t.gen η) else t.gen η).Wf from this _
  intro c _; split
  all_goals first | exact GenK.memo_wf h | exact h

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`**: only `comp` builds one (`GenK.comp_wf`), a variable reads
    `η`'s, and every other op returns tables. -/
theorem Tm.gen_wf_spine {A B : Obj} (t : Tm A B) :
    (∀ η : Code, η.Wf → (t.gen η).Wf) ∧
    ∀ (η : Code) (xs : Codes), η.Wf → (∀ x ∈ xs, x.2.2.Wf) → (t.argGen η xs).Wf := by
  induction t
  case prim r =>
    refine ⟨fun η _ => ?_, fun η xs _ hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).1
    · exact (primGen_ok r _ _ xs hx).1
  case arg f x ihf ihx =>
    refine ⟨fun η hη => ?_, fun η xs hη hx => ?_⟩ <;>
      simp only [Tm.gen, Tm.argGen] <;> refine ihf.2 η _ hη fun y hy => ?_ <;>
      rcases List.mem_cons.1 hy with rfl | hy
    any_goals exact code_wf (ihx.1 η hη)
    all_goals first | exact hx y hy | simp at hy
  case share _ R ih =>
    refine ⟨fun η hη => ?_, fun η xs hη hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · split
      · rename_i h; exact Codes.at_wf hη.2 h
      · exact code_wf (ih.1 η.closed ⟨fun _ _ _ => trivial, hη.2⟩)
    · exact ih.2 η.closed xs ⟨fun _ _ _ => trivial, hη.2⟩ hx
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η hη => ?_, fun η xs hη hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact code_wf (ih.1 _ (Code.args_wf hη ks [] fun _ h => nomatch h))
    · exact code_wf (ih.1 _ (Code.args_wf hη ks xs hx))
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η hη => ?_, fun η xs _ _ => by unfold Tm.argGen; exact trivial⟩
  all_goals simp only [Tm.gen]
  case comp R S ihR ihS => exact GenK.comp_wf _ (code_wf (ihS.1 η hη))
  case ldiv R S U V ihR ihS ihU ihV => exact GenK.ldiv_wf _ _ _ (code_wf (ihS.1 η hη))
  case own R ih => exact code_wf (ih.1 η hη)
  case var k => exact hη.1 k _ _
  case hylo => split <;> first | trivial | exact fun _ => trivial | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])
  all_goals first
    | trivial
    | exact GenK.ofVals_wf
    | exact GenK.top_wf
    | exact GenK.id_wf
    | exact GenK.meet_wf _ _
    | exact GenK.diff_wf _ _
    | exact GenK.pair_wf _ _
    | exact GenK.lift1_wf _
    | exact GenK.lift2_wf _ _
    | exact fun _ => trivial
    | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** (`Tm.gen_wf_spine`, its first half). -/
theorem Tm.gen_wf {A B : Obj} (t : Tm A B) :
    ∀ η : Code, η.Wf → (t.gen η).Wf := (Tm.gen_wf_spine t).1

/-- `Tm.gen_sound` with its spine half: a spine given codes `xs` that are `Wf` and represent `ss` generates code
    that represents its meaning of `ss` (`Tm.argGen`, `Tm.argDen`). -/
theorem Tm.gen_sound_spine {A B : Obj} (t : Tm A B) :
    (∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
    ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem),
      t.GenHyp η.sh.Shares → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
        ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) := by
  -- strong induction on `Tm.size`: a `hylo`'s children's term (`Tm.kids`) is no subterm, only no larger than its body
  suffices H : ∀ n {A B : Obj} (t : Tm A B), t.size ≤ n →
      (∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
      ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem),
        t.GenHyp η.sh.Shares → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
          ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) from H _ t (Nat.le_refl _)
  -- a fixed point's round binds its variable to its table (`Sound.bind`)
  have hconst {A B : Obj} (Y : Tab A B) : ∀ K, (GenK.const A B (.ok Y)).Reps K (rep Y) :=
    fun _ => (GenK.reps_iff _ _ _).2 fun t ht x y _ _ _ => by cases ht; exact Iff.rfl
  -- an error table runs to no table, so it represents every meaning
  have herr {A B : Obj} (e : String) (X : Den A B) : ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K X :=
    fun _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h
  intro n
  induction n
  case zero => intro A B t h; cases t <;> simp [Tm.size] at h
  rename_i n H
  intro A B t
  induction t <;> intro hn <;> simp only [Tm.size] at hn
  case prim r =>
    refine ⟨fun η ρ _ _ => ?_, fun η ρ xs ss _ _ hx hr => ?_⟩ <;>
      simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).2 [] trivial
    · exact (primGen_ok r _ _ xs hx).2 ss hr
  case arg C D f x ihf ihx =>
    have step (η ρ) (xs : Codes) (ss : List Sem)
        (hl : f.GenHyp η.sh.Shares ∧ x.GenHyp η.sh.Shares) (hs : Sound η ρ) (hx : ∀ y ∈ xs, y.2.2.Wf) (hr : CodesRep xs ss) :
        ∀ K, (f.argGen η (⟨C, D, x.code η⟩ :: xs)).Reps K (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) :=
      (ihf (by omega)).2 η ρ _ _ hl.1 hs (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact code_wf (gen_wf x η hs.2)
          · exact hx y hy)
        ⟨by rw [dif_pos ⟨rfl, rfl⟩]; exact code_of ((ihx (by omega)).1 η ρ hl.2 hs), hr⟩
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss hl hs hx hr => ?_⟩ <;>
      simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact step η ρ [] [] hl hs (fun _ h => nomatch h) trivial
    · exact step η ρ xs ss hl hs hx hr
  -- its slot where the table has one (`Codes.Shares`), else built under `η`'s table and no variable
  case share _ R ih =>
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss hl hs hx hr => ?_⟩ <;>
      simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen] <;>
      have he : Sound η.closed Val.empty := ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial, hs.2.2⟩
    · intro K; split
      · rename_i r h; exact hl.1 r h K
      · exact code_of ((ih (by omega)).1 η.closed Val.empty hl.2 he) K
    · exact (ih (by omega)).2 η.closed Val.empty xs ss hl.2 he hx hr
  -- the body under its arguments bound at `ks` (`Sound.args`), whatever the caller's `η`, `ρ`; same table
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss hl hs hx hr => ?_⟩ <;>
      simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact code_of ((ih (by omega)).1 _ _ (by rw [Code.args_sh]; exact hl)
        (Sound.args hs ks [] [] (fun _ h => nomatch h) trivial))
    · exact code_of ((ih (by omega)).1 _ _ (by rw [Code.args_sh]; exact hl)
        (Sound.args hs ks xs ss hx hr))
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss _ _ _ _ => by unfold Tm.argGen; exact herr _ _⟩
  all_goals simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den]
  case val R => exact GenK.val_sound (R, true)
  case uni U => exact GenK.uni_sound (U, true)
  case zero => exact GenK.zero_sound
  case id => exact GenK.id_sound
  case top V ih => exact GenK.top_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case outl => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
  case outr => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outr_holds h
  case comp R S ihR ihS =>
    exact GenK.comp_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case conv R ih => exact GenK.conv_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case meet R S ihR ihS =>
    exact GenK.meet_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case join R S ihR ihS => exact GenK.join_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case diff R S ihR ihS => exact GenK.diff_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case dom R ih => exact GenK.dom_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case ran R ih => exact GenK.ran_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case rdiv R S U V ihR ihS ihU ihV =>
    exact GenK.rdiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
  case ldiv R S U V ihR ihS ihU ihV =>
    exact GenK.ldiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
      (code_wf (gen_wf S η hs.2))
  case pair R S ihR ihS => exact GenK.pair_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case prod R S ihR ihS => exact GenK.prod_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case fold R S ihR ihS =>
    exact GenK.fold_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case foldr R S ihR ihS =>
    exact GenK.foldr_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case foldI R S ihR ihS =>
    exact GenK.foldI_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_wf (gen_wf R η hs.2))
      (code_of ((ihS (by omega)).1 η ρ hl.2 hs)) (code_wf (gen_wf S η hs.2))
  case lam R ih => exact GenK.lam_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case E R ih =>
    exact GenK.lam_sound (GenK.comp_sound (GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h)
      (code_of ((ih (by omega)).1 η ρ hl hs)) (code_wf (gen_wf R η hs.2)))
  case nil => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.nil_holds h
  case own R ih => exact code_of ((ih (by omega)).1 η ρ hl hs)
  case succ U ih => exact GenK.succ_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case arith U ih => exact GenK.arith_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case leq U ih => exact GenK.cmp_sound (s := false) (code_of ((ih (by omega)).1 η ρ hl hs))
  case lt U ih => exact GenK.cmp_sound (s := true) (code_of ((ih (by omega)).1 η ρ hl hs))
  case var k => exact hs.1 k _ _
  case est Q ih => exact GenK.est_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case thin Q ih => exact GenK.thin_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case atPos k => exact GenK.atPos_sound k
  case nu k S b ihS ihb =>
    exact GenK.nu_sound (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (fun X => code_of ((ihb (by omega)).1 _ _ hl.2.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  case mu k w m b ih =>
    exact GenK.mu_sound (fun X => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  -- children `Tm.kids` reads in no shape: `Tm.gen`'s error table
  case hylo A' B' k w b ih =>
    have hc := Tm.genHyp_kids k A' b hl.2
    have hsz := Tm.size_kids k A' b
    revert hc hsz
    cases hk : b.kids k A' with
    | none => intro _ _; simp only [Option.isNone_none, ↓reduceIte]; exact herr _ _
    | some c =>
      intro hc hsz
      simp only [Option.isNone_some, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hc hsz ⊢
      exact GenK.hylo_sound ((H c (by omega)).1 η ρ hc hs |> code_of) (code_wf (gen_wf c η hs.2))
        (fun Y => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst Y) (by trivial))))
        (fun Y => code_wf (gen_wf b _ (hs.bind k (hconst Y) (by trivial)).2))
        (fun _ _ h => Tm.den_mono hl.1 h) (fun X Y a h => Tm.den_local k ρ X Y b c hk a h)

/-- **`Tm.gen` is sound**: the code of every term represents its meaning in every context, given each fixed point's body
    positive and each shared slot its part's meaning (`Tm.GenHyp`), and an environment `η` that represents `ρ`;
    where the code is an error table (`Tm.hasCode` false) the run fails, which represents every meaning. -/
theorem Tm.gen_sound {A B : Obj} (t : Tm A B) :
    ∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ) :=
  (Tm.gen_sound_spine t).1

end Rel.Lang
