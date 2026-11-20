import Rel.Lang.GenKBits
import Rel.Lang.Den
import Rel.Run.Lang.Expand

/-! `Tm.gen`: `Expand.node` as a Lean function from a term to its `GenK` code, one `GenK` op per constructor with
    `Expand.node`'s argument order, and `Tm.code` as `Expand.code` (a closed part memoised, `GenK.memo`). Then
    `Tm.gen_sound`: on a term with no `Tm.gap` constructor, under `Sound`, the code represents `Tm.den` in every
    context, each case one `GenK.*_sound` (`GenKSpec`, `GenKBits`). A bit matrix the code passes on is `Rel.Wf`
    (`Tm.gen_wf`); `GenK.ReadsBack` (`ofBits` reads back what `compSelM`, `compTabMat` build) and the order law of each
    `Λ` (`LamLaw`, false at a float atom) are hypotheses. -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The code each variable `k` reads at the objects a term asks for: `Val`'s twin, what `Expand.node`'s `ρ` binds. -/
abbrev Code := Nat → (A B : Obj) → Rel A B

/-- No variable bound: `Val.empty`'s twin, what a `share` is built under. -/
def Code.empty : Code := fun _ A B => GenK.zero A B

/-- `η` with `k` bound to `r`, `Val.bind`'s twin: a use at other objects reads `𝟘`. -/
def Code.bind (η : Code) (k : Nat) {A B : Obj} (r : Rel A B) : Code := fun j A' B' =>
  if j = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ r else GenK.zero A' B') else η j A' B'

/-- The code environment `η` represents the meaning environment `ρ`, at every variable and object, in every
    context, and every bit matrix it holds is `Rel.Wf`. -/
def Sound (η : Code) (ρ : Val) : Prop := (∀ k A B K, (η k A B).Reps K (ρ k A B)) ∧ ∀ k A B, (η k A B).Wf

/-- The hypothesis of `Tab.lam_den` at `A ⟶ [B]`: two rows of one key whose codes ascend strictly hold values
    ascending in `B.lt`. It fails at a float atom, so it is asked per `Λ`, never for every object. -/
def LamLaw (A B : Obj) : Prop := ∀ (m : USize) (x : Vals (.prod A B) m) es, Vals.cols x = .ok es →
  ∀ i i' : Fin m.toNat, (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true →
    seenKey m es i ≠ seenKey m es i' → B.lt (x.row i).2 (x.row i').2

mutual
/-- `Expand.code` without the constant sharing: a closed `t` memoised (`GenK.memo`), any other its node. -/
def Tm.code (η : Code) {A B : Obj} (t : Tm A B) : Rel A B :=
  if Expand.closed t then GenK.memo A B (t.gen η) else t.gen η
termination_by 2 * t.size + 1

/-- `Expand.node`: `t`'s own `GenK` op, its parts by `Tm.code`. A fixed point's variable reads its round's table
    (`GenK.const`); `share` is built under no variable; `prim`, `arg`, `call` are `Tm.gap`: `Expand.primE` fits a
    row's wrapper by unification (`fitConst`) and `spine` names a kernel twin constant, neither a Lean function. -/
def Tm.gen (η : Code) {A B : Obj} (t : Tm A B) : Rel A B :=
  match A, B, t with
  | A, B, .val R => GenK.val A B (R, true)
  | A, _, .uni (m := m) U => GenK.uni A m (U, true)
  | A, B, .zero => GenK.zero A B
  | A, _, .id => GenK.id A
  | A, B, .top V => GenK.top A B (V.code η)
  | .prod A B, _, .outl => GenK.outl A B
  | .prod A B, _, .outr => GenK.outr A B
  | A, C, .comp (B := B) R S => GenK.comp A B C S.dem (R.code η) (S.code η)
  | B, A, .conv R => GenK.conv A B (R.code η)
  | A, B, .meet R S => GenK.meet A B R.dem S.dem (R.code η) (S.code η)
  | A, B, .join R S => GenK.join A B R.dem S.dem (R.code η) (S.code η)
  | A, B, .diff R S => GenK.diff A B R.dem S.dem (R.code η) (S.code η)
  | A, _, .dom (B := B) R => GenK.dom A B R.dem (R.code η)
  | B, _, .ran (A := A) R => GenK.ran A B (R.code η)
  | B, C, .ldiv (A := A) R S UB UC => GenK.ldiv A B C (R.code η) (S.code η) (UB.code η) (UC.code η)
  | A, B, .rdiv (C := C) R S UA UB => GenK.rdiv A B C (R.code η) (S.code η) (UA.code η) (UB.code η)
  | A, .prod B C, .pair R S => GenK.pair A B C R.dem S.dem (R.code η) (S.code η)
  | .prod A C, .prod B D, .prod R S => GenK.prod A B C D (R.code η) (S.code η)
  | .sum A B, C, .junc R S => GenK.junc A B C (R.code η) (S.code η)
  | A, .arr B, .lam R => GenK.lam A B R.dem (R.code η)
  | .arr A, .arr B, .E R => GenK.E A B R.dem (R.code η)
  | _, B, .est Q => GenK.est B (Q.code η)
  | _, .arr B, .thin Q => GenK.thin B (Q.code η)
  | A, .arr B, .nil => GenK.nil A B
  | .arr B, _, .atPos k => GenK.atPos B k
  | _, _, .own R => R.code η
  | _, _, .succ U => GenK.succ (U.code η)
  | _, _, .arith k U => GenK.arith k (U.code η)
  | _, _, .leq U => GenK.leq (U.code η)
  | _, _, .lt U => GenK.lt (U.code η)
  | .arr Y, V, .foldr e S => GenK.foldr Y V S.dem (e.code η) (S.code η)
  | .arr Y, V, .fold e S => GenK.fold Y V S.dem (e.code η) (S.code η)
  | _, _, .share _ R => R.code Code.empty
  | .prod I (.arr Y), V, .foldI e S => GenK.foldI I Y V e.dem S.dem (e.code η) (S.code η)
  | .prod I A, B, .flat R => GenK.flat I A B R.dem (R.code η)
  | A, B, .var _ k => η k A B
  | A, B, .nu k S b => GenK.nu A B (S.code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .mu k w n b => GenK.mu A B w n fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .hylo k w b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    GenK.hylo A B w ((b.kids k A).getD .zero).dem b.dem (((b.kids k A).getD .zero).code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | .sum A B, C, .juncD R S => GenK.juncD A B C R.dem S.dem (R.code η) (S.code η)
  | _, _, .prim r => .tab (.error s!"Tm.gen: the row `{r.sym}` is in the gap (Expand.primE)")
  | _, _, .arg .. => .tab (.error "Tm.gen: an argument is in the gap (Expand.primE, Expand.spine)")
  | _, _, .call _ c .. => .tab (.error s!"Tm.gen: the call `{c}` is in the gap (Expand.spine)")
termination_by 2 * t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
end

/-- Some node of `t` has no proved case in `Tm.gen_sound`: no `GenK` lemma yet (`arith est thin atPos fold foldr
    foldI mu nu hylo`), a lemma that does not hold as stated (`juncD`), or no mirror in `Tm.gen` (`prim arg call`). -/
def Tm.gap : {A B : Obj} → Tm A B → Bool
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .var .. => false
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .own R
  | _, _, .succ R | _, _, .leq R | _, _, .lt R | _, _, .flat R | _, _, .share _ R => R.gap
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .junc R S => R.gap || S.gap
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.gap || S.gap || U.gap || V.gap
  | _, _, .juncD .. | _, _, .arith .. | _, _, .est _ | _, _, .thin _ | _, _, .atPos _ | _, _, .fold ..
  | _, _, .foldr .. | _, _, .foldI .. | _, _, .mu .. | _, _, .nu .. | _, _, .hylo .. | _, _, .call ..
  | _, _, .arg .. | _, _, .prim _ => true

/-- `LamLaw` at each `Λ` and `E` of `t` (`E(R) = Λ(∋ ≫ R)`, at `[A] ⟶ [B]`). -/
def Tm.LamLaws : {A B : Obj} → Tm A B → Prop
  | _, _, .lam (A := A) (B := B) R => LamLaw A B ∧ R.LamLaws
  | _, _, .E (A := A) (B := B) R => LamLaw (.arr A) B ∧ R.LamLaws
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R | _, _, .succ R | _, _, .leq R
  | _, _, .lt R | _, _, .flat R | _, _, .share _ R => R.LamLaws
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .junc R S => R.LamLaws ∧ S.LamLaws
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.LamLaws ∧ S.LamLaws ∧ U.LamLaws ∧ V.LamLaws
  | _, _, _ => True

namespace GenK

theorem memo_sound {A B : Obj} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.memo A B R).Reps K X := fun K => by
  cases R with
  | tab t => exact hR K
  | lazy f => exact (reps_iff _ _ _).2 fun t h x y _ _ => (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl
  | bits => exact (reps_iff _ _ _).2 fun t h x y _ _ => (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl

theorem memo_wf {A B : Obj} (R : Rel A B) : (GenK.memo A B R).Wf := by cases R <;> trivial

end GenK

theorem Tm.code_of {η : Code} {A B : Obj} {t : Tm A B} {X : Core.Rel A.El B.El} (h : ∀ K, (t.gen η).Reps K X) :
    ∀ K, (t.code η).Reps K X := by
  rw [Tm.code]; split
  · exact GenK.memo_sound h
  · exact h

theorem Tm.code_wf {η : Code} {A B : Obj} {t : Tm A B} (h : (t.gen η).Wf) : (t.code η).Wf := by
  rw [Tm.code]; split
  · exact GenK.memo_wf _
  · exact h

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** off the gap: only `comp` builds one (`GenK.comp_wf`), a
    variable reads `η`'s, and every other op returns tables. -/
theorem Tm.gen_wf (hb : GenK.ReadsBack) {A B : Obj} (t : Tm A B) :
    ∀ η : Code, t.gap = false → (∀ k A B, (η k A B).Wf) → (t.gen η).Wf := by
  induction t <;> intro η hg hη <;> simp only [Tm.gap, Bool.or_eq_false_iff, Bool.true_eq_false] at hg <;>
    simp only [Tm.gen]
  case comp R S ihR ihS => exact GenK.comp_wf hb _ (code_wf (ihS η hg.2 hη))
  case own R ih => exact code_wf (ih η hg hη)
  case share R ih => exact code_wf (ih Code.empty hg fun _ _ _ => trivial)
  case var k => exact hη k _ _
  all_goals first
    | trivial
    | exact GenK.ofVals_wf
    | exact GenK.top_wf
    | exact GenK.meet_wf _ _
    | exact GenK.lift1_wf _
    | exact GenK.lift2_wf _ _
    | exact fun _ => trivial
    | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])

/-- **`Tm.gen` is sound off the gap**: the code of a term with no `Tm.gap` node represents its meaning in every
    context, given `ReadsBack`, `LamLaw` at each `Λ`, and an environment `η` that represents `ρ`. -/
theorem Tm.gen_sound (hb : GenK.ReadsBack) {A B : Obj} (t : Tm A B) :
    ∀ (η : Code) (ρ : Val), t.gap = false → t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ) := by
  induction t <;> intro η ρ hg hl hs <;> simp only [Tm.gap, Bool.or_eq_false_iff, Bool.true_eq_false] at hg <;>
    simp only [Tm.LamLaws] at hl <;> simp only [Tm.gen, Tm.den]
  case val R => exact GenK.val_sound (R, true)
  case uni U => exact GenK.uni_sound (U, true)
  case zero => exact GenK.zero_sound
  case id => exact GenK.id_sound
  case top V ih => exact GenK.top_sound (code_of (ih η ρ hg hl hs))
  case outl => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
  case outr => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outr_holds h
  case comp R S ihR ihS =>
    exact GenK.comp_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf hb S η hg.2 hs.2))
  case conv R ih => exact GenK.conv_sound (code_of (ih η ρ hg hl hs))
  case meet R S ihR ihS =>
    exact GenK.meet_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf hb R η hg.1 hs.2)) (code_wf (gen_wf hb S η hg.2 hs.2))
  case join R S ihR ihS => exact GenK.join_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
  case diff R S ihR ihS => exact GenK.diff_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
  case dom R ih => exact GenK.dom_sound (code_of (ih η ρ hg hl hs))
  case ran R ih => exact GenK.ran_sound (code_of (ih η ρ hg hl hs))
  case ldiv R S U V ihR ihS ihU ihV =>
    exact GenK.ldiv_sound (code_of (ihR η ρ hg.1.1.1 hl.1 hs)) (code_of (ihS η ρ hg.1.1.2 hl.2.1 hs))
      (code_of (ihU η ρ hg.1.2 hl.2.2.1 hs)) (code_of (ihV η ρ hg.2 hl.2.2.2 hs))
  case rdiv R S U V ihR ihS ihU ihV =>
    exact GenK.rdiv_sound (code_of (ihR η ρ hg.1.1.1 hl.1 hs)) (code_of (ihS η ρ hg.1.1.2 hl.2.1 hs))
      (code_of (ihU η ρ hg.1.2 hl.2.2.1 hs)) (code_of (ihV η ρ hg.2 hl.2.2.2 hs))
  case pair R S ihR ihS => exact GenK.pair_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
  case prod R S ihR ihS => exact GenK.prod_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
  case junc R S ihR ihS => exact GenK.junc_sound (code_of (ihR η ρ hg.1 hl.1 hs)) (code_of (ihS η ρ hg.2 hl.2 hs))
  case lam R ih => exact GenK.lam_sound (code_of (ih η ρ hg hl.2 hs)) hl.1
  case E R ih =>
    exact GenK.lam_sound (GenK.comp_sound (GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h)
      (code_of (ih η ρ hg hl.2 hs)) (code_wf (gen_wf hb R η hg hs.2))) hl.1
  case nil => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.nil_holds h
  case own R ih => exact code_of (ih η ρ hg hl hs)
  case succ U ih => exact GenK.succ_sound (code_of (ih η ρ hg hl hs))
  case leq U ih => exact GenK.cmp_sound (fun _ _ _ h => Tab.leq_holds h) (code_of (ih η ρ hg hl hs))
  case lt U ih => exact GenK.cmp_sound (fun _ _ _ h => Tab.lt_holds h) (code_of (ih η ρ hg hl hs))
  case share R ih =>
    exact code_of (ih Code.empty Val.empty hg hl ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial⟩)
  case flat R ih => exact GenK.flat_sound (code_of (ih η ρ hg hl hs))
  case var k => exact hs.1 k _ _

end Rel.Lang
