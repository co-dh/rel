module

public import Rel.Lang.GenKFold
public import Rel.RepWhere
public import Rel.RepAsc
public import Rel.RepSums
public import Rel.Lang.GenKEst
public import Rel.Lang.GenKFix
public import Rel.Lang.GenKHylo
public import Rel.Lang.Den
public import Rel.Run.Lang.TmGen
public import Rel.RepCast

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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
def Sound (η : Code) (ρ : Val) : Prop := (∀ k A B K, K.WF → (η k A B).Reps K (ρ k A B)) ∧ η.Wf

/-- The slot `k` of the table `σ` at `A ⟶ B`, where it has one, represents the meaning of the closed part `R`
    numbered `k`: what `Tm.gen_sound` asks at each `share k R` (`Tm.GenHyp`), since a slot is computed once, apart
    from the terms that read it (`Code.shares`). -/
def Codes.Shares (σ : Codes) {A B : Obj} (k : Nat) (R : Tm A B) : Prop :=
  ∀ r, σ.at k A B = some r → ∀ K, K.WF → r.Reps K (R.den Val.empty)

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
theorem Code.args_sh (η : Code) : ∀ (ks : List Nat) (xs : Codes) (ds : List Bool), (Code.args η ks xs ds).sh = η.sh
  | k :: ks, ⟨_, _, _⟩ :: xs, ds => Code.args_sh η ks xs ds.tail
  | [], _, _ | _ :: _, [], _ => rfl

/-- The empty table's code is `Wf` (`Tab.zero_wf`): what `Code.bind` and `Code.args` read at other objects. -/
theorem GenK.zero_wf {A B : Obj} : (GenK.zero A B).Wf := GenK.tab_wf fun _ h => Tab.zero_wf h

/-- A fixed point's round `GenK.const` of a `WF` table is `Wf`. -/
theorem GenK.const_wf {A B : Obj} {X : Tab A B} (h : X.WF) : (GenK.const A B (.ok X)).Wf := h

/-- A literal is `Wf` where its flag says its cells passed (`Tm.gen` sets it by `ValsB.cellsOk`). -/
theorem GenK.val_wf {A B : Obj} {R : Tab A B × Bool} (h : R.2 = true → R.1.WF) : (GenK.val A B R).Wf := by
  unfold GenK.val GenK.const; split
  · exact GenK.tab_wf fun _ ht => Tab.canon_wf ht (h ‹_›)
  · trivial

theorem GenK.uni_wf {A : Obj} {m : USize} {U : Vals A m × Bool} (h : U.2 = true → Vals.WF U.1) :
    (GenK.uni A m U).Wf := by
  unfold GenK.uni GenK.const; split
  · exact GenK.tab_wf fun _ ht => Tab.idU_wf ht (h ‹_›)
  · trivial

theorem GenK.conv_wf {A B : Obj} {R : Rel A B} (wR : R.Wf) : (GenK.conv A B R).Wf := by
  unfold GenK.conv; exact GenK.lift1_wf (fun _ h => h.conv) (fun _ _ w h => Tab.conv_wf h w) wR
theorem GenK.dom_wf {A B : Obj} {R : Rel A B} (wR : R.Wf) : (GenK.dom A B R).Wf := by
  unfold GenK.dom; refine GenK.lift1_wf ?_ (fun _ _ w h => Tab.dom_wf h w) wR
  exact fun _ h => ⟨h.side, trivial, trivial⟩
theorem GenK.ran_wf {A B : Obj} {R : Rel A B} (wR : R.Wf) : (GenK.ran A B R).Wf := by
  unfold GenK.ran; refine GenK.lift1_wf ?_ (fun _ _ w h => Tab.ran_wf h w) wR
  exact fun _ h => ⟨trivial, h.side, trivial⟩
theorem GenK.join_wf {A B : Obj} {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) : (GenK.join A B R S).Wf :=
  GenK.lift2_wf (fun _ h => h) (fun _ h => h) (fun _ _ _ wr ws h => Tab.union_wf h wr ws) wR wS

/-- `R/S` reads `ldivSel ldivOf` of the converses (`Tab.ldivOf_wf`, `Tab.ldivSel_wf`), turned back. -/
theorem GenK.rdiv_wf {A B C : Obj} {R : Rel A C} {S : Rel B C} {UA : Rel A A} {UB : Rel B B} (wR : R.Wf) (wS : S.Wf)
    (wA : UA.Wf) (wB : UB.Wf) : (GenK.rdiv A B C R S UA UB).Wf :=
  GenK.lift2_wf (fun _ _ => Known.wf_empty) (fun _ _ => Known.wf_empty) (fun r s t wr ws h => by
    obtain ⟨sc, hs, h⟩ := GenK.bind_ok h
    obtain ⟨rc, hr, h⟩ := GenK.bind_ok h
    obtain ⟨ub, hub, h⟩ := GenK.bind_ok h
    obtain ⟨ua, hua, h⟩ := GenK.bind_ok h
    obtain ⟨q, hq, h⟩ := GenK.bind_ok h
    have w1 := Tab.conv_wf hs ws
    have w2 := Tab.conv_wf hr wr
    have wu := wB.runE Known.wf_empty hub
    have wa := wA.runE Known.wf_empty hua
    exact Tab.conv_wf h (Tab.ldivSel_wf (fun h => Tab.ldivOf_wf h w1 w2 wu wa) hq w1 w2 wu wa)) wR wS

/-- A fixed point whose round `φ` is `Wf` on every `WF` table runs only `WF` rounds (`Tab.nu_wf`, `Tab.mu_wf`). -/
theorem GenK.nu_wf {A B : Obj} {S : Rel A B} {φ : Tab A B → Rel A B} (wS : S.Wf) (wφ : ∀ X, X.WF → (φ X).Wf) :
    (GenK.nu A B S φ).Wf :=
  GenK.tab_wf fun _ h => let ⟨_, hs, h⟩ := GenK.bind_ok h
    Tab.nu_wf (fun X _ ht wX => (wφ X wX).runE Known.wf_empty ht) h (wS.runE Known.wf_empty hs)
theorem GenK.mu_wf {A B : Obj} {what : String} {cap : Nat} {lin : Bool} {φ : Tab A B → Rel A B}
    (wφ : ∀ X, X.WF → (φ X).Wf) : (GenK.mu A B what cap lin φ).Wf :=
  GenK.tab_wf fun _ h => by
    cases lin
    · exact Tab.mu_wf (fun X _ ht wX => (wφ X wX).runE Known.wf_empty ht) h
    · exact Tab.muLin_wf (fun X _ ht wX => (wφ X wX).runE Known.wf_empty ht) h

/-- `hylo`'s nodes are `μN : D ∪ ran(N ≫ ch)` and its answer `D ≫ μX : N ≫ φ(X)`: `Tab.mu_wf` of `WF` rounds
    (`compT_wf`, `Tab.union_wf`, `Tab.ran_wf`), then `Tab.comp_wf`. -/
theorem GenK.hylo_wf {A B : Obj} {what : String} {ch : Rel A A} {φ : Tab A B → Rel A B} (wch : ch.Wf)
    (wφ : ∀ X, X.WF → (φ X).Wf) : (GenK.hylo A B what ch φ).Wf := by
  have after : ∀ {C : Obj} {T : Rel A C} (N : Tab A A), N.WF → T.Wf → ∀ {t}, (GenK.compT (.ok N) T).runE {} = .ok t →
      t.WF := fun N wN wT _ ht => (GenK.compT_wf (fun _ e => by cases e; exact wN) wT).runE Known.wf_empty ht
  refine GenK.ofVals_wf fun _ X t wX h => ?_
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  have wD := Tab.idU_wf hD wX
  obtain ⟨N, hN, h⟩ := GenK.bind_ok h
  have wN : N.WF := Tab.mu_wf (fun M _ ht wM => by
    obtain ⟨r, hr, ht⟩ := GenK.bind_ok ht
    obtain ⟨q, hq, ht⟩ := GenK.bind_ok ht
    exact Tab.union_wf ht wD (Tab.ran_wf hq (after M wM wch hr))) hN
  -- `C`, the cycle check `cyc`, and the `if` that throws on a cycle: none reaches the answer
  obtain ⟨_, -, h⟩ := GenK.bind_ok h
  obtain ⟨_, -, h⟩ := GenK.bind_ok h
  split at h; · cases h
  obtain ⟨_, -, h⟩ := GenK.bind_ok h
  obtain ⟨Y, hY, h⟩ := GenK.bind_ok h
  exact Tab.comp_wf h wD (Tab.mu_wf (fun M _ ht wM => after N wN (wφ M wM) ht) hY)

/-- `η` with `k` bound to a `Wf` code is `Wf`. -/
theorem Code.Wf.bind {η : Code} (hη : η.Wf) (k : Nat) {A B : Obj} {r : Rel A B} (hw : r.Wf) : (η.bind k r).Wf := by
  refine ⟨fun j A' B' => ?_, hη.2⟩
  by_cases hj : j = k
  · simp only [Code.bind, hj, if_true]
    by_cases ho : A = A' ∧ B = B'
    · obtain ⟨rfl, rfl⟩ := ho; rw [dif_pos ⟨rfl, rfl⟩]; exact hw
    · rw [dif_neg ho]; exact GenK.zero_wf
  · simp only [Code.bind, hj, if_false]; exact hη.1 j A' B'

/-- `η` with `k` bound to a `Wf` code `r` that represents `X` represents `ρ` with `k` bound to `X`: a fixed point's
    round (`GenK.const` of its table) or a call's argument (`Sound.args`). -/
theorem Sound.bind {η : Code} {ρ : Val} (hs : Sound η ρ) (k : Nat) {A B : Obj} {r : Rel A B} {X : Core.Rel (Obj.El A) (Obj.El B)}
    (hr : ∀ K, K.WF → r.Reps K X) (hw : r.Wf) : Sound (η.bind k r) (ρ.bind k X) := by
  refine ⟨fun j A' B' K hK => ?_, hs.2.bind k hw⟩
  by_cases hj : j = k
  · simp only [Code.bind, Val.bind, hj, if_true]
    by_cases ho : A = A' ∧ B = B'
    · obtain ⟨rfl, rfl⟩ := ho
      rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]; exact hr K hK
    · rw [dif_neg ho, dif_neg ho]; exact GenK.zero_sound K hK
  · simp only [Code.bind, Val.bind, hj, if_false]; exact hs.1 j A' B' K hK

/-- **A program's run-time names bound in statement order** (IO design A.3, the environment `n.io` computes in):
    each `(k, A, B, r, X)` of `bs` bound in turn, `r` a `Wf` code that represents `X` (an input's table,
    `GenK.val_sound`; a run-time definition's code, `Tm.gen_sound` of its body at the names before it), leaves the
    environment sound; then `Tm.gen_sound` of an output's term gives that its table represents its meaning. -/
theorem Sound.inputs {η : Code} {ρ : Val} (hs : Sound η ρ) :
    ∀ bs : List (Nat × (A : Obj) × (B : Obj) × (Rel A B × Core.Rel (Obj.El A) (Obj.El B))),
      (∀ b ∈ bs, (∀ K, K.WF → b.2.2.2.1.Reps K b.2.2.2.2) ∧ b.2.2.2.1.Wf) →
      Sound (bs.foldl (fun η b => η.bind b.1 b.2.2.2.1) η) (bs.foldl (fun ρ b => ρ.bind b.1 b.2.2.2.2) ρ)
  | [], _ => hs
  | b :: bs, h => Sound.inputs (hs.bind b.1 (h b (.head _)).1 (h b (.head _)).2) bs fun c hc => h c (.tail _ hc)

/-- `Code.args` over a `Wf` `η` is `Wf` when every argument is. -/
theorem Code.args_wf {η : Code} (hη : η.Wf) :
    ∀ (ks : List Nat) (xs : Codes) (ds : List Bool), (∀ x ∈ xs, x.2.2.Wf) → (Code.args η ks xs ds).Wf
  | k :: ks, ⟨X, Y, x⟩ :: xs, ds, hw => by
    have ih := Code.args_wf hη ks xs ds.tail fun y hy => hw y (List.mem_cons_of_mem _ hy)
    refine ⟨fun j A' B' => ?_, ih.2⟩
    simp only [Code.args, Code.bind]
    split
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hw _ List.mem_cons_self
      · exact GenK.zero_wf
    · exact ih.1 j A' B'
  | [], _, _, _ | _ :: _, [], _, _ => ⟨fun _ _ _ => GenK.zero_wf, hη.2⟩

/-- The rows whose case of `Tm.gen_sound` is proved (`rowsProved_ok`); `rowGens_proved` checks every row of
    `rowGens` is one. -/
def rowsProved : List String :=
  ["τ", "setify", "snoc", "cons", "cat", "uncat", "prefix", "suffix", "uncons", "unsnoc", "inits",
   "zip", "length", "sum", "loop", "filter", "concat", "merge", "thinL", "F", "positions", "asc",
   "tails", "takewhile", "sums", "flat", "$", "ymd", "foldI", "star", "dom", "ran", "nil", "est", "front"] ++
  floatOps.map (·.1) ++ arithOps.map (·.1) ++ ["succ", "mix", "at"] ++ cmpOps.map (·.1) ++ cmpOps.map (ordSym ·.2)

/-- What `Tm.gen_sound` asks of `t`: the body of each fixed point positive in its variable (`Tm.pol`, which
    `Tm.den_mono` reads), and `P k R` at each slot call `Tm.slot k R` (`Codes.Shares`). `Λ`'s order law asks nothing,
    since it is a theorem (`Vals.lamLaw`). -/
def Tm.GenHyp (P : {A B : Obj} → Nat → Tm A B → Prop) : {A B : Obj} → Tm A B → Prop
  | _, _, .call _ c _ _ R => (∀ k, c.slot? = some k → P k R) ∧ R.GenHyp P
  | _, _, .lam R | _, _, .top R | _, _, .conv R => R.GenHyp P
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .arg R S => R.GenHyp P ∧ S.GenHyp P
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.GenHyp P ∧ S.GenHyp P ∧ U.GenHyp P ∧ V.GenHyp P
  | _, _, .nu k S b => b.pol true k = true ∧ S.GenHyp P ∧ b.GenHyp P
  -- the children's term asks no more than the body (`Tm.genHyp_kids`)
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k = true ∧ b.GenHyp P
  -- every other constructor spelled out: a catch-all's equation lemmas time `simp` out
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .var .. | _, _, .prim _ | _, _, .mem | _, _, .inl | _, _, .inr => True

/-- `Tm.GenHyp` with nothing asked at a slot (`Tm.monoOK_iff`): what `GenSoundTest` evaluates beside
    `Tm.hasCode`. -/
def Tm.monoOK : {A B : Obj} → Tm A B → Bool
  | _, _, .lam R | _, _, .top R | _, _, .conv R
  | _, _, .call _ _ _ _ R => R.monoOK
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .arg R S => R.monoOK && S.monoOK
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.monoOK && S.monoOK && U.monoOK && V.monoOK
  | _, _, .nu k S b => b.pol true k && S.monoOK && b.monoOK
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k && b.monoOK
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .var .. | _, _, .prim _ | _, _, .mem | _, _, .inl | _, _, .inr => true

theorem Tm.monoOK_iff {A B : Obj} (t : Tm A B) : t.monoOK = true ↔ t.GenHyp fun _ _ => True := by
  induction t <;> simp [Tm.monoOK, Tm.GenHyp, and_assoc, *]

theorem Tm.genHyp_memAt {P : {A B : Obj} → Nat → Tm A B → Prop} (C E : Obj) : (Tm.memAt C E).GenHyp P := by
  unfold Tm.memAt; split <;> (try split) <;> (try subst_vars) <;> simp [Tm.GenHyp]

theorem Tm.genHyp_idAt {P : {A B : Obj} → Nat → Tm A B → Prop} (C E : Obj) : (Tm.idAt C E).GenHyp P := by
  unfold Tm.idAt; split <;> (try subst_vars) <;> simp [Tm.GenHyp]

/-- `inl°`, `inr°`'s code (`Tm.convInj`) is `Wf` and is their meaning, on the sum values in demand. -/
theorem Tm.convInj_wf {A B : Obj} {R : Tm A B} {c : Rel B A} (h : R.convInj = some c) : c.Wf := by
  cases R <;> simp [Tm.convInj] at h <;> subst h
  · exact GenK.ofVals_wf fun _ _ _ hX h => Tab.inlConv_wf h hX
  · exact GenK.ofVals_wf fun _ _ _ hX h => Tab.inrConv_wf h hX

theorem Tm.convInj_sound {A B : Obj} {R : Tm A B} {c : Rel B A} (ρ : Val) (h : R.convInj = some c) :
    ∀ K, K.WF → c.Reps K (R.den ρ)° := by
  cases R <;> simp [Tm.convInj] at h <;> subst h
  · exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.inlConv_holds h hX
  · exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.inrConv_holds h hX

/-- The children's term of `t` (`Tm.kids`) asks no more than `t`: `kids` builds it of `t`'s parts, `𝟙`, `𝟘`, `∪`,
    `juncD` and `∋`, none of which asks anything. -/
theorem Tm.genHyp_kids {P : {A B : Obj} → Nat → Tm A B → Prop} (k : Nat) (A : Obj)
    {C D : Obj} (t : Tm C D) (h : t.GenHyp P) : ((t.kids k A).getD .zero).GenHyp P := by
  induction t
  case arg f x _ _ =>
    cases f <;> unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;>
      simp_all (config := {decide := true}) [Tm.GenHyp, Tm.genHyp_memAt, Tm.genHyp_idAt]
  all_goals unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> (try subst_vars) <;>
    simp_all [Tm.GenHyp]

namespace GenK

theorem memo_sound {A B : Obj} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) :
    ∀ K, K.WF → (GenK.memo A B R).Reps K X := fun K hK => by
  cases R with
  | lazy f =>
    -- the forced value runs nothing new (`force_runE`), so in any `K` it computes what `R` computes closed
    have hF : ((Rel.lazy f).force {}).Reps K X := (reps_iff _ _ _).2 fun t h x y _ _ _ => by
      rw [force_runE] at h; exact (reps_iff _ _ _).1 (hR {} Known.wf_empty) t h x y rfl rfl trivial
    simp only [GenK.memo]; generalize (Rel.lazy f).force {} = v at hF ⊢
    rcases v with ⟨_ | _⟩ | _ | _ <;> first | exact hF | exact hR K hK
  | _ => exact hR K hK

theorem memo_wf {A B : Obj} {R : Rel A B} (h : R.Wf) : (GenK.memo A B R).Wf := by
  cases R with
  | lazy f =>
    have hF := h.force Known.wf_empty; simp only [GenK.memo]; generalize (Rel.lazy f).force {} = v at hF ⊢
    rcases v with ⟨_ | _⟩ | _ | _ <;> first | exact hF | exact h
  | _ => exact h

end GenK

theorem Tm.code_of {η : Code} {A B : Obj} {t : Tm A B} {X : Core.Rel A.El B.El} (h : ∀ K, K.WF → (t.gen η).Reps K X) :
    ∀ K, K.WF → (t.code η).Reps K X := by
  unfold Tm.code
  -- the condition held abstract: `split` would split the `matches` inside it
  suffices ∀ (c : Prop) [Decidable c], ∀ K, K.WF → (if c then GenK.memo A B (t.gen η) else t.gen η).Reps K X from this _
  intro c _; split
  all_goals first | exact GenK.memo_sound h | exact h

/-! ### The rows: `Prim.den` unfolded once, then one `Tab` law per row -/

/-- The codes `xs` represent the meanings `ss`, one for one at the same objects, in every context. -/
def CodesRep : Codes → List Sem → Prop
  | [], [] => True
  | ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss =>
    (if h : X' = X ∧ Y' = Y then ∀ K, K.WF → x.Reps K (h.1 ▸ h.2 ▸ T) else False) ∧ CodesRep xs ss
  | _, _ => False

/-- Codes `xs` that represent `ss` are at their objects, which `Prim.objs` reads. -/
theorem CodesRep.objs : ∀ {xs : Codes} {ss : List Sem}, CodesRep xs ss →
    ss.map (fun s => (s.1, s.2.1)) = xs.map fun x => (x.1, x.2.1)
  | [], [], _ => rfl
  | ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss, h => by
    simp only [CodesRep] at h; split at h
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; simp only [List.map_cons, CodesRep.objs h.2]
    · exact h.1.elim
  | [], _ :: _, h | _ :: _, [], h => by simp [CodesRep] at h

/-- `Wf` codes `xs` that represent `ss`, bound at `ks`, represent `ss` bound at `ks`: what a call's body is built
    and read under (`Sound.bind` per argument). -/
theorem Sound.args {η : Code} {ρ : Val} (hs : Sound η ρ) : ∀ (ks : List Nat) (xs : Codes) (ss : List Sem),
    ∀ (ds : List Bool), (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss → Sound (Code.args η ks xs ds) (Val.args ks ss)
  | k :: ks, ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss, ds, hw, hr => by
    simp only [CodesRep] at hr
    split at hr
    · rename_i h; obtain ⟨rfl, rfl⟩ := h
      exact (Sound.args hs ks xs ss ds.tail (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hr.2).bind k hr.1
        (hw _ List.mem_cons_self)
    · exact hr.1.elim
  | [], _, _, _, _, _ | _ :: _, [], [], _, _, _ => ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => GenK.zero_wf, hs.2.2⟩
  | _ :: _, [], _ :: _, _, _, hr | _ :: _, _ :: _, [], _, _, hr => by simp [CodesRep] at hr

/-- Row `s`'s cases of `Tm.gen_wf` and `Tm.gen_sound`: at every objects, given as many relation codes `xs` as it
    takes, each `Wf`, its code is `Wf`, and represents its meaning of any `ss` that `xs` represent. -/
def RowOK (s : String) : Prop := ∀ (r : Prim) (A B : Obj) (xs : Codes), r.sym = s → xs.length = rowArity s →
  (∀ x ∈ xs, x.2.2.Wf) → (primGen r A B xs).Wf ∧ ∀ ss, CodesRep xs ss →
    ∀ K, K.WF → (primGen r A B xs).Reps K (Prim.den r A B ss)

/-- `Prim.den` and `primGen` unfolded through the `rowDens` and `rowGens` lookups: a row is `RowOK` when its
    generated code at each `σ` and `xs` is `Wf`, and at the row's objects `c.ty σ` represents its meaning `D σ ss`
    of the `ss` that `xs` represent. -/
theorem rowOK_args {s : String} {c : RowCode} {D : RowDen c}
    {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (xs : Codes) (A B : Obj) (v : Rel A B), r.sym = s → xs.length = rowArity s →
      (∀ x ∈ xs, x.2.2.Wf) → f σ xs = some ⟨A, B, v⟩ → v.Wf ∧ ∀ ss, CodesRep xs ss →
        ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, K.WF → v.Reps K (hc.1 ▸ hc.2 ▸ D σ ss)) : RowOK s := by
  intro r A B xs hs hn hw
  have err (e : String) (X : List Sem → Core.Rel (Obj.El A) (Obj.El B)) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss,
      CodesRep xs ss → ∀ K, K.WF → (Rel.tab (A := A) (B := B) (.error e)).Reps K (X ss) :=
    ⟨trivial, fun _ _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
  unfold primGen; rw [hs, if_neg fun h => h hn, hf]
  cases hσ : r.objs A B (xs.map fun x => (x.1, x.2.1)) with
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
        unfold Prim.den; rw [hs, hD, hss.objs, hσ]; dsimp only
        rw [dif_pos hc]; exact hR K
      · exact err _ _
    · exact err _ _

/-- `rowOK_args` for a row given no relation (`rowArity s = 0`): only `xs = ss = []`. -/
theorem rowOK_of {s : String} {c : RowCode} {D : RowDen c} {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (A B : Obj) (v : Rel A B), r.sym = s → f σ [] = some ⟨A, B, v⟩ → v.Wf ∧
      ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, K.WF → v.Reps K (hc.1 ▸ hc.2 ▸ D σ []))
    (h0 : rowArity s = 0 := by decide) : RowOK s :=
  rowOK_args hD hf fun r σ xs A B v hs hn hw hv => by
    cases xs with
    | cons => simp [h0] at hn
    | nil =>
      obtain ⟨hw, hR⟩ := h r σ A B v hs hv
      refine ⟨hw, fun ss hss => ?_⟩
      cases ss with
      | nil => exact hR
      | cons => simp [CodesRep] at hss

theorem rowOK_tau : RowOK "τ" := rowOK_of (c := RowCode.tau) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.tau_wf h hX, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.tau_den h hX⟩

theorem rowOK_setify : RowOK "setify" := rowOK_of (c := RowCode.setify) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.setify_wf h hX, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.setify_den h hX⟩

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
theorem lamDen_eq {A B : Obj} {T : Core.Rel (Obj.El A) (Obj.El B)} {a : A.El} {L : List B.El} (hL : L.Pairwise B.lt)
    (hm : ∀ b, b ∈ L ↔ T a b) (zs : List B.El) : lamDen T a zs ↔ zs = L :=
  ⟨fun h => let ⟨hp, hz⟩ := (lamDen_iff _ _ _).1 h; pairwise_eq_of_mem (Obj.lt_irrefl _) (fun _ _ => Obj.lt_asymm _) hp hL
    fun b => (hz b).trans (hm b).symm, fun h => (lamDen_iff _ _ _).2 (by subst h; exact ⟨hL, hm⟩)⟩

/-- **`Λ(cat°)` at `xs`**: the one list strictly ascending in `Obj.lt` of the splits `(p₁, p₂)` of `xs` is the splits by
increasing split point, since a shorter first part is a proper prefix of a longer one. -/
theorem lamDen_splits {B : Obj} {T : Core.Rel (Obj.El (.arr B)) (Obj.El (.prod (.arr B) (.arr B)))} (xs : List B.El)
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
theorem lamDen_inits {B : Obj} {T : Core.Rel (Obj.El (.arr B)) (Obj.El (.arr B))} (xs : List B.El) (hT : ∀ ys, T xs ys ↔ ys <+: xs)
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
    (h : Tab.tails X = .ok T) (wX : Vals.WF X) (xs : List B.El)
    (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  unfold Tab.tails at h
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨L, hL, h⟩ := GenK.bind_ok h
  rcases L with ⟨N, key, m, lo, hi, f⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have wL := Tab.lamOf_wf hL wX (Tab.uncat_wf hU wX)
  -- the cells of `⟨m, lo, hi, f.2⟩` are those of `⟨m, lo, hi, f⟩` mapped by `Prod.snd`
  have hrow : ∀ i, ValsB.row (o := false) (A := .arr (.arr B)) ⟨m, lo, hi, f.2⟩ i =
      (ValsB.row (o := false) (A := .arr (.prod (.arr B) (.arr B))) ⟨m, lo, hi, f⟩ i).map Prod.snd := fun i => by
    have hc := wL.2.2.2.1 i trivial
    rw [ValsB.row_arr i (Arr.flat lo i) (Arr.flat hi i) hc, ValsB.row_arr i (Arr.flat lo i) (Arr.flat hi i) hc,
      List.map_map]
    congr 1; funext k; simp only [Function.comp_apply, apply_dite Prod.snd]; rfl
  obtain ⟨C, hC, wC⟩ := Tab.uncat_canonical hU wX
  have hs : ∀ (hx : ∃ i, X.row i = xs) zs, lamDen C.Holds xs zs ↔
      zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) :=
    fun hx => lamDen_splits xs fun p =>
      (Tab.canon_holds hC wC xs p).symm.trans ((Tab.uncat_holds hU wX xs p).trans (and_iff_right hx))
  constructor
  · rintro ⟨i, hk, hv⟩
    obtain ⟨hx, hd⟩ := (Tab.lamOf_den hC hL wX (Tab.uncat_wf hU wX) wC xs _).1 ⟨i, hk, rfl⟩
    refine ⟨hx, ?_⟩
    rw [← hv, hrow, (hs hx _).1 hd, List.map_map]; rfl
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hk, hv⟩ := (Tab.lamOf_den hC hL wX (Tab.uncat_wf hU wX) wC xs _).2 ⟨hx, (hs hx _).2 rfl⟩
    exact ⟨i, hk, by rw [hrow]; simp only at hv; rw [hv, List.map_map]; rfl⟩

theorem rowOK_tails : RowOK "tails" := rowOK_of (c := RowCode.tails) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.tails_wf h hX, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.tails_den h hX⟩

/-- A row run after the keys (`GenK.after`) represents `P` when `f D`, on the keys' coreflexive `D`, holds `D ≫ P`. -/
theorem GenK.after_row_sound {A B : Obj} {f : {K : Obj} → Tab K A → Except String (Tab K B)}
    {P : Core.Rel A.El B.El}
    (hf : ∀ {K : Obj} (D : Tab K A) t, D.WF → f D = .ok t → ∀ k b, t.Holds k b ↔ ∃ a, D.Holds k a ∧ P a b) :
    ∀ K, K.WF → (GenK.after A B f).Reps K P :=
  GenK.ofVals_row_sound fun _ X t hX h a b => by
    cases hD : Tab.idU X with
    | error e => rw [hD] at h; exact nomatch h
    | ok D =>
    rw [hD] at h
    rw [hf D t (Tab.idU_wf hD hX) h]
    constructor
    · rintro ⟨a', ha', hp⟩; obtain ⟨rfl, hx⟩ := (Tab.idU_holds hD hX a a').1 ha'; exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩; exact ⟨a, (Tab.idU_holds hD hX a a).2 ⟨rfl, hx⟩, hp⟩

/-- A row run after the keys (`GenK.after`) is `Wf` when `f` keeps `Tab.WF` (`Tab.idU_wf`). -/
theorem GenK.after_wf {A B : Obj} {f : {K : Obj} → Tab K A → Except String (Tab K B)}
    (hf : ∀ {K : Obj} (D : Tab K A) t, f D = .ok t → D.WF → t.WF) : (GenK.after A B f).Wf :=
  GenK.ofVals_wf fun _ _ t hX h => by obtain ⟨D, hD, h⟩ := GenK.bind_ok h; exact hf D t h (Tab.idU_wf hD hX)

/-- `stepAfter`'s step `D ≫ F` keeps `Tab.WF` (`compT_wf`), so `f` keeping it makes the row `Wf`. -/
theorem GenK.stepAfter_wf {S T A C : Obj} {F : Rel S T}
    {f : {K : Obj} → (Tab S S → Except String (Tab S T)) → Tab K A → Except String (Tab K C)}
    (hf : ∀ {K : Obj} (q : Tab S S → Except String (Tab S T)), (∀ D t, q D = .ok t → D.WF → t.WF) →
      ∀ (P : Tab K A) t, f q P = .ok t → P.WF → t.WF) (wF : F.Wf) : (GenK.stepAfter S T A C F f).Wf :=
  GenK.after_wf fun P t h wP => hf _ (fun D _ hD wD =>
    (compT_wf (r' := .ok D) (fun _ hr => by cases hr; exact wD) wF).runE Known.wf_empty hD) P t h wP

/-- The pair test `Q` run on a `WF` table's pairs (`testAfter`, `testVals`) answers `WF` tables. -/
theorem GenK.testQ_wf {B : Obj} {Q : Rel (.prod B B) (.prod B B)} (wQ : Q.Wf) :
    ∀ (D : Tab (.prod B B) (.prod B B)) t, Q.runE ⟨some ⟨D.n, D.val⟩, none, none⟩ = .ok t → D.WF → t.WF :=
  fun D _ hD wD => wQ.runE (K := ⟨some ⟨D.n, D.val⟩, none, none⟩) ⟨wD.2, trivial, trivial⟩ hD

theorem GenK.testAfter_wf {B A C : Obj} {Q : Rel (.prod B B) (.prod B B)}
    {f : {K : Obj} → (Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))) → Tab K A →
      Except String (Tab K C)}
    (hf : ∀ {K : Obj} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))),
      (∀ D t, q D = .ok t → D.WF → t.WF) → ∀ (P : Tab K A) t, f q P = .ok t → P.WF → t.WF) (wQ : Q.Wf) :
    (GenK.testAfter B A C Q f).Wf :=
  GenK.after_wf fun P t h wP => hf _ (GenK.testQ_wf wQ) P t h wP

theorem GenK.testVals_wf {B A C : Obj} {Q : Rel (.prod B B) (.prod B B)}
    {f : {n : USize} → (Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))) → Vals A n →
      Except String (Tab A C)}
    (hf : ∀ {n : USize} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))),
      (∀ D t, q D = .ok t → D.WF → t.WF) → ∀ (X : Vals A n) t, f q X = .ok t → Vals.WF X → t.WF) (wQ : Q.Wf) :
    (GenK.testVals B A C Q f).Wf :=
  GenK.ofVals_wf fun _ X t hX h => hf _ (GenK.testQ_wf wQ) X t h hX

/-- `elems`' relation run on the elements in demand (`ran` of `∋`, `WF`) answers a `WF` table. -/
theorem GenK.elems_wf {A B C : Obj} {R : Rel A B}
    {f : {n : USize} → Tab A B → Vals (.arr A) n → Except String (Tab (.arr A) C)}
    (hf : ∀ {n : USize} (P : Tab A B) (X : Vals (.arr A) n) t, f P X = .ok t → P.WF → Vals.WF X → t.WF)
    (wR : R.Wf) : (GenK.elems A B C R f).Wf :=
  GenK.ofVals_wf fun _ X t hX h => by
    obtain ⟨M, hM, h⟩ := GenK.bind_ok h
    obtain ⟨k, hk, h⟩ := GenK.bind_ok h
    obtain ⟨P, hP, h⟩ := GenK.bind_ok h
    exact hf P X t h (wR.runE (K := ⟨some ⟨k.n, k.key⟩, none, none⟩) ⟨(Tab.ran_wf hk (Tab.mem_wf hM hX)).1, trivial, trivial⟩ hP) hX

theorem GenK.onKeys_wf {I A B C : Obj} {R : Rel I C}
    {f : {n : USize} → Vals (.prod I A) n → Tab I C → Except String (Tab (.prod I A) B)}
    (hf : ∀ {n : USize} (X : Vals (.prod I A) n) (P : Tab I C) t, f X P = .ok t → Vals.WF X → P.WF → t.WF)
    (wR : R.Wf) : (GenK.onKeys I A B C R f).Wf :=
  GenK.ofVals_wf fun _ X t hX h => by
    obtain ⟨P, hP, h⟩ := GenK.bind_ok h
    exact hf X P t h hX (wR.runE (K := ⟨some ⟨_, X.1⟩, none, none⟩) ⟨hX.1, trivial, trivial⟩ hP)

/-- `Λ(R)` on `WF` keys, `R` run knowing them (`Tab.lam_wf`); `E(R)` is `Λ(∋ ≫ R)`. -/
theorem GenK.lam_wf {A B : Obj} {R : Rel A B} (wR : R.Wf) : (GenK.lam A B R).Wf := by
  unfold GenK.lam
  exact GenK.ofVals_wf fun _ X _ hX h => let ⟨_, hr, h⟩ := GenK.bind_ok h
    Tab.lam_wf h hX (wR.runE (K := ⟨some ⟨_, X⟩, none, none⟩) ⟨hX, trivial, trivial⟩ hr)

/-- A comparison answers a table of atoms, `WF` with no cell to check. -/
theorem GenK.cmp_wf {op : String} {t : QAtomicType} {o : Except String Kernel.Op} {U : Rel (.atom t) (.atom t)} :
    (GenK.cmp op o U).Wf :=
  fun _ _ => GenK.tab_wf fun _ _ => ⟨trivial, trivial⟩

/-- The folds' rounds (`Tab.foldRounds_wf`), each step `P` paired with an element, then `S` (`compT_wf`). -/
theorem GenK.fold_wf {E V : Obj} {e : Rel V V} {S : Rel (.prod V E) V} (we : e.Wf) (wS : S.Wf) :
    (GenK.fold E V e S).Wf := by
  unfold GenK.fold
  refine GenK.ofVals_wf fun _ X _ hX h => ?_
  obtain ⟨I, hI, h⟩ := GenK.bind_ok h
  obtain ⟨v, hv, h⟩ := GenK.bind_ok h
  obtain ⟨T, hT, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  exact Tab.foldRounds_wf (fun _ _ => Tab.peelL_wf)
    (fun _ _ _ hs wP wel => (GenK.compT_wf (fun _ hp => Tab.pair_wf hp wP wel) wS).runE Known.wf_empty hs) h
    (Tab.idU_wf hI hX) (Tab.top_wf hT hX (we.runE Known.wf_empty hv).2) (Tab.zero_wf hz)
theorem GenK.foldr_wf {E V : Obj} {e : Rel V V} {S : Rel (.prod E V) V} (we : e.Wf) (wS : S.Wf) :
    (GenK.foldr E V e S).Wf := by
  unfold GenK.foldr
  refine GenK.ofVals_wf fun _ X _ hX h => ?_
  obtain ⟨I, hI, h⟩ := GenK.bind_ok h
  obtain ⟨v, hv, h⟩ := GenK.bind_ok h
  obtain ⟨T, hT, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  exact Tab.foldRounds_wf (fun _ _ => Tab.peelR_wf)
    (fun _ _ _ hs wP wel => (GenK.compT_wf (fun _ hp => Tab.pair_wf hp wel wP) wS).runE Known.wf_empty hs) h
    (Tab.idU_wf hI hX) (Tab.top_wf hT hX (we.runE Known.wf_empty hv).2) (Tab.zero_wf hz)
theorem GenK.foldI_wf {I E V : Obj} {e : Rel I (.prod V V)} {S : Rel (.prod (.prod I V) E) (.prod I V)}
    (we : e.Wf) (wS : S.Wf) : (GenK.foldI I E V e S).Wf := by
  unfold GenK.foldI
  refine GenK.ofVals_wf fun _ X _ hX h => ?_
  obtain ⟨i, hi, h⟩ := GenK.bind_ok h
  have wi := Tab.outl_wf hi hX
  obtain ⟨es, hes, h⟩ := GenK.bind_ok h
  have wes := (GenK.compT_wf (r' := .ok i) (fun _ e => by cases e; exact wi) we).runE Known.wf_empty hes
  obtain ⟨b, hb, h⟩ := GenK.bind_ok h
  obtain ⟨c, hc, h⟩ := GenK.bind_ok h
  obtain ⟨p0, hp0, h⟩ := GenK.bind_ok h
  obtain ⟨p, hp, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  obtain ⟨out, hout, h⟩ := GenK.bind_ok h
  obtain ⟨g, hg, h⟩ := GenK.bind_ok h
  have wout := Tab.foldRounds_wf (fun _ _ => Tab.peelL_wf) (fun P el _ hs wP wel => by
      obtain ⟨s, hs', hs⟩ := GenK.bind_ok hs
      have ws := (GenK.compT_wf (fun _ hq => Tab.pair_wf hq wP wel) wS).runE Known.wf_empty hs'
      obtain ⟨o1, h1, hs⟩ := GenK.bind_ok hs
      obtain ⟨o2, h2, hs⟩ := GenK.bind_ok hs
      obtain ⟨o3, h3, hs⟩ := GenK.bind_ok hs
      exact Tab.inter_wf hs ws (Tab.pair_wf h3 wi (Tab.comp_wf h2 ws (Tab.outr_wf h1 ws.2))))
    hout (Tab.outr_wf hb hX) (Tab.pair_wf hp wi (Tab.comp_wf hp0 wes (Tab.outr_wf hc wes.2))) (Tab.zero_wf hz)
  exact Tab.comp_wf h wout (Tab.outr_wf hg wout.2)

theorem rowOK_snoc : RowOK "snoc" := rowOK_of (c := RowCode.snoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.after_wf fun _ _ h w => Tab.snoc_wf h w, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ wD h => Tab.snoc_holds h wD⟩⟩

theorem rowOK_cons : RowOK "cons" := rowOK_of (c := RowCode.cons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.after_wf fun _ _ h w => Tab.cons_wf h w, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ wD h => Tab.cons_holds h wD⟩⟩

theorem rowOK_cat : RowOK "cat" := rowOK_of (c := RowCode.cat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.after_wf fun _ _ h w => Tab.cat_wf h w, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ wD h => Tab.cat_holds h wD⟩⟩

theorem rowOK_uncat : RowOK "uncat" := rowOK_of (c := RowCode.uncat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.uncat_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.uncat_holds h hX⟩⟩

/-- **`cat° ≫ graph f`** on the cells `X` (`Tab.prefix`, `Tab.suffix`): `uncat`'s splits composed with a table `g` of
them that holds `graph f`. -/
theorem Tab.uncat_comp_holds {B : Obj} {n : USize} {X : Vals (.arr B) n}
    {g : {m : USize} → Vals (.prod (.arr B) (.arr B)) m → Except String (Tab (.prod (.arr B) (.arr B)) (.arr B))}
    {f : (Obj.prod (.arr B) (.arr B)).El → List B.El}
    (hg : ∀ m (P : Vals (.prod (.arr B) (.arr B)) m) t, g P = .ok t → Vals.WF P → ∀ p ys,
      t.Holds p ys ↔ (∃ i, P.row i = p) ∧ Core.Rel.graph f p ys)
    (hgw : ∀ m (P : Vals (.prod (.arr B) (.arr B)) m) t, g P = .ok t → Vals.WF P → t.WF)
    {T : Tab (.arr B) (.arr B)} (h : (do let u ← Tab.uncat X; u.comp (← g u.val)) = .ok T) (wX : Vals.WF X)
    (xs ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ∃ p : (Obj.prod (.arr B) (.arr B)).El, xs = p.1 ++ p.2 ∧ ys = f p := by
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨G, hG, h⟩ := GenK.bind_ok h
  have wU := Tab.uncat_wf hU wX
  rw [Tab.comp_holds h wU (hgw _ _ _ hG wU.2)]
  constructor
  · rintro ⟨p, hp, hq⟩
    exact ⟨((Tab.uncat_holds hU wX xs p).1 hp).1, p, ((Tab.uncat_holds hU wX xs p).1 hp).2, ((hg _ _ _ hG wU.2 p ys).1 hq).2⟩
  · rintro ⟨hx, p, he, rfl⟩
    have hp := (Tab.uncat_holds hU wX xs p).2 ⟨hx, he⟩
    obtain ⟨i, -, hv⟩ := hp
    exact ⟨p, (Tab.uncat_holds hU wX xs p).2 ⟨hx, he⟩, (hg _ _ _ hG wU.2 p _).2 ⟨⟨i, hv⟩, rfl⟩⟩

/-- **`prefix`** (`Tab.prefix`) = `cat° ≫ π₁`: each array of `X` to its initial segments. -/
theorem Tab.prefix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.prefix X = .ok T) (wX : Vals.WF X) (xs ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <+: xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outl P) (f := Prod.fst) (fun _ _ _ h hP => Tab.outl_holds h hP)
    (fun _ _ _ h w => Tab.outl_wf h w) h wX]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.2, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(ys, t), ht.symm, rfl⟩⟩

/-- **`suffix`** (`Tab.suffix`) = `cat° ≫ π₂`: each array of `X` to its final segments. -/
theorem Tab.suffix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.suffix X = .ok T) (wX : Vals.WF X) (xs ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <:+ xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outr P) (f := Prod.snd) (fun _ _ _ h hP => Tab.outr_holds h hP)
    (fun _ _ _ h w => Tab.outr_wf h w) h wX]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.1, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(t, ys), ht.symm, rfl⟩⟩

theorem rowOK_prefix : RowOK "prefix" := rowOK_of (c := RowCode.prefix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.prefix_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.prefix_holds h hX⟩⟩

theorem rowOK_suffix : RowOK "suffix" := rowOK_of (c := RowCode.suffix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.suffix_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.suffix_holds h hX⟩⟩

theorem rowOK_uncons : RowOK "uncons" := rowOK_of (c := RowCode.uncons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.uncons_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.uncons_holds h hX⟩⟩

theorem rowOK_unsnoc : RowOK "unsnoc" := rowOK_of (c := RowCode.unsnoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.unsnoc_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.unsnoc_holds h hX⟩⟩

/-- **`inits` on the cells `X`** (`Tab.inits`) = `Λ(prefix)`: each array of `X` to its prefixes by increasing length. -/
theorem Tab.inits_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.inits X = .ok T) (wX : Vals.WF X) (xs : List B.El) (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  unfold Tab.inits at h
  obtain ⟨P, hP, h⟩ := GenK.bind_ok h
  have hP' := hP; unfold Tab.prefix at hP'
  obtain ⟨u, hu, hP'⟩ := GenK.bind_ok hP'; obtain ⟨o, ho, hP'⟩ := GenK.bind_ok hP'
  have wu := Tab.uncat_wf hu wX
  obtain ⟨U, hU, wU, -⟩ := Tab.comp_canon hP' wu (Tab.outl_wf ho wu.2)
  rw [Tab.lamOf_den hU h (wD := wX) (wr := Tab.prefix_wf hP wX) (wR := wU)]
  exact and_congr_right fun hx => lamDen_inits xs (fun ys =>
    (Tab.canon_holds hU wU xs ys).symm.trans ((Tab.prefix_holds hP wX xs ys).trans (and_iff_right hx))) yss

theorem rowOK_inits : RowOK "inits" := rowOK_of (c := RowCode.inits) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.inits_wf h hX, ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.inits_den h hX⟩

theorem rowOK_zip : RowOK "zip" := rowOK_of (c := RowCode.zip) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.after_wf fun _ _ h w => Tab.zip_wf h w, ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ wD h => Tab.zip_holds h wD⟩⟩

theorem rowOK_concat : RowOK "concat" := rowOK_of (c := RowCode.concat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.flatten_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.flatten_holds h hX⟩⟩

theorem rowOK_length : RowOK "length" := rowOK_of (c := RowCode.length) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.length_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.length_holds h hX⟩⟩

/-- `$` at the objects `σ` names: the graph `castDen`, no ordering hypothesis. -/
theorem rowOK_cast : RowOK "$" := rowOK_of (c := RowCode.cast) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.cast_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.cast_den h⟩⟩

/-- `ymd` at the objects `σ` names: the graph `ymdDen`, no ordering hypothesis. -/
theorem rowOK_ymd : RowOK "ymd" := rowOK_of (c := RowCode.ymd) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.ymd_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.ymd_den h⟩⟩

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
          exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.floatOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.floatOp_den rfl h⟩⟩
    | exact rowOK_of (c := ⟨_, fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₂ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
        cases hv
        rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
          exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.floatOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.floatOp_den rfl h⟩⟩

/-- An `arithOps` row at the atom `σ` names: `stepOn` of its verb (`Tab.arithOp_den`), one case per row. -/
theorem rowOK_arith {s : String} (hs : s ∈ arithOps.map (·.1)) : RowOK s := by
  simp only [arithOps, List.map, List.mem_cons, List.not_mem_nil, or_false] at hs
  repeat' (rcases hs with rfl | hs)
  all_goals first | (subst hs) | skip
  all_goals
    exact rowOK_of (c := ⟨_, fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₁ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
      cases hv
      rcases σ with _ | ⟨_, _⟩ <;>
        exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.arithOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.arithOp_den rfl h⟩⟩

/-- `succ` at the atom `σ` names: `succOn` (`Tab.succOp_den`). -/
theorem rowOK_succ : RowOK "succ" := rowOK_of (c := ⟨"succ", fun σ => (σ₁ σ, σ₁ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _⟩ <;>
    exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.succOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.succOp_den h⟩⟩

/-- `at` at the array and index objects `σ` names: `atOn` (`Tab.atRow_den`). -/
theorem rowOK_at : RowOK "at" :=
  rowOK_of (c := ⟨"at", fun σ => (.prod (.arr (σ₁ σ)) (σ₂ σ), σ₁ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
    cases hv
    rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
      exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.atRow_wf h hX,
        ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.atRow_den h hX⟩⟩

/-- `mix` at the atom `σ` names: `mixOn` (`Tab.mixOp_den`). -/
theorem rowOK_mix : RowOK "mix" := rowOK_of (c := ⟨"mix", fun σ => (σ₁ σ, σ₁ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _⟩ <;>
    exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.mixOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.mixOp_den h⟩⟩

/-- A `cmpOps` row at the atom `σ` names: the coreflexive `ordDen` of its order (`Tab.cmpOp_den`), one case per row. -/
theorem rowOK_cmp {s : String} (hs : s ∈ cmpOps.map (·.1)) : RowOK s := by
  simp only [cmpOps, List.map, List.mem_cons, List.not_mem_nil, or_false] at hs
  repeat' (rcases hs with rfl | hs)
  all_goals first | (subst hs) | skip
  all_goals
    exact rowOK_of (c := ⟨_, fun σ => (.prod (σ₁ σ) (σ₁ σ), .prod (σ₁ σ) (σ₁ σ))⟩) rfl rfl fun _ σ _ _ _ _ hv => by
      cases hv
      rcases σ with _ | ⟨_, _⟩ <;>
        exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.cmpOp_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ _ h => Tab.cmpOp_den rfl h⟩⟩

/-- `cmpRelRow` given `U` at the atom `σ` names: `ltDen`, `leqDen` of it (`GenK.cmp_sound`); an error table at any
    other object, whose meaning `ordRelDen` is `𝟘`. -/
theorem rowOK_cmpRel (b : Bool) : RowOK (ordSym b) := by
  cases b <;>
  exact rowOK_args (c := ⟨_, fun σ => (σ₁ σ, σ₁ σ)⟩) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
    rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil,
      show rowArity (ordSym true) = 1 by decide, show rowArity (ordSym false) = 1 by decide] at hn <;> try omega
    rcases σ with _ | ⟨a, σ⟩ <;>
      simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
    all_goals
      split at hv
      case isFalse => simp at hv
      rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
      cases hv
      refine ⟨?_, fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
      · first | exact GenK.cmp_wf | (cases Y <;> first | exact GenK.cmp_wf | exact trivial)
      rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
      split at hss
      case isFalse => exact hss.elim
      rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
      simp only [Sem.one]
      split
      · first
          | exact GenK.cmp_sound hss (hw _ (List.mem_singleton_self _))
          | (cases Y' <;> first
              | exact GenK.cmp_sound hss (hw _ (List.mem_singleton_self _))
              | exact fun _ _ => (GenK.reps_iff _ _ _).2 fun t h => by
                  simp [Rel.Rel.runE, GenK.cmpRel, List.getD_cons_zero] at h)
      · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_sum : RowOK "sum" := rowOK_of (c := RowCode.sum) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.sum_wf h hX, ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.sum_holds h hX⟩⟩

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
    refine ⟨GenK.stepAfter_wf (fun _ hq _ _ h wP => Tab.loop_wf hq h wP) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.loop_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_filter : RowOK "filter" := rowOK_args (c := RowCode.filter) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.elems_wf (fun _ _ _ h wP hX => Tab.filter_wf h wP hX) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.filter_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_takewhile : RowOK "takewhile" :=
  rowOK_args (c := RowCode.takewhile) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.elems_wf (fun _ _ _ h wP hX => Tab.takewhile_wf h wP hX) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.takewhile_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_positions : RowOK "positions" :=
  rowOK_args (c := RowCode.positions) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.elems_wf (fun _ _ _ h wP hX => (Tab.positions_spec h wP hX).2) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.positions_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_asc : RowOK "asc" :=
  rowOK_args (c := RowCode.asc) rfl rfl fun _ σ xs _ _ _ hs hn hw hv => by
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
    refine ⟨GenK.lift1_wf (fun _ _ => Known.wf_empty) (fun _ _ wP h => Tab.asc_wf h wP) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss (hw _ (List.mem_singleton_self _)) fun _ _ h wr hr => by subst hr; exact Tab.asc_holds h wr
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_sums : RowOK "sums" :=
  rowOK_args (c := RowCode.sums) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.lift1_wf (fun _ _ => Known.wf_empty) (fun _ _ wP h => Tab.sums_wf h wP) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss (hw _ (List.mem_singleton_self _)) fun _ _ h wr hr => by subst hr; exact Tab.sums_den h wr
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_F : RowOK "F" := rowOK_args (c := RowCode.map) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.elems_wf (fun _ _ _ h wP hX => Tab.map_wf h wP hX) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact fun K hK => (GenK.reps_iff _ _ _).2 fun t ht x y h1 h2 h3 =>
        ((GenK.reps_iff _ _ _).1 (GenK.map_sound hss (hw _ (List.mem_singleton_self _)) K hK) t ht x y h1 h2 h3).trans
          (mapDen_iff _ x y).symm
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `merge(Q)`, `Expand.primE`'s fit of the row (`testAfter`, `Tab.merge`): each `(x, y)` in demand to
`List.merge x y` under `Q`'s meaning `TQ` as the test, `Q` run on the pairs of heads it is asked about (`est`'s rule). -/
theorem GenK.merge_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))}
    (hQ : ∀ K, K.WF → Q.Reps K TQ) (wQ : Q.Wf) :
    ∀ K, K.WF → (GenK.testAfter B (.prod (.arr B) (.arr B)) (.arr B) Q fun q P => Tab.merge q P).Reps K
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.after_row_sound fun _ _ wP h k zs => Tab.merge_holds (fun D _ wD hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _
      ((GenK.side_some rfl p).2 hp) rfl trivial) (GenK.testQ_wf wQ) h wP k zs

theorem rowOK_merge : RowOK "merge" := rowOK_args (c := RowCode.merge) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.testAfter_wf (fun _ hq _ _ h wP => Tab.merge_wf hq h wP) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.merge_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `thinL(Q)`, `Expand.primE`'s fit of the row (`testVals`, `Tab.thinL`): each array in demand to `thinLDen` under
`Q`'s meaning `TQ` as the test, `Q` run on the pairs it is asked about (`est`'s rule). -/
theorem GenK.thinL_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))}
    (hQ : ∀ K, K.WF → Q.Reps K TQ) (wQ : Q.Wf) :
    ∀ K, K.WF → (GenK.testVals B (.arr B) (.arr B) Q fun q X => Tab.thinL q X).Reps K
      (thinLDen fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.ofVals_row_sound fun _ _ _ hX h xs w => Tab.thinL_holds (fun D _ wD hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _
      ((GenK.side_some rfl p).2 hp) rfl trivial) (GenK.testQ_wf wQ) h hX xs w

theorem rowOK_thinL : RowOK "thinL" := rowOK_args (c := RowCode.thinL) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.testVals_wf (fun _ hq _ _ h hX => Tab.thinL_wf hq h hX) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.thinL_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_est : RowOK "est" := rowOK_args (c := RowCode.est) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "est" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨GenK.testVals_wf (fun _ hq _ _ h hX => Tab.est_wf hq h hX) (hw _ (List.mem_singleton_self _)),
      fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.est_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_front : RowOK "front" := rowOK_args (c := RowCode.front) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "front" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨GenK.testVals_wf (fun _ hq _ _ h hX => Tab.front_wf hq h hX) (hw _ (List.mem_singleton_self _)),
      fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.front_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

/-- `Rᴵ`, `Expand.primE`'s fit of the row (`onKeys`, `Tab.flat`): the `(a', b)` of `R` at the key of each pair in
demand, kept where `a'` is its source, `R` run on the keys in demand. -/
theorem GenK.flat_sound {I A B : Obj} {R : Rel I (.prod A B)} {X : Core.Rel I.El (Obj.prod A B).El}
    (hR : ∀ K, K.WF → R.Reps K X) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.onKeys I A B (.prod A B) R fun X r => Tab.flat X r).Reps K (flatDen X) :=
  GenK.ofVals_sound fun _ _ Xs _ hK wX h p b hp _ _ => by
    obtain ⟨r, hr, ht⟩ := GenK.bind_ok h
    have er := (GenK.reps_iff _ _ _).1 (hR ⟨some ⟨_, Xs.1⟩, none, none⟩ ⟨wX.1, trivial, trivial⟩) r hr
    obtain ⟨i, rfl⟩ := (GenK.side_some hK p).1 hp
    have wr := wR.runE (by exact ⟨wX.1, trivial, trivial⟩) hr
    exact (Tab.flat_holds ht wX wr _ b).trans (((and_iff_right ⟨i, rfl⟩).trans
      (er _ _ ((GenK.side_some rfl _).2 ⟨i, rfl⟩) rfl trivial)).trans (flatDen_iff X (ValsB.row Xs i) b).symm)

theorem rowOK_flat : RowOK "flat" := rowOK_args (c := RowCode.flat) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
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
    refine ⟨GenK.onKeys_wf (fun _ _ _ h hX wR => Tab.flat_wf h hX wR) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.flat_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_foldI : RowOK "foldI" := rowOK_args (c := RowCode.foldI) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have hr : rowArity "foldI" = 2 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨⟨X₂, Y₂, x₂⟩, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, hr] at hn <;> try omega
  rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, σ⟩⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    simp only [Option.bind_some] at hv
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    simp only [Option.bind_some] at hv
    cases hv
    refine ⟨GenK.foldI_wf (hw _ List.mem_cons_self) (hw _ (List.mem_cons_of_mem _ List.mem_cons_self)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨⟨X₂', Y₂', U⟩, _ | ⟨_, _⟩⟩⟩ <;>
      simp only [CodesRep, and_true, and_false] at hss
    obtain ⟨hs1, hs2⟩ := hss
    split at hs1
    case isFalse => exact hs1.elim
    rename_i he; revert hs1; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hs1
    split at hs2
    case isFalse => exact hs2.elim
    rename_i he; revert hs2; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hs2
    simp only [Sem.two]
    split
    · exact GenK.foldI_sound hs1 (hw _ List.mem_cons_self) hs2 (hw _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rename_i h; exact absurd ⟨rfl, rfl, rfl, rfl⟩ h

/-- `star(R)`, `Expand.primE`'s fit of the row (`stepAfter`, `Tab.star`): each key in demand to `μX : 𝟙 ∪ R X`,
    `R` run on the frontier each round meets (`compT_sound`, `Tab.star_holds`). -/
theorem GenK.star_sound {B : Obj} {F : Rel B B} {TF : Core.Rel (Obj.El B) (Obj.El B)} (hF : ∀ K, K.WF → F.Reps K TF)
    (wF : F.Wf) :
    ∀ K, K.WF → (GenK.stepAfter B B B B F fun F P => Tab.star F P).Reps K (Core.Rel.mu fun X => 𝟙 _ ∪ TF ≫ X) := by
  have hF' : ∀ (D : Tab B B) T, (GenK.compT (.ok D) F).runE {} = .ok T → D.WF →
      ∀ a c, T.Holds a c ↔ ∃ b, D.Holds a b ∧ TF b c := fun D T hT wD a c =>
    (GenK.reps_iff _ _ _).1 (GenK.compT_sound (r' := .ok D) (K := {}) (X := rep D)
      (fun _ hr a b _ _ _ => by cases hr; exact Iff.rfl) hF wF Known.wf_empty (fun _ hr => by cases hr; exact wD))
      T hT a c rfl rfl trivial
  have hFw : ∀ (D : Tab B B) T, (GenK.compT (.ok D) F).runE {} = .ok T → D.WF → T.WF :=
    fun D T hT wD => (GenK.compT_wf (r' := .ok D) (fun _ hr => by cases hr; exact wD) wF).runE Known.wf_empty hT
  unfold GenK.stepAfter
  exact GenK.after_row_sound fun _ _ wD h k c => Tab.star_holds hF' hFw wD h k c

theorem rowOK_star : RowOK "star" := rowOK_args (c := RowCode.star) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "star" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨GenK.stepAfter_wf (fun _ hq _ _ h wP => Tab.star_wf hq h wP) (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.star_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_dom : RowOK "dom" := rowOK_args (c := RowCode.dom) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "dom" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨GenK.dom_wf (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.dom_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_ran : RowOK "ran" := rowOK_args (c := RowCode.ran) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "ran" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨GenK.ran_wf (hw _ (List.mem_singleton_self _)), fun ss hss => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ran_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_nil : RowOK "nil" := rowOK_of (c := RowCode.nil) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;> exact ⟨GenK.ofVals_wf fun _ _ _ hX h => Tab.nil_wf h hX,
    ⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ hX h => Tab.nil_holds h hX⟩

/-- Every row of `rowsProved` is `RowOK`: the obligations enumerated from the list `rowGens_proved` checks. -/
theorem rowsProved_ok (r : Prim) (h : r.sym ∈ rowsProved) : RowOK r.sym := by
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
  by_cases h24 : r.sym = "prefix"; · rw [h24]; exact rowOK_prefix
  by_cases h25 : r.sym = "suffix"; · rw [h25]; exact rowOK_suffix
  by_cases h26 : r.sym = "uncons"; · rw [h26]; exact rowOK_uncons
  by_cases h27 : r.sym = "unsnoc"; · rw [h27]; exact rowOK_unsnoc
  by_cases h28 : r.sym = "inits"; · rw [h28]; exact rowOK_inits
  by_cases h29 : r.sym = "takewhile"; · rw [h29]; exact rowOK_takewhile
  by_cases h30 : r.sym = "sums"; · rw [h30]; exact rowOK_sums
  by_cases h31 : r.sym = "flat"; · rw [h31]; exact rowOK_flat
  by_cases h32 : r.sym = "$"; · rw [h32]; exact rowOK_cast
  by_cases h41 : r.sym = "ymd"; · rw [h41]; exact rowOK_ymd
  by_cases h33 : r.sym = "foldI"; · rw [h33]; exact rowOK_foldI
  by_cases h34 : r.sym = "star"; · rw [h34]; exact rowOK_star
  by_cases h35 : r.sym = "dom"; · rw [h35]; exact rowOK_dom
  by_cases h36 : r.sym = "ran"; · rw [h36]; exact rowOK_ran
  by_cases h37 : r.sym = "nil"; · rw [h37]; exact rowOK_nil
  by_cases h38 : r.sym = "est"; · rw [h38]; exact rowOK_est
  by_cases h39 : r.sym = "front"; · rw [h39]; exact rowOK_front
  by_cases hu : r.sym ∈ floatOps.map (·.1); · exact rowOK_float hu
  by_cases ha : r.sym ∈ arithOps.map (·.1); · exact rowOK_arith ha
  by_cases h40 : r.sym = "succ"; · rw [h40]; exact rowOK_succ
  by_cases h42 : r.sym = "mix"; · rw [h42]; exact rowOK_mix
  by_cases h43 : r.sym = "at"; · rw [h43]; exact rowOK_at
  by_cases hc : r.sym ∈ cmpOps.map (·.1); · exact rowOK_cmp hc
  by_cases hc2 : r.sym ∈ cmpOps.map (ordSym ·.2); · simp only [cmpOps, List.map, List.mem_cons, List.not_mem_nil, or_false] at hc2; rcases hc2 with h | h <;> rw [h] <;> exact rowOK_cmpRel _
  simp [rowsProved, hu, ha, hc, hc2, h40, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h41, h42, h43] at h

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
    ∀ ss, CodesRep xs ss → ∀ K, K.WF → (primGen r A B xs).Reps K (Prim.den r A B ss) := by
  have err (e : String) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss, CodesRep xs ss →
      ∀ K, K.WF → (Rel.tab (A := A) (B := B) (.error e)).Reps K (Prim.den r A B ss) :=
    ⟨trivial, fun _ _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
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
    ∀ (η : Code) (xs : Codes) (ds : List Bool), η.Wf → (∀ x ∈ xs, x.2.2.Wf) → (t.argGen η xs ds).Wf := by
  -- strong induction on `Tm.size`: a `hylo`'s children's term (`Tm.kids`) is no subterm, only no larger than its body
  suffices H : ∀ n {A B : Obj} (t : Tm A B), t.size ≤ n → (∀ η : Code, η.Wf → (t.gen η).Wf) ∧
      ∀ (η : Code) (xs : Codes) (ds : List Bool), η.Wf → (∀ x ∈ xs, x.2.2.Wf) → (t.argGen η xs ds).Wf from H _ t (Nat.le_refl _)
  intro n
  induction n
  case zero => intro A B t h; cases t <;> simp [Tm.size] at h
  rename_i n H
  have c : ∀ {C D : Obj} (s : Tm C D), s.size ≤ n → ∀ η : Code, η.Wf → (s.code η).Wf :=
    fun s hs η hη => code_wf ((H s hs).1 η hη)
  intro A B t hn
  cases t <;> simp only [Tm.size] at hn
  case prim r =>
    refine ⟨fun η _ => ?_, fun η xs ds _ hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).1
    · exact (primGen_ok r _ _ xs hx).1
  case arg C D f x =>
    refine ⟨fun η hη => ?_, fun η xs ds hη hx => ?_⟩ <;>
      simp only [Tm.gen, Tm.argGen] <;> refine (H x (by omega)).2 η _ _ hη fun y hy => ?_ <;>
      rcases List.mem_cons.1 hy with rfl | hy
    any_goals exact c f (by omega) η hη
    all_goals first | exact hx y hy | simp at hy
  case call ks _ _ _ b =>
    refine ⟨fun η hη => ?_, fun η xs ds hη hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · split
      · rename_i h; obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h; exact Codes.at_wf hη.2 h
      · exact c b (by omega) _ (Code.args_wf hη ks [] [] fun _ h => nomatch h)
    · exact c b (by omega) _ (Code.args_wf hη ks xs ds hx)
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η hη => ?_, fun η xs ds _ _ => by unfold Tm.argGen; exact trivial⟩
  all_goals simp only [Tm.gen]
  case var k => exact hη.1 k _ _
  case hylo k w b =>
    have := Tm.size_kids k A b
    split
    · trivial
    · exact GenK.hylo_wf (c _ (by omega) η hη) fun X wX => c b (by omega) _ (hη.bind k (GenK.const_wf wX))
  -- each op's `GenK.*_wf` on its operands' codes `w`, a fixed point's body under its variable bound to a `WF` table
  all_goals have w := fun {C D : Obj} (s : Tm C D) (h : s.size ≤ n) => c s h η hη
  case val =>
    refine GenK.val_wf fun h => ?_
    simp only [Bool.and_eq_true] at h; exact ⟨Vals.cellsOk_wf h.1, Vals.cellsOk_wf h.2⟩
  case uni => exact GenK.uni_wf Vals.cellsOk_wf
  case zero => exact GenK.zero_wf
  case id => exact GenK.id_wf
  case top => exact GenK.top_wf (w _ (by omega))
  case outl => exact GenK.ofVals_wf fun _ _ _ hX h => Tab.outl_wf h hX
  case outr => exact GenK.ofVals_wf fun _ _ _ hX h => Tab.outr_wf h hX
  case mem => exact GenK.ofVals_wf fun _ _ _ hX h => Tab.mem_wf h hX
  case inl => exact GenK.ofVals_wf fun _ _ _ hX h => Tab.inl_wf h hX
  case inr => exact GenK.ofVals_wf fun _ _ _ hX h => Tab.inr_wf h hX
  case comp => exact GenK.comp_wf (w _ (by omega)) (w _ (by omega))
  case conv R =>
    split
    · next hc => exact Tm.convInj_wf hc
    · exact GenK.conv_wf (w _ (by omega))
  case meet => exact GenK.meet_wf (w _ (by omega)) (w _ (by omega))
  case join => exact GenK.join_wf (w _ (by omega)) (w _ (by omega))
  case diff => exact GenK.diff_wf (w _ (by omega)) (w _ (by omega))
  case ldiv => exact GenK.ldiv_wf (w _ (by omega)) (w _ (by omega)) (w _ (by omega)) (w _ (by omega))
  case rdiv => exact GenK.rdiv_wf (w _ (by omega)) (w _ (by omega)) (w _ (by omega)) (w _ (by omega))
  case pair => exact GenK.pair_wf (w _ (by omega)) (w _ (by omega))
  case lam => exact GenK.lam_wf (w _ (by omega))
  case fold => exact GenK.fold_wf (w _ (by omega)) (w _ (by omega))
  case foldr => exact GenK.foldr_wf (w _ (by omega)) (w _ (by omega))
  case nu => exact GenK.nu_wf (w _ (by omega)) fun X wX => c _ (by omega) _ (hη.bind _ (GenK.const_wf wX))
  case mu => exact GenK.mu_wf fun X wX => c _ (by omega) _ (hη.bind _ (GenK.const_wf wX))

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** (`Tm.gen_wf_spine`, its first half). -/
theorem Tm.gen_wf {A B : Obj} (t : Tm A B) :
    ∀ η : Code, η.Wf → (t.gen η).Wf := (Tm.gen_wf_spine t).1

/-- `Tm.gen_sound` with its spine half: a spine given codes `xs` that are `Wf` and represent `ss` generates code
    that represents its meaning of `ss` (`Tm.argGen`, `Tm.argDen`). -/
theorem Tm.gen_sound_spine {A B : Obj} (t : Tm A B) :
    (∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, K.WF → (t.gen η).Reps K (t.den ρ)) ∧
    ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem) (ds : List Bool),
      t.GenHyp η.sh.Shares → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
        ∀ K, K.WF → (t.argGen η xs ds).Reps K (t.argDen ρ ss) := by
  -- strong induction on `Tm.size`: a `hylo`'s children's term (`Tm.kids`) is no subterm, only no larger than its body
  suffices H : ∀ n {A B : Obj} (t : Tm A B), t.size ≤ n →
      (∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, K.WF → (t.gen η).Reps K (t.den ρ)) ∧
      ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem) (ds : List Bool),
        t.GenHyp η.sh.Shares → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
          ∀ K, K.WF → (t.argGen η xs ds).Reps K (t.argDen ρ ss) from H _ t (Nat.le_refl _)
  -- a fixed point's round binds its variable to its table (`Sound.bind`)
  have hconst {A B : Obj} (Y : Tab A B) : ∀ K, K.WF → (GenK.const A B (.ok Y)).Reps K (rep Y) :=
    fun _ _ => (GenK.reps_iff _ _ _).2 fun t ht x y _ _ _ => by cases ht; exact Iff.rfl
  -- an error table runs to no table, so it represents every meaning
  have herr {A B : Obj} (e : String) (X : Core.Rel (Obj.El A) (Obj.El B)) : ∀ K, K.WF → (Rel.tab (A := A) (B := B) (.error e)).Reps K X :=
    fun _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h
  intro n
  induction n
  case zero => intro A B t h; cases t <;> simp [Tm.size] at h
  rename_i n H
  intro A B t
  induction t <;> intro hn <;> simp only [Tm.size] at hn
  case prim r =>
    refine ⟨fun η ρ _ _ => ?_, fun η ρ xs ss ds _ _ hx hr => ?_⟩ <;>
      simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).2 [] trivial
    · exact (primGen_ok r _ _ xs hx).2 ss hr
  case arg C D f x ihf ihx =>
    have step (η ρ) (xs : Codes) (ss : List Sem) (ds : List Bool)
        (hl : f.GenHyp η.sh.Shares ∧ x.GenHyp η.sh.Shares) (hs : Sound η ρ) (hx : ∀ y ∈ xs, y.2.2.Wf) (hr : CodesRep xs ss) :
        ∀ K, K.WF → (f.argGen η (⟨C, D, x.code η⟩ :: xs) ds).Reps K (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) :=
      (ihf (by omega)).2 η ρ _ _ _ hl.1 hs (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact code_wf (gen_wf x η hs.2)
          · exact hx y hy)
        ⟨by rw [dif_pos ⟨rfl, rfl⟩]; exact code_of ((ihx (by omega)).1 η ρ hl.2 hs), hr⟩
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss ds hl hs hx hr => ?_⟩ <;>
      simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact step η ρ [] [] _ hl hs (fun _ h => nomatch h) trivial
    · exact step η ρ xs ss _ hl hs hx hr
  -- a slot where the table has one (`Codes.Shares`; its meaning is the body's under no variable, `Val.args ks []`),
  -- else the body under its arguments bound at `ks` (`Sound.args`), whatever the caller's `η`, `ρ`; same table
  case call ks _ _ _ b ih =>
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss ds hl hs hx hr => ?_⟩ <;>
      simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · intro K; split
      · rename_i r h; obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.1 h; cases ks <;> exact hl.1 k hk r h K
      · exact code_of ((ih (by omega)).1 _ _ (by rw [Code.args_sh]; exact hl.2)
          (Sound.args hs ks [] [] [] (fun _ h => nomatch h) trivial)) K
    · exact code_of ((ih (by omega)).1 _ _ (by rw [Code.args_sh]; exact hl.2)
        (Sound.args hs ks xs ss ds hx hr))
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss ds _ _ _ _ => by unfold Tm.argGen; exact herr _ _⟩
  all_goals simp only [Tm.GenHyp] at hl <;> simp only [Tm.gen, Tm.den]
  case val R => exact GenK.val_sound _ fun h => by simp only [Bool.and_eq_true] at h; exact ⟨Vals.cellsOk_wf h.1, Vals.cellsOk_wf h.2⟩
  case uni U => exact GenK.uni_sound _ Vals.cellsOk_wf
  case zero => exact GenK.zero_sound
  case id => exact GenK.id_sound
  case top V ih => exact GenK.top_sound (code_of ((ih (by omega)).1 η ρ hl hs)) (code_wf (gen_wf V η hs.2))
  case outl => exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.outl_holds h hX
  case outr => exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.outr_holds h hX
  case comp R S ihR ihS =>
    exact GenK.comp_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case conv R ih =>
    split
    · next hc => exact Tm.convInj_sound ρ hc
    · exact GenK.conv_sound (code_of ((ih (by omega)).1 η ρ hl hs)) (code_wf (gen_wf R η hs.2))
  case meet R S ihR ihS =>
    exact GenK.meet_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case join R S ihR ihS =>
    exact GenK.join_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case diff R S ihR ihS =>
    exact GenK.diff_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case rdiv R S U V ihR ihS ihU ihV =>
    exact GenK.rdiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2)) (code_wf (gen_wf U η hs.2)) (code_wf (gen_wf V η hs.2))
  case ldiv R S U V ihR ihS ihU ihV =>
    exact GenK.ldiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2)) (code_wf (gen_wf U η hs.2)) (code_wf (gen_wf V η hs.2))
  case pair R S ihR ihS =>
    exact GenK.pair_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case fold R S ihR ihS =>
    exact GenK.fold_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_wf (gen_wf R η hs.2)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case foldr R S ihR ihS =>
    exact GenK.foldr_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_wf (gen_wf R η hs.2)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case lam R ih => exact GenK.lam_sound (code_of ((ih (by omega)).1 η ρ hl hs)) (code_wf (gen_wf R η hs.2))
  case mem => exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.mem_holds h hX
  case inl => exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.inl_holds h hX
  case inr => exact GenK.ofVals_row_sound fun _ _ _ hX h => Tab.inr_holds h hX
  case var k => exact hs.1 k _ _
  case nu k S b ihS ihb =>
    exact GenK.nu_sound (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs)) (code_wf (gen_wf S η hs.2))
      (fun X wX => code_of ((ihb (by omega)).1 _ _ hl.2.2 (hs.bind k (hconst X) wX)))
      (fun X wX => code_wf (gen_wf b _ (hs.bind k (hconst X) wX).2)) fun _ _ h => Tm.den_mono hl.1 h
  case mu k w m b ih =>
    exact GenK.mu_sound (fun X wX => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst X) wX)))
      (fun X wX => code_wf (gen_wf b _ (hs.bind k (hconst X) wX).2)) (fun _ _ h => Tm.den_mono hl.1 h)
      fun hlin X Y => Tm.den_linIn hlin _ X Y
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
        (fun Y wY => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst Y) wY)))
        (fun Y wY => code_wf (gen_wf b _ (hs.bind k (hconst Y) wY).2))
        (fun _ _ h => Tm.den_mono hl.1 h) (fun X Y a h => Tm.den_local k ρ X Y b c hk a h)

/-- **`Tm.gen` is sound**: the code of every term represents its meaning in every context, given each fixed point's body
    positive and each shared slot its part's meaning (`Tm.GenHyp`), and an environment `η` that represents `ρ`;
    where the code is an error table (`Tm.hasCode` false) the run fails, which represents every meaning. -/
theorem Tm.gen_sound {A B : Obj} (t : Tm A B) :
    ∀ (η : Code) (ρ : Val), t.GenHyp η.sh.Shares → Sound η ρ → ∀ K, K.WF → (t.gen η).Reps K (t.den ρ) :=
  (Tm.gen_sound_spine t).1

/-! ### `Code.program` meets `Codes.Shares`

The share table `Code.shares ts` is `Sound` and its slot `k` represents `ts[k]`'s meaning wherever every slot term
reads the table literally (`Res.Slot`: at each `share j R`, `R` is slot `j`'s term). `Tm.number` keeps that
(`Tm.number_spec`), so the terms `Code.program` numbers meet `Tm.GenHyp` under their table (`Code.program_sound`). -/

/-- `R` is the term of slot `k` of `ts` at its objects. -/
def Res.Slot (ts : Array Res) {A B : Obj} (k : Nat) (R : Tm A B) : Prop := ts[k]? = some ⟨A, B, R⟩

theorem Tm.GenHyp.mono {P Q : {A B : Obj} → Nat → Tm A B → Prop}
    (hPQ : ∀ {A B : Obj} (k : Nat) (R : Tm A B), P k R → Q k R) {A B : Obj} {t : Tm A B} (h : t.GenHyp P) :
    t.GenHyp Q := by
  induction t <;> simp_all [Tm.GenHyp]

theorem Tm.GenHyp.slot {P : {A B : Obj} → Nat → Tm A B → Prop} {A B : Obj} {k : Nat} {R : Tm A B} (h : P k R)
    (hR : R.GenHyp P) : (Tm.slot k R).GenHyp P :=
  ⟨fun j hj => by obtain rfl := Option.some.inj (hj.symm.trans rfl); exact h, hR⟩

theorem Tm.pol_of_fv{A B : Obj} (t : Tm A B) : ∀ (s : Bool) (k : Nat), k ∉ t.fv → t.pol s k = true := by
  induction t with
  | arg f x ihf ihx => intro s k h; cases f <;> simp_all [Tm.pol, Tm.fv] <;> grind
  | _ => intro s k h; simp only [Tm.pol, Tm.fv] at h ⊢ <;> grind

/-- Every slot's term reads the table as a definition does: at each `share j R`, `R` is slot `j`'s term. -/
def Shares.Inv (s : Shares) : Prop := ∀ x ∈ s.1, x.2.2.GenHyp (Res.Slot s.1)

/-- `ts'` keeps every slot of `ts`. -/
abbrev Shares.Ext (ts ts' : Array Res) : Prop := ∀ (k : Nat) (x : Res), ts[k]? = some x → ts'[k]? = some x

theorem Shares.Ext.trans {a b c : Array Res} (h1 : Shares.Ext a b) (h2 : Shares.Ext b c) : Shares.Ext a c :=
  fun k x h => h2 k x (h1 k x h)

theorem Shares.Ext.push (ts : Array Res) (y : Res) : Shares.Ext ts (ts.push y) := fun k x h => by
  have : k < ts.size := (Array.getElem?_eq_some_iff.1 h).1
  rw [Array.getElem?_push, if_neg (by omega)]; exact h

theorem Tm.GenHyp.ext {ts ts' : Array Res} (he : Shares.Ext ts ts') {A B : Obj} {t : Tm A B}
    (h : t.GenHyp (Res.Slot ts)) : t.GenHyp (Res.Slot ts') :=
  Tm.GenHyp.mono (fun k _ hR => he k _ hR) h

/-- What numbering `t` to `t'` keeps, the table at `ts`: `t'` reads it (`Res.Slot`), has no more free variables,
    no worse a sign of any, and a row stays itself (a spine's head, `Tm.pol`). -/
def NOut {A B : Obj} (t t' : Tm A B) (ts : Array Res) : Prop :=
  t'.GenHyp (Res.Slot ts) ∧ (∀ k ∈ t'.fv, k ∈ t.fv) ∧ (∀ s k, t.pol s k = true → t'.pol s k = true) ∧
    (∀ r, t = .prim r → t' = t)

theorem NOut.ext {A B : Obj} {t t' : Tm A B} {ts ts' : Array Res} (h : NOut t t' ts) (he : Shares.Ext ts ts') :
    NOut t t' ts' := ⟨h.1.ext he, h.2⟩

theorem NOut.trans {A B : Obj} {t t1 t2 : Tm A B} {ts : Array Res} (h1 : NOut t t1 ts) (h2 : NOut t1 t2 ts) :
    NOut t t2 ts :=
  ⟨h2.1, fun k hk => h1.2.1 k (h2.2.1 k hk), fun s k h => h2.2.2.1 s k (h1.2.2.1 s k h),
    fun r h => by rw [h2.2.2.2 r (by rw [h1.2.2.2 r h]; exact h), h1.2.2.2 r h]⟩

/-- `x`, run from a table every slot of which reads it, keeps that, keeps every slot, and numbers `t`. -/
def NSpec {A B : Obj} (t : Tm A B) (x : StateM Shares (Tm A B)) : Prop :=
  ∀ s, Shares.Inv s → Shares.Inv (x.run s).2 ∧ Shares.Ext s.1 (x.run s).2.1 ∧ NOut t (x.run s).1 (x.run s).2.1

theorem closed_prim {A B : Obj} (r : Prim) : Expand.closed (Tm.prim (A := A) (B := B) r) = false := by
  simp [Expand.closed, Tm.dem]

theorem numberSlot_spec {A B : Obj} (t : Tm A B) (s : Shares) (hs : Shares.Inv s) (ht : t.GenHyp (Res.Slot s.1)) :
    Shares.Inv (t.numberSlot.run s).2 ∧ Shares.Ext s.1 (t.numberSlot.run s).2.1 ∧
      NOut t (t.numberSlot.run s).1 (t.numberSlot.run s).2.1 := by
  have refl : NOut t t s.1 := ⟨ht, fun _ h => h, fun _ _ h => h, fun _ _ => rfl⟩
  have np : Expand.closed t = true → ∀ r, t ≠ .prim r := fun h r e => by
    subst e; rw [closed_prim] at h; cases h
  -- a new slot: `t` pushed
  have new : ∀ m, Expand.closed t = true →
      let s' : Shares := (s.1.push ⟨A, B, t⟩, m)
      Shares.Inv s' ∧ Shares.Ext s.1 s'.1 ∧ NOut t (.slot s.1.size t) s'.1 := fun m h => by
    have he := Shares.Ext.push s.1 ⟨A, B, t⟩
    refine ⟨fun x hx => ?_, he, ⟨.slot (by simp [Res.Slot]) (ht.ext he), by simp [Tm.slot, Tm.fv], fun _ _ _ => by simp [Tm.slot, Tm.pol],
      by simp [np h]⟩⟩
    rcases Array.mem_push.1 hx with hx | hx
    · exact (hs x hx).ext he
    · subst hx; exact ht.ext he
  obtain ⟨ts, m⟩ := s
  simp only [Tm.numberSlot, StateT.run]
  by_cases h : Expand.closed t = true
  · simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · exact new m h
    · split
      · exact new _ h
      · split
        · split
          · rename_i hAB
            obtain ⟨rfl, rfl⟩ := hAB
            rename_i hk _
            refine ⟨hs, fun _ _ x => x, ⟨.slot hk (hs _ (Array.mem_of_getElem? hk)), by simp [Tm.slot, Tm.fv],
              fun _ _ _ => by simp [Tm.slot, Tm.pol], fun r e => absurd e (np h r)⟩⟩
          · exact new m h
        · exact new m h
  · simp only [h, Bool.not_false, if_true]
    exact ⟨hs, fun _ _ x => x, refl⟩

/-- One step of `Code.shares`: the slot of `x` under the slots `σ` before it. -/
private abbrev shStep (σ : Codes) (x : Res) : Codes := σ ++ [⟨x.1, x.2.1, x.2.2.code { Code.empty with sh := σ }⟩]

private theorem shFold_take : ∀ (l : List Res) (acc : Codes),
    (l.foldl shStep acc).take acc.length = acc ∧ (l.foldl shStep acc).length = acc.length + l.length
  | [], acc => by simp
  | x :: l, acc => by
    obtain ⟨h1, h2⟩ := shFold_take l (shStep acc x)
    refine ⟨?_, by simp [h2]; omega⟩
    simp only [List.foldl_cons]
    calc _ = ((l.foldl shStep (shStep acc x)).take (shStep acc x).length).take acc.length := by
            rw [List.take_take]; congr 1; simp
      _ = acc := by rw [h1]; simp

private theorem shFold_get : ∀ (l : List Res) (acc : Codes) (i : Nat) (x : Res), l[i]? = some x →
    (l.foldl shStep acc)[acc.length + i]? =
      some ⟨x.1, x.2.1, x.2.2.code { Code.empty with sh := (l.foldl shStep acc).take (acc.length + i) }⟩
  | [], _, _, _, h => by simp at h
  | y :: l, acc, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    have h0 := (shFold_take (y :: l) acc).1
    have h1 := (shFold_take l (shStep acc y)).1
    simp only [List.foldl_cons] at h0 ⊢
    simp only [Nat.add_zero, h0]
    rw [← List.getElem?_take_of_lt (Nat.lt_succ_self acc.length),
      show acc.length.succ = (shStep acc y).length by simp, h1]; simp
  | y :: l, acc, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    have := shFold_get l (shStep acc y) i x h
    simp only [List.foldl_cons]
    have e : (shStep acc y).length + i = acc.length + (i + 1) := by simp; omega
    rw [e] at this; exact this

private theorem shFold_wf : ∀ (l : List Res) (acc : Codes), (∀ x ∈ acc, x.2.2.Wf) →
    ∀ x ∈ l.foldl shStep acc, x.2.2.Wf
  | [], _, h => h
  | y :: l, acc, h => shFold_wf l _ fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact h x hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact Tm.code_wf (Tm.gen_wf _ _ ⟨fun _ _ _ => GenK.zero_wf, h⟩)

private theorem shares_sh (ts : Array Res) : (Code.shares ts).sh = ts.toList.foldl shStep [] := by
  simp only [Code.shares]; rw [← Array.foldl_toList]

/-- **The share table is sound** where each slot's term reads, at each of its `share j R`, the slot `j` itself
    (`Res.Slot`): the table represents the empty context, and its slot `k` the meaning of the term numbered `k`
    (`Codes.Shares`), so a term that reads the table the same way meets `Tm.GenHyp` (`Tm.GenHyp.mono`). -/
theorem Code.shares_sound (ts : Array Res) (hts : ∀ x ∈ ts, x.2.2.GenHyp (Res.Slot ts)) :
    Sound (Code.shares ts) Val.empty ∧
      ∀ {A B : Obj} (k : Nat) (R : Tm A B), Res.Slot ts k R → (Code.shares ts).sh.Shares k R := by
  have hwf : ∀ x ∈ (Code.shares ts).sh, x.2.2.Wf := by
    rw [shares_sh]; exact shFold_wf _ _ fun _ h => nomatch h
  have hs : ∀ k, Sound { Code.empty with sh := (Code.shares ts).sh.take k } Val.empty := fun k =>
    ⟨fun _ _ _ K => GenK.zero_sound K, fun _ _ _ => GenK.zero_wf, fun x hx => hwf x (List.mem_of_mem_take hx)⟩
  refine ⟨⟨fun _ _ _ K => GenK.zero_sound K, fun _ _ _ => GenK.zero_wf, hwf⟩, ?_⟩
  suffices H : ∀ n k, k < n → ∀ {A B : Obj} (R : Tm A B), Res.Slot ts k R → (Code.shares ts).sh.Shares k R from
    fun {_ _} k R h => H (k + 1) k (by omega) R h
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk A B R hR r hr K
    have hget := shFold_get ts.toList [] k ⟨A, B, R⟩ (by simpa [Res.Slot] using hR)
    rw [← shares_sh] at hget
    simp only [List.length_nil, Nat.zero_add] at hget
    unfold Codes.at at hr; rw [hget] at hr; simp at hr; subst hr
    refine Tm.code_of (Tm.gen_sound R _ _ ?_ (hs k)) K
    refine Tm.GenHyp.mono ?_ (hts _ (Array.mem_of_getElem? hR))
    intro A' B' j R' hj r' hr'
    by_cases hjk : j < k
    · have e : Codes.at ((Code.shares ts).sh.take k) j A' B' = (Code.shares ts).sh.at j A' B' := by
        simp [Codes.at, hjk]
      exact ih j (by omega) R' hj r' (e ▸ hr')
    · simp [Codes.at, List.getElem?_take, hjk] at hr'

theorem NSpec.bindSlot {A B : Obj} {t : Tm A B} {x : StateM Shares (Tm A B)} (h : NSpec t x) :
    NSpec t (x >>= Tm.numberSlot) := fun s hs => by
  obtain ⟨i1, e1, o1⟩ := h s hs
  obtain ⟨i2, e2, o2⟩ := numberSlot_spec _ _ i1 o1.1
  exact ⟨i2, e1.trans e2, (o1.ext e2).trans o2⟩

theorem NSpec.bindWrap {A B : Obj} {t : Tm A B} {x : StateM Shares (Tm A B)} (h : NSpec t x) (hd : Bool) :
    NSpec t (x >>= Tm.numberWrap hd) := by
  cases hd
  · exact NSpec.bindSlot h
  · exact fun s hs => h s hs

theorem NSpec.pure {A B : Obj} {t : Tm A B} (h : ∀ ts, t.GenHyp (Res.Slot ts)) : NSpec t (pure t) := fun _ hs =>
  ⟨hs, fun _ _ x => x, h _, fun _ h => h, fun _ _ h => h, fun _ _ => rfl⟩

theorem NSpec.map1 {A B A' B' : Obj} {t : Tm A B} {R : Tm A' B'} {x : StateM Shares (Tm A' B')}
    (C : Tm A' B' → Tm A B) (h : NSpec R x) (hC : ∀ ts a, NOut R a ts → NOut t (C a) ts) :
    NSpec t (do return C (← x)) := fun s hs => by
  obtain ⟨i1, e1, o1⟩ := h s hs
  exact ⟨i1, e1, hC _ _ o1⟩

theorem NSpec.map2 {A B A1 B1 A2 B2 : Obj} {t : Tm A B} {R : Tm A1 B1} {S : Tm A2 B2}
    {x : StateM Shares (Tm A1 B1)} {y : StateM Shares (Tm A2 B2)}
    (C : Tm A1 B1 → Tm A2 B2 → Tm A B) (hx : NSpec R x) (hy : NSpec S y)
    (hC : ∀ ts a b, NOut R a ts → NOut S b ts → NOut t (C a b) ts) :
    NSpec t (do return C (← x) (← y)) := fun s hs => by
  obtain ⟨i1, e1, o1⟩ := hx s hs
  obtain ⟨i2, e2, o2⟩ := hy _ i1
  exact ⟨i2, e1.trans e2, hC _ _ _ (o1.ext e2) o2⟩

/-- `NSpec.map2` given a fact `Q` of every term `x` returns, which `hC` reads (a spine's head, `Tm.number_spine`). -/
theorem NSpec.map2Q {A B A1 B1 A2 B2 : Obj} {t : Tm A B} {R : Tm A1 B1} {S : Tm A2 B2}
    {x : StateM Shares (Tm A1 B1)} {y : StateM Shares (Tm A2 B2)} {Q : Tm A1 B1 → Prop}
    (C : Tm A1 B1 → Tm A2 B2 → Tm A B) (hx : NSpec R x) (hq : ∀ s, Shares.Inv s → Q (x.run s).1)
    (hy : NSpec S y) (hC : ∀ ts a b, Q a → NOut R a ts → NOut S b ts → NOut t (C a b) ts) :
    NSpec t (do return C (← x) (← y)) := fun s hs => by
  obtain ⟨i1, e1, o1⟩ := hx s hs
  obtain ⟨i2, e2, o2⟩ := hy _ i1
  exact ⟨i2, e1.trans e2, hC _ _ _ (hq s hs) (o1.ext e2) o2⟩

theorem NSpec.map4 {A B A1 B1 A2 B2 A3 B3 A4 B4 : Obj} {t : Tm A B} {R : Tm A1 B1} {S : Tm A2 B2}
    {U : Tm A3 B3} {V : Tm A4 B4} {x : StateM Shares (Tm A1 B1)} {y : StateM Shares (Tm A2 B2)}
    {z : StateM Shares (Tm A3 B3)} {w : StateM Shares (Tm A4 B4)}
    (C : Tm A1 B1 → Tm A2 B2 → Tm A3 B3 → Tm A4 B4 → Tm A B) (hx : NSpec R x) (hy : NSpec S y) (hz : NSpec U z)
    (hw : NSpec V w) (hC : ∀ ts a b c d, NOut R a ts → NOut S b ts → NOut U c ts → NOut V d ts → NOut t (C a b c d) ts) :
    NSpec t (do return C (← x) (← y) (← z) (← w)) := fun s hs => by
  obtain ⟨i1, e1, o1⟩ := hx s hs
  obtain ⟨i2, e2, o2⟩ := hy _ i1
  obtain ⟨i3, e3, o3⟩ := hz _ i2
  obtain ⟨i4, e4, o4⟩ := hw _ i3
  exact ⟨i4, e1.trans (e2.trans (e3.trans e4)), hC _ _ _ _ _ (((o1.ext e2).ext e3).ext e4) ((o2.ext e3).ext e4)
    (o3.ext e4) o4⟩

/-- The side conditions of one constructor: each part's numbering reads the table, so the node does. -/
local macro "nout" : tactic => `(tactic| (
  intros
  simp only [NOut] at *
  refine ⟨?_, ?_, ?_, fun _ e => by cases e⟩
  · (try simp only [Tm.GenHyp] at *); grind
  · (try simp only [Tm.fv, List.mem_append, List.mem_filter, List.not_mem_nil] at *); grind
  · (try simp only [Tm.pol, Tm.fv, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      List.contains_iff_mem, decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq] at *); grind))

/-- The constructors `Tm.number` numbers through `Tm.mapMSz`: all but a spine's nodes (a call, a slot included). -/
def Tm.numGeneric : {A B : Obj} → Tm A B → Bool
  | _, _, .arg .. | _, _, .call .. => false
  | _, _, _ => true

theorem Tm.number_mapMSz {A B : Obj} (t : Tm A B) (h : t.numGeneric = true) (hd : Bool) :
    t.number hd = (t.mapMSz fun c _ => c.number) >>= Tm.numberSlot := by
  cases t <;> simp only [Tm.numGeneric, Bool.false_eq_true] at h <;> rw [Tm.number.eq_def]

set_option hygiene false in
local macro "gh" : tactic =>
  `(tactic| first | exact hg | exact hg.1 | exact hg.2 | exact hg.2.1 | exact hg.2.2 | exact hg.2.2.1 | exact hg.2.2.2)

set_option hygiene false in
/-- One goal of a `NSpec.map*`: a part's spec by `ih`, the node's `NOut`, or a part's term (fixed by the others). -/
local macro "part" : tactic =>
  `(tactic| first | (refine ih _ ?_ ?_ <;> first | (simp only [Tm.size]; omega) | gh) | nout | skip)

theorem Tm.mapMSz_spec {A B : Obj} (t : Tm A B) (h : t.numGeneric = true) (hg : t.GenHyp fun _ R => R.fv = [])
    (ih : ∀ {C D : Obj} (c : Tm C D), c.size < t.size → c.GenHyp (fun _ R => R.fv = []) → NSpec c (c.number false)) :
    NSpec t (t.mapMSz fun c _ => c.number) := by
  cases t <;> simp only [Tm.numGeneric, Bool.false_eq_true] at h <;> simp only [Tm.GenHyp] at hg <;>
    dsimp only [Tm.mapMSz]
  all_goals first
    | exact NSpec.pure fun _ => by simp [Tm.GenHyp]
    | (refine NSpec.map1 (R := ?_) _ ?_ ?_ <;> part)
    | (refine NSpec.map2 (R := ?_) (S := ?_) _ ?_ ?_ ?_ <;> part)
    | (refine NSpec.map4 (R := ?_) (S := ?_) (U := ?_) (V := ?_) _ ?_ ?_ ?_ ?_ ?_ <;> part)

/-- A spine numbered at its head (`hd`) stays a spine of its row with each argument's sign kept: no slot is made
    at the head (`Tm.numberWrap`), a row is never closed (`closed_prim`), and each argument keeps `Tm.pol` (`NOut`). -/
theorem Tm.number_spine {A B : Obj} (t : Tm A B) (s : Bool) (k : Nat) (hg : t.GenHyp fun _ R => R.fv = [])
    (ih : ∀ {C D : Obj} (c : Tm C D), c.size ≤ t.size → c.GenHyp (fun _ R => R.fv = []) → ∀ hd,
      NSpec c (c.number hd))
    (hp : t.spinePol s k = true) (st : Shares) (hs : Shares.Inv st) :
    ((t.number true).run st).1.spinePol s k = true := by
  induction t generalizing st with
  | prim r => rw [(ih _ (Nat.le_refl _) hg true st hs).2.2.2.2.2 r rfl]; exact hp
  | arg f x ihf _ =>
    simp only [Tm.spinePol, Bool.and_eq_true] at hp
    simp only [Tm.GenHyp] at hg
    have hf := ih f (by simp only [Tm.size]; omega) hg.1 true st hs
    have hx := ih x (by simp only [Tm.size]; omega) hg.2 false _ hf.1
    rw [Tm.number.eq_def]
    show Tm.spinePol s k (.arg ((f.number true).run st).1 ((x.number).run ((f.number true).run st).2).1) = true
    simp only [Tm.spinePol, Bool.and_eq_true]
    exact ⟨ihf hg.1 (fun c hc => ih c (by simp only [Tm.size]; omega)) hp.1 st hs, hx.2.2.2.2.1 s k hp.2⟩
  | _ => simp [Tm.spinePol] at hp

/-- **`Tm.number` keeps the table read literally**: from a table each slot of which reads it (`Shares.Inv`), a term
    whose every shared part is closed numbers to one that reads the extended table (`NSpec`). -/
theorem Tm.number_spec : ∀ (n : Nat) {A B : Obj} (t : Tm A B), t.size ≤ n →
    t.GenHyp (fun _ R => R.fv = []) → ∀ hd, NSpec t (t.number hd) := by
  intro n
  induction n with
  | zero => intro A B t h; cases t <;> simp [Tm.size] at h
  | succ n ih =>
    intro A B t hn hg hd
    cases hk : t.numGeneric
    · cases t <;> simp only [Tm.numGeneric, Bool.true_eq_false] at hk <;> simp only [Tm.GenHyp] at hg <;>
        simp only [Tm.size] at hn <;> rw [Tm.number.eq_def] <;> dsimp only
      case call ks c cv os b =>
        by_cases hc : c.slot?.isSome = true
        · -- a slot is its body numbered, whose part is closed
          rw [if_pos hc]
          intro s hs
          obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hc
          obtain ⟨i, e, o⟩ := ih b (by omega) hg.2 hd s hs
          have hn : ∀ j, j ∉ ((b.number hd).run s).1.fv := fun j hj => by simpa [hg.1 k hk] using o.2.1 j hj
          exact ⟨i, e, o.1, fun j hj => absurd hj (hn j), fun b j _ => Tm.pol_of_fv _ b j (hn j),
            fun _ e => by cases e⟩
        · rw [if_neg hc]
          have hc' : ∀ k, c.slot? ≠ some k := fun k h => hc (by simp [h])
          exact NSpec.bindWrap (NSpec.map1 _ (ih b (by omega) hg.2 false) (by nout)) hd
      case arg C D f x =>
        -- `cases` binds the function as `x` and the argument as `f`
        refine NSpec.bindWrap (NSpec.map2Q (Q := fun a => ∀ s k, x.spinePol s k = true → a.spinePol s k = true)
          (fun a b => .arg a b) (ih x (by omega) hg.1 true)
          (fun st hst s k h => Tm.number_spine x s k hg.1 (fun c hc hgc => ih c (by omega) hgc) h st hst)
          (ih f (by omega) hg.2 false) ?_) hd
        intro ts a b q ⟨g1, f1, p1, r1⟩ ⟨g2, f2, p2, _⟩
        refine ⟨⟨g1, g2⟩, fun k hk => ?_, fun s k hp => ?_, fun _ e => by cases e⟩
        · simp only [Tm.fv, List.mem_append] at hk ⊢; grind
        · by_cases hk : k ∈ (Tm.arg a b).fv
          · have hk' : k ∈ (Tm.arg x f).fv := by simp only [Tm.fv, List.mem_append] at hk ⊢; grind
            have hp : x.spinePol s k = true ∧ f.pol s k = true := by simpa [Tm.pol, hk'] using hp
            simp only [Tm.pol, Bool.or_eq_true, Bool.and_eq_true]
            exact Or.inl ⟨q s k hp.1, p2 s k hp.2⟩
          · exact Tm.pol_of_fv _ s k hk
    · rw [Tm.number_mapMSz t hk]
      exact NSpec.bindSlot (Tm.mapMSz_spec t hk hg fun c hc hgc => ih c (by omega) hgc false)

theorem Code.program_go : ∀ (ds : List Res), (∀ d ∈ ds, d.2.2.GenHyp fun _ R => R.fv = []) → ∀ s, Shares.Inv s →
    let r := (ds.mapM (m := StateM Shares) fun (r : Res) => do pure (⟨r.1, r.2.1, ← r.2.2.number⟩ : Res)).run s
    Shares.Inv r.2 ∧ Shares.Ext s.1 r.2.1 ∧ ∀ d ∈ r.1, d.2.2.GenHyp (Res.Slot r.2.1)
  | [], _, s, hs => ⟨hs, fun _ _ x => x, fun _ h => nomatch h⟩
  | d :: ds, h, s, hs => by
    obtain ⟨i1, e1, o1⟩ := Tm.number_spec _ d.2.2 (Nat.le_refl _) (h d List.mem_cons_self) false s hs
    obtain ⟨i2, e2, o2⟩ := Code.program_go ds (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ i1
    simp only [List.mapM_cons]
    refine ⟨i2, e1.trans e2, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact o1.1.ext e2
    · exact o2 x hx

/-- **`Code.program` meets `Codes.Shares`**: for terms whose every shared part is closed, the share table the program
    numbers is `Sound` for the empty context, and every numbered term meets `Tm.GenHyp` under it, so `Tm.gen_sound`
    applies to each. -/
theorem Code.program_sound (ds : List Res) (h : ∀ d ∈ ds, d.2.2.GenHyp fun _ R => R.fv = []) :
    Sound (Code.shares (Code.program ds).2) Val.empty ∧
      ∀ d ∈ (Code.program ds).1, d.2.2.GenHyp (Code.shares (Code.program ds).2).sh.Shares := by
  obtain ⟨i, -, o⟩ := Code.program_go ds h (#[], {}) fun _ h => nomatch h
  have hs := Code.shares_sound _ i
  exact ⟨hs.1, fun d hd => Tm.GenHyp.mono hs.2 (o d hd)⟩

end Rel.Lang
