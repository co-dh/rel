import Rel.Lang.Laws.AopA6_2
import Rel.Lang.Laws.AopA6_6e_Quicksort
import Rel.Lang.PreludeMerge
import Rel.Lang.PreludeTails

/-! # Laws of freyd `AOP/A6_6b_SortConcrete.lean` (B&dM §6.6, selection sort), at the list fold on snoc

freyd folds over `cons`, the prelude over `snoc`: `ok cons` becomes `K snoc`, with `K` any `[α]×α ⟶ [α]×α` (the book's
`ok`, the coreflexive "the element is below all of the array"), and `perm` is any `P` with the two facts the proof uses
(`K` commutes with `P×𝟙`, and `snoc P = (P×𝟙) snoc P`): the stronger form, with `P = perm`, `K = ok` an instance. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude row `snoc`, with its object fixed. -/
abbrev Tm.snocRow (B : Obj) : Tm (.prod (.arr B) B) (.arr B) := .prim (rowOf "snoc")

theorem lcompLe {α β γ : Type} {R : Core.Rel α β} {S T : Core.Rel β γ} (h : S ⊑ T) : R ≫ S ⊑ R ≫ T :=
  Core.Rel.le_iff.2 fun a c ⟨b, hr, hs⟩ => ⟨b, hr, Core.Rel.le_iff.1 h b c hs⟩

/-- p.153 `select_proviso`: `(P×𝟙) select° ⊑ K snoc P` from `select° ⊑ K snoc P`, `K (P×𝟙) = (P×𝟙) K` (Ex 6.22) and the
    snoc branch of `P`. -/
theorem selectProviso_core {X Y : Type} {A K : Core.Rel X X} {sn : Core.Rel X Y} {P : Core.Rel Y Y} {S' : Core.Rel X Y}
    (hK : K ≫ A = A ≫ K) (hs : sn ≫ P = (A ≫ sn) ≫ P) (hsel : S' ⊑ (K ≫ sn) ≫ P) : A ≫ S' ⊑ (K ≫ sn) ≫ P := by
  have heq : A ≫ ((K ≫ sn) ≫ P) = (K ≫ sn) ≫ P :=
    calc A ≫ ((K ≫ sn) ≫ P) = A ≫ (K ≫ (sn ≫ P)) := by rw [Core.Rel.comp_assoc K sn P]
      _ = (A ≫ K) ≫ (sn ≫ P) := (Core.Rel.comp_assoc A K _).symm
      _ = (K ≫ A) ≫ (sn ≫ P) := by rw [hK]
      _ = K ≫ (A ≫ (sn ≫ P)) := Core.Rel.comp_assoc K A _
      _ = K ≫ (sn ≫ P) := by rw [← Core.Rel.comp_assoc A sn P, ← hs]
      _ = (K ≫ sn) ≫ P := (Core.Rel.comp_assoc K sn P).symm
  have h1 : A ≫ S' ⊑ A ≫ ((K ≫ sn) ≫ P) := lcompLe hsel
  rwa [heq] at h1

theorem Tm.selectProviso_den {B : Obj} {P : Tm (.arr B) (.arr B)} {K : Tm (.prod (.arr B) B) (.prod (.arr B) B)}
    {S : Tm (.arr B) (.prod (.arr B) B)} (ρ : Val)
    (hK : (Tm.comp K (Tm.pair (.comp .outl P) (.comp .outr .id))).den ρ
      = (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) K).den ρ)
    (hs : (Tm.comp (Tm.snocRow B) P).den ρ
      = (Tm.comp (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) (Tm.snocRow B)) P).den ρ)
    (hsel : S.conv.den ρ ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ) :
    (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) S.conv).den ρ
      ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ :=
  selectProviso_core hK hs hsel

/-- p.152 `selection_sort` at the list fold: `⦇[e, select°]⦈° ⊑ P O` for `O = ⦇[e, K snoc]⦈` a coreflexive, `P° = P`
    and `e ⊑ e P` (freyd gets it from `perm` reflexive): (6.4) fusion under the proviso, then the converse. -/
theorem Tm.selectionSort_den {B : Obj} {P O : Tm (.arr B) (.arr B)} {K : Tm (.prod (.arr B) B) (.prod (.arr B) B)}
    {S : Tm (.arr B) (.prod (.arr B) B)} {e : Tm .one (.arr B)} (ρ : Val)
    (hP : P.conv.den ρ = P.den ρ) (hOid : O.den ρ ⊑ (Tm.id (A := .arr B)).den ρ)
    (hO : O.den ρ = (Tm.fold (Tm.ran e) (Tm.comp K (Tm.snocRow B))).den ρ)
    (hK : (Tm.comp K (Tm.pair (.comp .outl P) (.comp .outr .id))).den ρ
      = (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) K).den ρ)
    (hs : (Tm.comp (Tm.snocRow B) P).den ρ
      = (Tm.comp (Tm.comp (Tm.pair (.comp .outl P) (.comp .outr .id)) (Tm.snocRow B)) P).den ρ)
    (he : e.den ρ ⊑ (Tm.comp e P).den ρ)
    (hsel : S.conv.den ρ ⊑ (Tm.comp (Tm.comp K (Tm.snocRow B)) P).den ρ) :
    (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv.den ρ ⊑ (Tm.comp P O).den ρ := by
  have hf := Tm.relCata_le_comp_den (e := e) (f := Tm.comp K (Tm.snocRow B)) (e' := e) (g := S.conv) (S := P) ρ he
    (Tm.selectProviso_den ρ hK hs hsel)
  refine Core.Rel.le_iff.2 fun w xs h => ?_
  have h' : (𝟙 _ ≫ (Tm.fold (Tm.ran e) S.conv).den ρ) xs w := h
  rw [Core.Rel.id_comp] at h'
  obtain ⟨u, hu, hPu⟩ := Core.Rel.le_iff.1 hf xs w h'
  rw [← hO] at hu
  obtain rfl : xs = u := Core.Rel.le_iff.1 hOid xs u hu
  exact ⟨xs, (congrFun (congrFun hP w) xs).mp hPu, hu⟩

/-- p.153: the converse of the fold unfolds one `select` at a time, `X° = e°nil ∪ select (X°×𝟙) snoc`. -/
theorem Tm.sortRec_den {B : Obj} {S : Tm (.arr B) (.prod (.arr B) B)} {e : Tm .one (.arr B)} (ρ : Val) :
    (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv.den ρ
      = (Tm.join (Tm.comp e.conv (Tm.nil : Tm .one (.arr B)))
          (Tm.comp (Tm.comp S (Tm.pair (Tm.comp .outl (Tm.comp Tm.id (Tm.fold (Tm.ran e) S.conv)).conv) (Tm.comp .outr .id)))
            (Tm.snocRow B))).den ρ := by
  apply Core.Rel.ext
  intro w xs
  induction xs using snocInd generalizing w with
  | nil =>
    simp only [↓pairComp_den, Tm.nil, Prim.den_nilRow, Tm.den, Prim.den_snoc, nilDen, Core.Rel.union, Core.Rel.comp,
      Core.Rel.rprodMap, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, exists_eq_left, exists_eq_left']
    rw [foldDen_empty]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨m, hm⟩ := (ranSeed_iff ρ e w).1 ⟨a, ha⟩
      exact Or.inl ⟨m, hm, by simp⟩
    · rintro (⟨m, hm, -⟩ | ⟨b, -, h⟩)
      · exact (ranSeed_iff ρ e w).2 ⟨m, hm⟩
      · exact absurd h (by simp)
  | snoc L x ih =>
    simp only [↓pairComp_den, Tm.nil, Prim.den_nilRow, Tm.den, Prim.den_snoc, nilDen, Core.Rel.union, Core.Rel.comp,
      Core.Rel.rprodMap, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, exists_eq_left, exists_eq_left']
    rw [foldDen_snoc]
    constructor
    · rintro ⟨u, hu, hS⟩
      exact Or.inr ⟨(L, x), ⟨(u, x), hS, hu, rfl⟩, rfl⟩
    · rintro (⟨m, -, h⟩ | ⟨⟨L', x'⟩, ⟨⟨u, y⟩, hS, hf, hs⟩, h⟩)
      · exact absurd h (by simp)
      · dsimp only at h hs hf
        obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
        obtain rfl := (List.cons.inj h2).1
        subst hs
        exact ⟨u, hf, hS⟩

/-- `xs` is `Q`-pairwise iff at every suffix `h :: t`, `h` is `Q`-related to every element of `t`. -/
theorem pairwise_iff_drop {α : Type} (Q : α → α → Prop) (xs : List α) :
    xs.Pairwise Q ↔ ∀ k h t, xs.drop k = h :: t → ∀ x ∈ t, Q h x := by
  induction xs with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩ (_ | k) h t e x hx
      · simp only [List.drop_zero, List.cons.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact h1 x hx
      · exact h2 k h t e x hx
    · intro H
      exact ⟨fun x hx => H 0 a l rfl x hx, fun k h t e => H (k + 1) h t e⟩

/-- `∼Q` on pairs as the prelude's `ordered` elaborates it, `𝟙 − dom(π₂ ∩ π₁Q)`, `Q` the variable 1. -/
def Tm.orderedNotQ (B : Obj) : Tm (.prod B B) (.prod B B) :=
  Tm.id.diff (Tm.dom (Tm.outr.meet (Tm.outl.comp (Tm.var 1 : Tm B B))))

/-- What breaks `ordered(Q)`: `tails ∋ ⟨at(0),tail⟩ (π₁∼Q ∩ π₂∋)` relates `xs` to `x` at a suffix `h :: t` with `x ∈ t`
    and not `h Q x`; `at(0)` is `Tm.headAt`, `tail` the call `Tm.tailCall`. -/
def Tm.orderedBad (B : Obj) (os : List Obj) : Tm (.arr B) B :=
  (((Tm.prim (rowOf "tails") : Tm (.arr B) (.arr (.arr B))).comp Tm.mem).comp
      ((Tm.headAt (B := B)).pair (Tm.tailCall B os))).comp
    (((Tm.id : Tm (.prod B (.arr B)) (.prod B (.arr B))).pair (Tm.outr.comp Tm.mem)).comp
      ((Tm.dom ((((Tm.outl : Tm (.prod (.prod B (.arr B)) B) (.prod B (.arr B))).comp Tm.outl).pair Tm.outr).comp
        (Tm.orderedNotQ B))).comp Tm.outr))

/-- `ordered(Q) ≜ 𝟙 − dom(tails ∋ ⟨at(0),tail⟩(π₁∼Q ∩ (π₂∋)))` (Prelude) at the object `B`, `Q` the variable 1. -/
def Tm.orderedDef (B : Obj) (os : List Obj) : Tm (.arr B) (.arr B) := Tm.id.diff (Tm.dom (Tm.orderedBad B os))

/-- `Tm.orderedDef` keeps exactly the `Q`-pairwise arrays, `Q` the meaning of the variable 1. -/
theorem Tm.orderedDef_iff {B : Obj} (ρ : Val) (Q : Core.Rel B.El B.El) (hv : ρ 1 B B = Q) (xs ys : List B.El) :
    (Tm.orderedDef B [B]).den ρ xs ys ↔ xs = ys ∧ xs.Pairwise (fun a b => Q a b) := by
  have dc : ∀ {X Y Z : Obj} (R : Tm X Y) (S : Tm Y Z), (R.comp S).den ρ = R.den ρ ≫ S.den ρ := fun _ _ => rfl
  have dp : ∀ {X Y Z : Obj} (R : Tm X Y) (S : Tm X Z), (R.pair S).den ρ = Core.Rel.rpair (R.den ρ) (S.den ρ) :=
    fun _ _ => rfl
  have dd : ∀ {X Y : Obj} (R S : Tm X Y), (R.diff S).den ρ = Core.Rel.diff (R.den ρ) (S.den ρ) := fun _ _ => rfl
  have dm : ∀ {X Y : Obj} (R S : Tm X Y), (R.meet S).den ρ = Core.Rel.inter (R.den ρ) (S.den ρ) := fun _ _ => rfl
  have di : ∀ {X : Obj}, (Tm.id : Tm X X).den ρ = Core.Rel.id _ := rfl
  have dl : ∀ {X Y : Obj}, (Tm.outl : Tm (.prod X Y) X).den ρ = Core.Rel.graph Prod.fst := rfl
  have dr : ∀ {X Y : Obj}, (Tm.outr : Tm (.prod X Y) Y).den ρ = Core.Rel.graph Prod.snd := rfl
  have dmem : ∀ {X : Obj}, (Tm.mem : Tm (.arr X) X).den ρ = memDen := rfl
  have dv : (Tm.var 1 : Tm B B).den ρ = Q := hv
  have dt : (Tm.prim (rowOf "tails") : Tm (.arr B) (.arr (.arr B))).den ρ =
      fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k := Prim.den_tails
  have hH : (Tm.headAt (B := B)).den ρ = fun xs b => ∃ h : 0 < xs.length, b = xs[0]'h :=
    funext fun xs => funext fun b => propext (Tm.headAt_den ρ xs b)
  have hT : (Tm.tailCall B [B]).den ρ = fun xs ys => ∃ a, xs = a :: ys :=
    funext fun xs => funext fun ys => propext (Tm.tailCall_den ρ xs ys)
  have hN : (Tm.orderedNotQ B).den ρ = fun p q => p = q ∧ ¬ Q p.1 p.2 := by
    funext p q; apply propext
    simp only [Tm.orderedNotQ, dd, di, Tm.dom_den, dm, dc, dl, dr, dv, Core.Rel.diff, Core.Rel.inter,
      Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.graph, Core.Rel.id]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, fun hq => h ⟨rfl, p.2, ⟨rfl, p.1, rfl, hq⟩, rfl, p.1, rfl, hq⟩⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, fun ⟨_, c, ⟨e, b, eb, hq⟩, _⟩ => h (by subst e eb; exact hq)⟩
  have hBad : ∀ xs z, (Tm.orderedBad B [B]).den ρ xs z ↔ ∃ k h t, xs.drop k = h :: t ∧ z ∈ t ∧ ¬ Q h z := by
    intro xs z
    simp only [Tm.orderedBad, dc, dp, di, Tm.dom_den, dl, dr, dmem, dt, hH, hT, hN, Core.Rel.comp_apply,
      Core.Rel.inter, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, memDen]
    constructor
    · rintro ⟨⟨h, t⟩, ⟨s, ⟨_, rfl, hs⟩, ⟨hl, hh⟩, a, rfl⟩, ⟨⟨h', t'⟩, x⟩, ⟨e1, _, rfl, hx⟩, _,
        ⟨rfl, _, ⟨⟨c1, c2⟩, ⟨⟨_, rfl, ec⟩, ec2⟩, rfl, hq⟩, -⟩, rfl⟩
      obtain ⟨k, -, hk⟩ := List.mem_map.1 hs
      simp only [Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      dsimp only at hh ec ec2 hq hx
      subst ec ec2
      simp only [List.getElem_cons_zero] at hh
      subst hh
      exact ⟨k, _, _, hk, hx, hq⟩
    · rintro ⟨k, h, t, hk, hx, hq⟩
      have hl : k < xs.length + 1 := by
        have := congrArg List.length hk
        simp only [List.length_drop, List.length_cons] at this
        omega
      exact ⟨(h, t), ⟨h :: t, ⟨_, rfl, List.mem_map.2 ⟨k, List.mem_range.2 hl, hk⟩⟩, ⟨by simp, rfl⟩, h, rfl⟩,
        ((h, t), z), ⟨rfl, _, rfl, hx⟩, _, ⟨rfl, (h, z), ⟨(h, z), ⟨⟨_, rfl, rfl⟩, rfl⟩, rfl, hq⟩, (h, z),
        ⟨⟨_, rfl, rfl⟩, rfl⟩, rfl, hq⟩, rfl⟩
  simp only [Tm.orderedDef, dd, di, Tm.dom_den, Core.Rel.diff, Core.Rel.inter, Core.Rel.comp_apply,
    Core.Rel.recip_apply, Core.Rel.id, hBad]
  rw [pairwise_iff_drop]
  constructor
  · rintro ⟨rfl, H⟩
    exact ⟨rfl, fun k h t e x hx => Classical.byContradiction fun hq =>
      H ⟨rfl, x, ⟨k, h, t, e, hx, hq⟩, k, h, t, e, hx, hq⟩⟩
  · rintro ⟨rfl, H⟩
    exact ⟨rfl, fun ⟨_, x, ⟨k, h, t, e, hx, hq⟩, _⟩ => hq (H k h t e x hx)⟩

/-- **`ordered`'s text is `Q`-pairwise**: the body the prelude elaborates, `prelude.ordered.body`, at any objects `σ`,
    its parameter bound to `Q`, keeps exactly the arrays whose every element is `Q`-related to each later one. A law
    about a call of `ordered` takes `(ht : prelude.ordered.body.instObj [.general] [B] = .ok t' := by rfl)`. -/
theorem Tm.orderedDef_den (ph : List QAtomicType) (σ : List Obj)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.ordered.body.instObj ph σ = .ok t')
    (Q : Core.Rel (Obj.El ((Obj.atom .general).inst ph σ)) (Obj.El ((Obj.atom .general).inst ph σ))) (xs ys) :
    t'.den (Val.args [1] [⟨_, _, Q⟩]) xs ys ↔ xs = ys ∧ xs.Pairwise (fun a b => Q a b) := by
  obtain rfl : Tm.orderedDef _ [(Obj.atom .general).inst ph σ] = t' := Except.ok.inj ht
  exact Tm.orderedDef_iff _ Q (Val.bind_apply _ _ _ rfl rfl) xs ys

/-- A left fold whose seed is `[]` and whose step appends `x` to `u` exactly when every `c ∈ u` has `Q c x` is the
    coreflexive of the `Q`-sorted arrays. -/
theorem foldDen_pairwise {A : Obj} (Te : Core.Rel (Obj.El (.arr A)) (Obj.El (.arr A)))
    (TS : Core.Rel (Obj.El (.prod (.arr A) A)) (Obj.El (.arr A))) (Q : A.El → A.El → Prop)
    (hseed : ∀ v, (∃ a, Te a v) ↔ v = []) (hstep : ∀ u x w, TS (u, x) w ↔ (∀ c ∈ u, Q c x) ∧ w = u ++ [x])
    (xs ys : List A.El) : foldDen Te TS xs ys ↔ xs = ys ∧ xs.Pairwise Q := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n generalizing xs ys with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    rw [foldDen_empty, hseed]
    exact ⟨fun h => ⟨h.symm, List.Pairwise.nil⟩, fun h => h.1.symm⟩
  | succ n ih =>
    obtain ⟨L, x, rfl⟩ := (List.eq_nil_or_concat xs).resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at *
    rw [foldDen_snoc]
    simp only [hstep, ih L _ (by simpa using hn)]
    constructor
    · rintro ⟨_, ⟨rfl, hp⟩, hc, rfl⟩
      exact ⟨rfl, List.pairwise_append.2 ⟨hp, List.pairwise_singleton _ _,
        fun a ha b hb => (List.mem_singleton.1 hb) ▸ hc a ha⟩⟩
    · rintro ⟨rfl, h⟩
      obtain ⟨hp, -, hc⟩ := List.pairwise_append.1 h
      exact ⟨L, ⟨rfl, hp⟩, fun c hc' => hc c hc' x (List.mem_singleton_self x), rfl⟩

/-- `ordered(Q) = ⦇[nil, ok(Q) snoc]⦈` (B&dM p.152), with `ok(Q) = dom(⟨π₂,π₁⟩cor(Q°/∋))` inline: both sides are the
    coreflexive of the `Q`-sorted arrays. -/
theorem Tm.orderedCata_den {A : Obj} {cvo cv : Option Lean.Name} {oso os : List Obj}
    {to : Tm (.arr A) (.arr A)} {tc : Tm (.prod A (.arr A)) (.prod A (.arr A))}
    (ho : Rel.Programs.prelude.ordered.body.instObj [.general] [A] = .ok to := by rfl)
    (hc : Rel.Programs.prelude.cor.body.instObj [.general, .u1] [A, .arr A] = .ok tc := by rfl) (ρ : Val) :
    Tm.den ρ (Tm.arg (Tm.call [1] `Rel.Programs.prelude.ordered cvo oso to) (Tm.var 0 : Tm A A)) =
    Tm.den ρ (Tm.fold (Tm.ran (Tm.closedNil A))
      ((Tm.dom (((Tm.outr : Tm (.prod (.arr A) A) A).pair Tm.outl).comp
        (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os tc)
          ((Tm.var 0 : Tm A A).conv.rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id)))).comp
        (Tm.prim (rowOf "snoc")))) := by
  have hseed (v : List A.El) : (∃ a, (Tm.ran (Tm.closedNil A)).den ρ a v) ↔ v = [] := by
    simp [Tm.ran_den, Tm.closedNil_den, Core.Rel.id, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
  have h1 : ∀ p q, (Tm.arg (Tm.call [2] `Rel.Programs.prelude.cor cv os tc)
      ((Tm.var 0 : Tm A A).conv.rdiv (Tm.id.comp Tm.mem) Tm.id Tm.id)).den ρ p q ↔ p = q ∧ ∀ c ∈ p.2, ρ 0 A A c p.1 :=
    fun p q => (Tm.corCall_den hc ρ _ p q).trans (and_congr Iff.rfl (rdivDen_mem_iff _ _ _))
  apply Core.Rel.ext
  intro xs ys
  refine (Tm.orderedDef_den [.general] [A] ho (ρ 0 A A) xs ys).trans (Iff.symm (foldDen_pairwise _ _ _ hseed ?_ xs ys))
  intro u x w
  show Core.Rel.comp (Tm.den ρ (Tm.dom _)) (Tm.den ρ (Tm.prim _)) _ _ ↔ _
  rw [Tm.dom_den]
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.graph, Core.Rel.rpair,
    Core.Rel.id, Prim.den_snoc] at h1 ⊢
  simp only [h1]
  constructor
  · rintro ⟨_, ⟨rfl, _, ⟨⟨a, b⟩, ⟨hx, hu⟩, rfl, hq⟩, -⟩, rfl⟩
    dsimp only at hx hu hq ⊢
    subst hx hu
    exact ⟨hq, rfl⟩
  · rintro ⟨hq, rfl⟩
    exact ⟨(u, x), ⟨rfl, (x, u), ⟨(x, u), ⟨rfl, rfl⟩, rfl, hq⟩, (x, u), ⟨rfl, rfl⟩, rfl, hq⟩, rfl⟩

end Rel.Lang
