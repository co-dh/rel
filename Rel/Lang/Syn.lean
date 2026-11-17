/-
  The syntactic category `Syn` (`doc/rel-denotation-design.md` §4): the objects are `Obj`, a hom `A ⟶ B` is a term
  modulo `Tm.Eqv`, the equivalence the allegory axioms generate (`Tm.Le`). `⟦−⟧ρ` is a functor `Syn ⟶ Rel(Set)`
  because every axiom is sound (`Tm.Le.sound`); rel has no category class (decision A of the split), so the category
  laws and the functor laws are theorems here over `Core.Rel`, and `RelAop.Syn` makes them freyd's `Cat Syn` and
  `Functor Syn RelSet`. Completeness (`⟦s⟧ = ⟦t⟧` for every `ρ` implies `Eqv s t`) is open. The rest is the §4.2
  table of laws.
-/
import Rel.Lang.Den
import Rel.Run.Lang.Elab

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open scoped Rel.Core.Rel

/-! ### The axioms -/

/-- The equational allegory axioms (Freyd §2.1, §2.21): the category laws, the two laws of `°`, and the
    distributive laws of `∩`, `≫` over `∪`, `𝟘`. `Tm.Le` reads each in both directions. -/
inductive Tm.Ax : {A B : Obj} → {d e : Bool} → Tm A B d → Tm A B e → Prop
  | id_comp {A B : Obj} {d : Bool} (R : Tm A B d) : Tm.Ax (.comp .id R) R
  | comp_id {A B : Obj} {d : Bool} (R : Tm A B d) : Tm.Ax (.comp R .id) R
  | assoc {A B C D : Obj} {d e f : Bool} (R : Tm A B d) (S : Tm B C e) (T : Tm C D f) :
      Tm.Ax (.comp (.comp R S) T) (.comp R (.comp S T))
  | conv_conv {A B : Obj} (R : Tm A B false) : Tm.Ax (.conv (.conv R)) R
  | conv_comp {A B C : Obj} (R : Tm A B false) (S : Tm B C false) :
      Tm.Ax (.conv (.comp R S)) (.comp (.conv S) (.conv R))
  | meet_join {A B : Obj} {d e f : Bool} (R : Tm A B d) (S : Tm A B e) (T : Tm A B f) :
      Tm.Ax (.meet R (.join S T)) (.join (.meet R S) (.meet R T))
  | comp_join {A B C : Obj} {d e f : Bool} (R : Tm A B d) (S : Tm B C e) (T : Tm B C f) :
      Tm.Ax (.comp R (.join S T)) (.join (.comp R S) (.comp R T))
  | join_comp {A B C : Obj} {d e f : Bool} (R : Tm A B d) (S : Tm A B e) (T : Tm B C f) :
      Tm.Ax (.comp (.join R S) T) (.join (.comp R T) (.comp S T))
  | comp_zero {A B C : Obj} {d : Bool} (R : Tm A B d) : Tm.Ax (.comp R (.zero : Tm B C false)) .zero
  | zero_comp {A B C : Obj} {d : Bool} (R : Tm B C d) : Tm.Ax (.comp (.zero : Tm A B false) R) .zero
  /-- `μX : φ = φ[μX : φ]` where `X` occurs in `φ` only positively; `refold` has no such law, since its own demand
      bit is `true` and `X` may occur in `φ` at `false`, where no term stands for it (`Tm.lift`). -/
  | mu_unfold {A B : Obj} (k : Nat) (what : String) (cap : Nat) (b : Tm A B false) (h : b.pol true k = true) :
      Tm.Ax (.mu k what cap b) (b.subst [(k, ⟨A, B, .mu k what cap b⟩)])
  /-- `νX : φ = φ[νX : φ]` where `X` occurs in `φ` only positively. -/
  | nu_unfold {A B : Obj} (k : Nat) (S b : Tm A B false) (h : b.pol true k = true) :
      Tm.Ax (.nu k S b) (b.subst [(k, ⟨A, B, .nu k S b⟩)])

/-- The allegory order on terms: the least preorder that holds the equations `Tm.Ax`, makes `∩` the meet, `∪` the
    join and `𝟘` the least element, holds the modular law, and is a congruence for every constructor of `Tm` —
    monotone in each argument where `⟦−⟧` is, antitone where it is (`diff`'s second), and a congruence for `Eqv`
    only where it is neither (`lam`, `E`, `thin`, the `R` of `ldiv`, the `S` of `rdiv`). `Tm` has no `∋`, so no
    power law can be stated. -/
inductive Tm.Le : {A B : Obj} → {d e : Bool} → Tm A B d → Tm A B e → Prop
  | refl {A B : Obj} {d : Bool} (R : Tm A B d) : Tm.Le R R
  | trans {A B : Obj} {d e f : Bool} {R : Tm A B d} {S : Tm A B e} {T : Tm A B f} :
      Tm.Le R S → Tm.Le S T → Tm.Le R T
  | ax {A B : Obj} {d e : Bool} {R : Tm A B d} {S : Tm A B e} : Tm.Ax R S → Tm.Le R S
  | ax_symm {A B : Obj} {d e : Bool} {R : Tm A B d} {S : Tm A B e} : Tm.Ax R S → Tm.Le S R
  | meet_left {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm.Le (.meet R S) R
  | meet_right {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm.Le (.meet R S) S
  | le_meet {A B : Obj} {d e f : Bool} {R : Tm A B d} {S : Tm A B e} {T : Tm A B f} :
      Tm.Le T R → Tm.Le T S → Tm.Le T (.meet R S)
  | join_left {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm.Le R (.join R S)
  | join_right {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm.Le S (.join R S)
  | join_le {A B : Obj} {d e f : Bool} {R : Tm A B d} {S : Tm A B e} {T : Tm A B f} :
      Tm.Le R T → Tm.Le S T → Tm.Le (.join R S) T
  | zero_le {A B : Obj} {d : Bool} (R : Tm A B d) : Tm.Le .zero R
  | modular {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm B C false) (T : Tm A C e) :
      Tm.Le (.meet (.comp R S) T) (.comp (.meet R (.comp T (.conv S))) S)
  | comp {A B C : Obj} {d d' e e' : Bool} {R : Tm A B d} {R' : Tm A B d'} {S : Tm B C e} {S' : Tm B C e'} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le (.comp R S) (.comp R' S')
  | conv {A B : Obj} {R R' : Tm A B false} : Tm.Le R R' → Tm.Le (.conv R) (.conv R')
  | top {A B : Obj} {V V' : Tm B B false} : Tm.Le V V' → Tm.Le (.top V : Tm A B true) (.top V')
  | dom {A B : Obj} {d d' : Bool} {R : Tm A B d} {R' : Tm A B d'} : Tm.Le R R' → Tm.Le (.dom R) (.dom R')
  | ran {A B : Obj} {R R' : Tm A B false} : Tm.Le R R' → Tm.Le (.ran R) (.ran R')
  | diff {A B : Obj} {d d' e e' : Bool} {R : Tm A B d} {R' : Tm A B d'} {S : Tm A B e} {S' : Tm A B e'} :
      Tm.Le R R' → Tm.Le S' S → Tm.Le (.diff R S) (.diff R' S')
  | ldiv {A B C : Obj} {R R' : Tm A B false} {S S' : Tm A C false} {U U' : Tm B B false} {V V' : Tm C C false} :
      Tm.Le R R' → Tm.Le R' R → Tm.Le S S' → Tm.Le U U' → Tm.Le V V' → Tm.Le (.ldiv R S U V) (.ldiv R' S' U' V')
  | rdiv {A B C : Obj} {R R' : Tm A C false} {S S' : Tm B C false} {U U' : Tm A A false} {V V' : Tm B B false} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le S' S → Tm.Le U U' → Tm.Le V V' → Tm.Le (.rdiv R S U V) (.rdiv R' S' U' V')
  | pair {A B C : Obj} {d d' e e' : Bool} {R : Tm A B d} {R' : Tm A B d'} {S : Tm A C e} {S' : Tm A C e'} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le (.pair R S) (.pair R' S')
  | prod {A B C D : Obj} {R R' : Tm A B false} {S S' : Tm C D false} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le (.prod R S) (.prod R' S')
  | junc {A B C : Obj} {R R' : Tm A C false} {S S' : Tm B C false} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le (.junc R S) (.junc R' S')
  | juncD {A B C : Obj} {d d' e e' : Bool} {R : Tm A C d} {R' : Tm A C d'} {S : Tm B C e} {S' : Tm B C e'} :
      Tm.Le R R' → Tm.Le S S' → Tm.Le (.juncD R S) (.juncD R' S')
  | lam {A B : Obj} {d d' : Bool} {R : Tm A B d} {R' : Tm A B d'} :
      Tm.Le R R' → Tm.Le R' R → Tm.Le (.lam R) (.lam R')
  | E {A B : Obj} {d d' : Bool} {R : Tm A B d} {R' : Tm A B d'} : Tm.Le R R' → Tm.Le R' R → Tm.Le (.E R) (.E R')
  | est {B : Obj} {Q Q' : Tm (.prod B B) (.prod B B) true} : Tm.Le Q Q' → Tm.Le (.est Q) (.est Q')
  | thin {B : Obj} {Q Q' : Tm (.prod B B) (.prod B B) true} :
      Tm.Le Q Q' → Tm.Le Q' Q → Tm.Le (.thin Q) (.thin Q')
  | own {A : Obj} {d d' : Bool} {R : Tm A A d} {R' : Tm A A d'} : Tm.Le R R' → Tm.Le (.own R) (.own R')
  | succ {U U' : Tm .long .long false} : Tm.Le U U' → Tm.Le (.succ U) (.succ U')
  | arith (k : UInt8) {U U' : Tm .long .long false} : Tm.Le U U' → Tm.Le (.arith k U) (.arith k U')
  | leq {U U' : Tm .long .long false} : Tm.Le U U' → Tm.Le (.leq U) (.leq U')
  | lt {U U' : Tm .long .long false} : Tm.Le U U' → Tm.Le (.lt U) (.lt U')
  | fold {E V : Obj} {d d' : Bool} {e e' : Tm V V false} {S : Tm (.prod E V) V d} {S' : Tm (.prod E V) V d'} :
      Tm.Le e e' → Tm.Le S S' → Tm.Le (.fold e S) (.fold e' S')
  | share (k : Nat) {A B : Obj} {d d' : Bool} {R : Tm A B d} {R' : Tm A B d'} :
      Tm.Le R R' → Tm.Le (.share k R) (.share k R')
  | foldI {I E V : Obj} {d d' e e' : Bool} {s : Tm I (.prod V V) d} {s' : Tm I (.prod V V) d'}
      {S : Tm (.prod E (.prod I V)) (.prod I V) e} {S' : Tm (.prod E (.prod I V)) (.prod I V) e'} :
      Tm.Le s s' → Tm.Le S S' → Tm.Le (.foldI s S) (.foldI s' S')
  | flat {I A B : Obj} {d d' : Bool} {R : Tm I (.prod A B) d} {R' : Tm I (.prod A B) d'} :
      Tm.Le R R' → Tm.Le (.flat R) (.flat R')
  -- one head `f` and arguments each below the other: a row's meaning of its argument is not monotone (`setify` is
  -- `Λ`), and two heads with one meaning can be different rows (`Tm.argDen`)
  | arg {A B C D : Obj} {d e e' : Bool} {f : Tm A B d} {x : Tm C D e} {x' : Tm C D e'} :
      Tm.Le x x' → Tm.Le x' x → Tm.Le (.arg f x) (.arg f x')
  | nu (k : Nat) {A B : Obj} {S S' b b' : Tm A B false} : Tm.Le S S' → Tm.Le b b' → Tm.Le (.nu k S b) (.nu k S' b')
  | mu (k : Nat) (what : String) (cap : Nat) {A B : Obj} {b b' : Tm A B false} :
      Tm.Le b b' → Tm.Le (.mu k what cap b) (.mu k what cap b')
  | refold (k : Nat) (what : String) {A B : Obj} {d d' e e' : Bool} {ch : Tm A A d} {ch' : Tm A A d'}
      {b : Tm A B e} {b' : Tm A B e'} : Tm.Le ch ch' → Tm.Le b b' → Tm.Le (.refold k what ch b) (.refold k what ch' b')

/-! ### Soundness -/

theorem foldDen_le {E V : Obj} {Te Te' : Den V V} {TS TS' : Den (.prod E V) V} (he : Te ⊑ Te') (hS : TS ⊑ TS') :
    foldDen Te TS ⊑ foldDen Te' TS' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem foldIDen_le {I E V : Obj} {Te Te' : Den I (.prod V V)} {TS TS' : Den (.prod E (.prod I V)) (.prod I V)}
    (he : Te ⊑ Te') (hS : TS ⊑ TS') : foldIDen Te TS ⊑ foldIDen Te' TS' :=
  le_iff.2 fun p _ h => le_iff.1 (foldDen_le (Te := fun a b => Te p.1 (a, b)) (Te' := fun a b => Te' p.1 (a, b))
    (TS := fun q v => TS (q.1, (p.1, q.2)) (p.1, v)) (TS' := fun q v => TS' (q.1, (p.1, q.2)) (p.1, v))
    (le_iff.2 fun _ _ h => le_iff.1 he _ _ h) (le_iff.2 fun _ _ h => le_iff.1 hS _ _ h)) _ _ h

/-- Each equation holds in `Rel(Set)` under every valuation. -/
theorem Tm.Ax.sound {A B : Obj} {d e : Bool} {s : Tm A B d} {t : Tm A B e} (h : Tm.Ax s t) (ρ : Val) :
    s.den ρ = t.den ρ := by
  cases h with
  | id_comp => exact Core.Rel.id_comp _
  | comp_id => exact Core.Rel.comp_id _
  | assoc => exact Core.Rel.comp_assoc _ _ _
  | conv_conv => exact Core.Rel.recip_recip _
  | conv_comp => exact Core.Rel.recip_comp _ _
  | meet_join => exact Core.Rel.inter_union _ _ _
  | comp_join => exact Core.Rel.comp_union _ _ _
  | join_comp => exact Core.Rel.union_comp _ _ _
  | comp_zero => exact Core.Rel.comp_zero _
  | zero_comp => exact Core.Rel.zero_comp _
  | mu_unfold _ _ _ b h =>
    rw [(b.den_subst _ (fun e he _ _ => by obtain rfl := List.mem_singleton.1 he; rfl) _).1]; exact (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm
  | nu_unfold _ _ b h =>
    rw [(b.den_subst _ (fun e he _ _ => by obtain rfl := List.mem_singleton.1 he; rfl) _).1]; exact (Core.Rel.nu_fix fun _ _ hXY => den_mono h hXY).symm

/-- **Soundness**: `Le s t` gives `⟦s⟧ρ ⊑ ⟦t⟧ρ` under every valuation, one case per rule. -/
theorem Tm.Le.sound {A B : Obj} {d e : Bool} {s : Tm A B d} {t : Tm A B e} (h : Tm.Le s t) :
    ∀ ρ, s.den ρ ⊑ t.den ρ := by
  induction h with
  | refl R => exact fun _ => Core.Rel.le_refl _
  | trans _ _ ih ih' => exact fun ρ => Core.Rel.le_trans (ih ρ) (ih' ρ)
  | ax h => exact fun ρ => by rw [h.sound ρ]; exact Core.Rel.le_refl _
  | ax_symm h => exact fun ρ => by rw [h.sound ρ]; exact Core.Rel.le_refl _
  | meet_left R S => exact fun ρ => Core.Rel.inter_le_left (R.den ρ) (S.den ρ)
  | meet_right R S => exact fun ρ => Core.Rel.inter_le_right (R.den ρ) (S.den ρ)
  | le_meet _ _ ih ih' => exact fun ρ => Core.Rel.le_inter (ih ρ) (ih' ρ)
  | join_left R S => exact fun ρ => Core.Rel.le_union_left (R.den ρ) (S.den ρ)
  | join_right R S => exact fun ρ => Core.Rel.le_union_right (R.den ρ) (S.den ρ)
  | join_le _ _ ih ih' => exact fun ρ => Core.Rel.union_le (ih ρ) (ih' ρ)
  | zero_le R => exact fun ρ => Core.Rel.zero_le (R.den ρ)
  | modular R S T => exact fun ρ => Core.Rel.modular (R.den ρ) (S.den ρ) (T.den ρ)
  | comp _ _ ih ih' => exact fun ρ => comp_le' (ih ρ) (ih' ρ)
  | conv _ ih => exact fun ρ => conv_le' (ih ρ)
  | top _ ih => exact fun ρ => comp_le' (Core.Rel.le_refl _) (ih ρ)
  | dom _ ih => exact fun ρ => inter_le' (Core.Rel.le_refl _) (comp_le' (ih ρ) (conv_le' (ih ρ)))
  | ran _ ih => exact fun ρ => inter_le' (Core.Rel.le_refl _) (comp_le' (conv_le' (ih ρ)) (conv_le' (conv_le' (ih ρ))))
  | diff _ _ ih ih' => exact fun ρ => diff_le (ih ρ) (ih' ρ)
  | ldiv _ _ _ _ _ ihR ihR' ihS ihU ihV =>
    intro ρ; show ldivDen _ _ _ _ ⊑ ldivDen _ _ _ _
    rw [Core.Rel.le_antisymm (ihR ρ) (ihR' ρ)]; exact ldiv_le (ihS ρ) (ihU ρ) (ihV ρ)
  | rdiv _ _ _ _ _ ihR ihS ihS' ihU ihV =>
    intro ρ; show rdivDen _ _ _ _ ⊑ rdivDen _ _ _ _
    rw [Core.Rel.le_antisymm (ihS ρ) (ihS' ρ)]; exact rdiv_le (ihR ρ) (ihU ρ) (ihV ρ)
  | pair _ _ ih ih' => exact fun ρ => pair_le (ih ρ) (ih' ρ)
  | prod _ _ ih ih' => exact fun ρ => prod_le (ih ρ) (ih' ρ)
  | junc _ _ ih ih' | juncD _ _ ih ih' => exact fun ρ => junc_le (ih ρ) (ih' ρ)
  | lam _ _ ih ih' =>
    intro ρ; show lamDen _ ⊑ lamDen _; rw [Core.Rel.le_antisymm (ih ρ) (ih' ρ)]; exact Core.Rel.le_refl _
  | E _ _ ih ih' =>
    intro ρ; show EDen _ ⊑ EDen _; rw [Core.Rel.le_antisymm (ih ρ) (ih' ρ)]; exact Core.Rel.le_refl _
  | thin _ _ ih ih' =>
    intro ρ; show thinDen _ ⊑ thinDen _; rw [Core.Rel.le_antisymm (ih ρ) (ih' ρ)]; exact Core.Rel.le_refl _
  | est _ ih =>
    exact fun ρ => le_iff.2 fun _ _ ⟨hm, hn⟩ =>
      ⟨hm, fun ⟨c, hc, hne, hq⟩ => hn ⟨c, hc, hne, fun h => hq (le_iff.1 (ih ρ) _ _ h)⟩⟩
  | own _ ih => exact ih
  | succ _ ih =>
    exact fun ρ => le_iff.2 fun _ _ ⟨⟨v, h⟩, hw, v', h'⟩ =>
      ⟨⟨v, le_iff.1 (ih ρ) _ _ h⟩, hw, v', le_iff.1 (ih ρ) _ _ h'⟩
  | arith _ _ ih =>
    -- arithDen filters both inputs by ⟦U⟧ and its result through ⟦U⟧: each factor is monotone in ⟦U⟧
    intro ρ
    exact comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) (ih ρ))
        (conv_le' (comp_le' (Core.Rel.le_refl _) (ih ρ)))))
      (comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) (ih ρ))
        (conv_le' (comp_le' (Core.Rel.le_refl _) (ih ρ))))) (comp_le' (Core.Rel.le_refl _) (ih ρ)))
  | leq _ ih | lt _ ih =>
    exact fun ρ => le_iff.2 fun _ _ ⟨⟨v, h⟩, ⟨v', h'⟩, hl⟩ =>
      ⟨⟨v, le_iff.1 (ih ρ) _ _ h⟩, ⟨v', le_iff.1 (ih ρ) _ _ h'⟩, hl⟩
  | fold _ _ ih ih' => exact fun ρ => foldDen_le (ih ρ) (ih' ρ)
  | share _ _ ih => exact fun _ => ih Val.empty
  | foldI _ _ ih ih' => exact fun ρ => foldIDen_le (ih ρ) (ih' ρ)
  | flat _ ih => exact fun ρ => le_iff.2 fun _ _ h => le_iff.1 (ih ρ) _ _ h
  | arg _ _ ih ih' =>
    exact fun ρ => by simp only [Tm.den, Core.Rel.le_antisymm (ih ρ) (ih' ρ)]; exact Core.Rel.le_refl _
  | nu k _ _ _ ih => exact fun ρ => Core.Rel.nu_mono fun X => ih (ρ.bind k X)
  | mu k _ _ _ ih => exact fun ρ => Core.Rel.mu_mono fun X => ih (ρ.bind k X)
  | refold k _ _ _ _ ih => exact fun ρ => Core.Rel.mu_mono fun X => ih (ρ.bind k X)

/-! ### The syntactic category -/

/-- Two terms each below the other: the equivalence the axioms generate. -/
def Tm.Eqv {A B : Obj} (s t : (d : Bool) × Tm A B d) : Prop := s.2.Le t.2 ∧ t.2.Le s.2

def Tm.setoid (A B : Obj) : Setoid ((d : Bool) × Tm A B d) :=
  ⟨Tm.Eqv, ⟨fun _ => ⟨.refl _, .refl _⟩, fun h => ⟨h.2, h.1⟩, fun h h' => ⟨.trans h.1 h'.1, .trans h'.2 h.2⟩⟩⟩

/-- The objects of the syntactic category. -/
def Syn := Obj

namespace Syn

/-- A hom `A ⟶ B`: a term `A ⟶ B` of either demand bit, modulo the axioms. -/
def Hom (A B : Syn) := Quotient (Tm.setoid A B)

/-- `𝟙`, the term `id`. -/
def id (A : Syn) : Hom A A := Quotient.mk _ ⟨true, .id⟩

/-- `f g`, diagram order: the term `comp`. -/
def comp {A B C : Syn} : Hom A B → Hom B C → Hom A C :=
  Quotient.lift₂ (s₁ := Tm.setoid A B) (s₂ := Tm.setoid B C) (fun R S => Quotient.mk _ ⟨R.1, .comp R.2 S.2⟩)
    fun _ _ _ _ hR hS => Quotient.sound (And.intro (.comp hR.1 hS.1) (.comp hR.2 hS.2))

/-- `f ∩ g`: the term `meet`. -/
def meet {A B : Syn} : Hom A B → Hom A B → Hom A B :=
  Quotient.lift₂ (s₁ := Tm.setoid A B) (s₂ := Tm.setoid A B) (fun R S => Quotient.mk _ ⟨R.1 || S.1, .meet R.2 S.2⟩)
    fun _ _ _ _ hR hS => Quotient.sound (And.intro
      (.le_meet (.trans (.meet_left _ _) hR.1) (.trans (.meet_right _ _) hS.1))
      (.le_meet (.trans (.meet_left _ _) hR.2) (.trans (.meet_right _ _) hS.2)))

/-- `f ∪ g`: the term `join`. -/
def join {A B : Syn} : Hom A B → Hom A B → Hom A B :=
  Quotient.lift₂ (s₁ := Tm.setoid A B) (s₂ := Tm.setoid A B) (fun R S => Quotient.mk _ ⟨R.1 || S.1, .join R.2 S.2⟩)
    fun _ _ _ _ hR hS => Quotient.sound (And.intro
      (.join_le (.trans hR.1 (.join_left _ _)) (.trans hS.1 (.join_right _ _)))
      (.join_le (.trans hR.2 (.join_left _ _)) (.trans hS.2 (.join_right _ _))))

/-- `𝟘`, the term `zero`. -/
def zero (A B : Syn) : Hom A B := Quotient.mk _ ⟨false, .zero⟩

/-- `Λ(f)`: the term `lam`. -/
def lam {A B : Syn} : Hom A B → Hom A (Obj.arr B) :=
  Quotient.lift (s := Tm.setoid A B) (fun R => Quotient.mk _ ⟨true, .lam R.2⟩)
    fun _ _ h => Quotient.sound (And.intro (.lam h.1 h.2) (.lam h.2 h.1))

/-- `⟦f⟧ρ`, the meaning of a hom: the one meaning its terms share, by soundness. -/
def Hom.den {A B : Syn} (ρ : Val) : Hom A B → Den A B :=
  Quotient.lift (s := Tm.setoid A B) (·.2.den ρ) fun _ _ h => Core.Rel.le_antisymm (h.1.sound ρ) (h.2.sound ρ)

variable {A B C D : Syn}

theorem Hom.den_mk {d : Bool} (t : Tm A B d) (ρ : Val) : Hom.den ρ (Quotient.mk (Tm.setoid A B) ⟨d, t⟩) = t.den ρ :=
  rfl

/-- `⟦−⟧ρ` keeps `𝟙`. -/
theorem Hom.den_id (ρ : Val) : Hom.den ρ (id A) = 𝟙 _ := rfl

/-- `⟦−⟧ρ` keeps composition: `⟦f g⟧ = ⟦f⟧ ⟦g⟧`. -/
theorem Hom.den_comp (ρ : Val) (f : Hom A B) (g : Hom B C) : Hom.den ρ (comp f g) = Hom.den ρ f ≫ Hom.den ρ g :=
  Quotient.inductionOn₂ f g fun _ _ => rfl

/-- `⟦−⟧ρ` keeps `°` where `Syn` has it: on a hom with a closed term (`conv` takes only `d = false`). -/
theorem Hom.den_conv (ρ : Val) (R : Tm A B false) :
    Hom.den ρ (Quotient.mk (Tm.setoid B A) ⟨false, .conv R⟩) = (Hom.den ρ (Quotient.mk (Tm.setoid A B) ⟨false, R⟩))° :=
  rfl

/-- `⟦−⟧ρ` keeps `∩`. -/
theorem Hom.den_meet (ρ : Val) (f g : Hom A B) : Hom.den ρ (meet f g) = Hom.den ρ f ∩ Hom.den ρ g :=
  Quotient.inductionOn₂ f g fun _ _ => rfl

/-- `⟦−⟧ρ` keeps `∪`. -/
theorem Hom.den_join (ρ : Val) (f g : Hom A B) : Hom.den ρ (join f g) = Hom.den ρ f ∪ Hom.den ρ g :=
  Quotient.inductionOn₂ f g fun _ _ => rfl

/-- `⟦−⟧ρ` keeps `𝟘`. -/
theorem Hom.den_zero (ρ : Val) : Hom.den ρ (zero A B) = 𝟘 := rfl

/-- `⟦−⟧ρ` keeps `Λ`, read as `lamDen` (`𝒫B` held as the canonical list). -/
theorem Hom.den_lam (ρ : Val) (f : Hom A B) : Hom.den ρ (lam f) = lamDen (Hom.den ρ f) :=
  Quotient.inductionOn f fun _ => rfl

theorem id_comp (f : Hom A B) : comp (id A) f = f :=
  Quotient.inductionOn f fun R => Quotient.sound (And.intro (.ax (.id_comp R.2)) (.ax_symm (.id_comp R.2)))

theorem comp_id (f : Hom A B) : comp f (id B) = f :=
  Quotient.inductionOn f fun R => Quotient.sound (And.intro (.ax (.comp_id R.2)) (.ax_symm (.comp_id R.2)))

theorem assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) : comp (comp f g) h = comp f (comp g h) :=
  Quotient.inductionOn₃ f g h fun R S T =>
    Quotient.sound (And.intro (.ax (.assoc R.2 S.2 T.2)) (.ax_symm (.assoc R.2 S.2 T.2)))

end Syn

/-! ### The laws (§4.2) -/

namespace Tm

variable {A B C : Obj} {d e : Bool} (ρ : Val)

theorem den_comp (R : Tm A B d) (S : Tm B C e) : (comp R S).den ρ = R.den ρ ≫ S.den ρ := rfl
theorem den_id : (id : Tm A A true).den ρ = 𝟙 _ := rfl
theorem den_zero : (zero : Tm A B false).den ρ = 𝟘 := rfl
theorem den_conv (R : Tm A B false) : (conv R).den ρ = (R.den ρ)° := rfl
theorem den_meet (R : Tm A B d) (S : Tm A B e) : (meet R S).den ρ = R.den ρ ∩ S.den ρ := rfl
theorem den_join (R : Tm A B d) (S : Tm A B e) : (join R S).den ρ = R.den ρ ∪ S.den ρ := rfl
theorem den_pair (R : Tm A B d) (S : Tm A C e) : (pair R S).den ρ = rpair (R.den ρ) (S.den ρ) := rfl
theorem den_prod {D : Obj} (R : Tm A B false) (S : Tm C D false) :
    (prod R S).den ρ = rprodMap (R.den ρ) (S.den ρ) := rfl
theorem den_junc (R : Tm A C false) (S : Tm B C false) : (junc R S).den ρ = Core.Rel.junc (R.den ρ) (S.den ρ) := rfl
theorem den_dom (R : Tm A B d) : (dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° := rfl
theorem den_ran (R : Tm A B false) : (ran R).den ρ = 𝟙 _ ∩ (R.den ρ)° ≫ R.den ρ := rfl
theorem den_share (k : Nat) (R : Tm A B d) : (share k R).den ρ = R.den Val.empty := rfl
theorem den_own (R : Tm A A d) : (own R).den ρ = R.den ρ := rfl

/-! The fixed points unfold where their variable occurs only positively: `Core.Rel.mu_fix`, `nu_fix` with the
    monotonicity `den_mono` gives. -/

theorem den_mu {k cap : Nat} {what : String} {b : Tm A B false} (h : b.pol true k = true) :
    (mu k what cap b).den ρ = b.den (ρ.bind k ((mu k what cap b).den ρ)) :=
  (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm

theorem den_nu {k : Nat} {S b : Tm A B false} (h : b.pol true k = true) :
    (nu k S b).den ρ = b.den (ρ.bind k ((nu k S b).den ρ)) :=
  (Core.Rel.nu_fix fun _ _ hXY => den_mono h hXY).symm

theorem den_refold {k : Nat} {what : String} {ch : Tm A A d} {b : Tm A B e} (h : b.pol true k = true) :
    (refold k what ch b).den ρ = b.den (ρ.bind k ((refold k what ch b).den ρ)) :=
  (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm

end Tm

end Rel.Lang
