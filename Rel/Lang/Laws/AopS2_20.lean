import Rel.Lang.Laws.Map

/-! # Distributive-allegory laws of freyd §2.2 `Freyd/S2_20.lean`, on the concrete core

Each `Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`, so that
`Rel/Programs/Aop/S2_20.lean` states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. The five coproduct equations of
§2.214 are laws of the injections `inl`, `inr` of the sum `α + β`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.recip_union_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.conv (Tm.join R S)).den ρ = (Tm.join (Tm.conv S) (Tm.conv R)).den ρ :=
  Core.Rel.ext fun _ _ => Or.comm

theorem Tm.recip_zero_den {A B : Obj} (ρ : Val) :
    (Tm.conv (Tm.zero (A := A) (B := B))).den ρ = (Tm.zero (A := B) (B := A)).den ρ :=
  Core.Rel.ext fun _ _ => Iff.rfl

theorem Tm.inl_inl_conv_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.inl (A := A) (B := B)) (Tm.conv Tm.inl)).den ρ = (Tm.id (A := A)).den ρ :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨_, h₁, h₂⟩ => Sum.inl.inj (h₁.symm.trans h₂) ▸ rfl,
    fun h => ⟨_, rfl, h ▸ rfl⟩⟩

theorem Tm.inr_inr_conv_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.inr (A := A) (B := B)) (Tm.conv Tm.inr)).den ρ = (Tm.id (A := B)).den ρ :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨_, h₁, h₂⟩ => Sum.inr.inj (h₁.symm.trans h₂) ▸ rfl,
    fun h => ⟨_, rfl, h ▸ rfl⟩⟩

theorem Tm.inl_inr_conv_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.inl (A := A) (B := B)) (Tm.conv Tm.inr)).den ρ = (Tm.zero (A := A) (B := B)).den ρ :=
  Core.Rel.ext fun _ _ => Iff.intro (fun ⟨_, h₁, h₂⟩ => nomatch h₁.symm.trans h₂) fun h => False.elim h

theorem Tm.inr_inl_conv_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.inr (A := A) (B := B)) (Tm.conv Tm.inl)).den ρ = (Tm.zero (A := B) (B := A)).den ρ :=
  Core.Rel.ext fun _ _ => Iff.intro (fun ⟨_, h₁, h₂⟩ => nomatch h₁.symm.trans h₂) fun h => False.elim h

theorem Tm.inl_conv_inl_union_den {A B : Obj} (ρ : Val) :
    (Tm.join (Tm.comp (Tm.conv Tm.inl) Tm.inl) (Tm.comp (Tm.conv Tm.inr) Tm.inr) :
      Tm (Obj.sum A B) (Obj.sum A B)).den ρ = (Tm.id (A := Obj.sum A B)).den ρ :=
  Core.Rel.ext fun s _ => ⟨fun h => h.elim (fun ⟨_, h₁, h₂⟩ => (h₁ : _ = _).trans (h₂ : _ = _).symm) fun ⟨_, h₁, h₂⟩ => (h₁ : _ = _).trans (h₂ : _ = _).symm,
    fun h => h ▸ s.rec (fun x => .inl ⟨x, rfl, rfl⟩) fun y => .inr ⟨y, rfl, rfl⟩⟩

end Rel.Lang
