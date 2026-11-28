import Rel.Lang.Laws.Map

/-! # Laws of freyd §2.5 `Freyd/S2_50.lean`, on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`
(`Rel/Programs/Aop/S2_50.lean` states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`). -/

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.inter_zero_den {A B : Obj} {R : Tm A B} (ρ : Val) :
    (Tm.meet R Tm.zero).den ρ = (Tm.zero (A := A) (B := B)).den ρ :=
  Core.Rel.ext fun _ _ => Iff.intro (fun h => h.2) fun h => False.elim h

end Rel.Lang
