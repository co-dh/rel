module

public import Rel.Lang.PlanSpec
public import Rel.RepCanon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `gatherCols` means `ValsB.gather` (`canonT_builds`, stage 1b)

A side `x : ValsB o A n` in registers is `ValsB.regVals x`, in `regsOf` order; `gatherB` of one register is
`kgather` of its `Enc`, which is what `ColB.gather` computes. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-- The register values of the side `x`, in `regsOf` order: an atom its `Enc`; a product its two sides'; an array its
    payload's count, `lo`, `hi`, then its payload's; a band sum its one `Opt`; a general sum its tag, then its two
    summands'; `1` none. -/
def _root_.Rel.ValsB.regVals : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → List Val
  | _, .atom _, _, x => [Reg.put (ColB.enc x)]
  | _, .prod _ _, _, x => ValsB.regVals x.1 ++ ValsB.regVals x.2
  | _, .arr _, _, ⟨c, lo, hi, f⟩ => [.size c, Reg.put (ColB.enc lo), Reg.put (ColB.enc hi)] ++ ValsB.regVals f
  | _, .sum _ _, _, s => match ValsB.view s with
    | .opt _ x => [Reg.put x.enc]
    | .gen _ tag x y => Reg.put tag.enc :: (ValsB.regVals x ++ ValsB.regVals y)
  | _, .one, _, _ => []

/-- Every `Enc` is a register that reads back as itself (`foR` its parts, `pos` none). -/
theorem enc_get_put : ∀ e : Enc, (Reg.get? (Reg.put e) : Option Enc) = some e
  | .foR m p => foR_get_put m p
  | .pos => by
    have hp : (Reg.put (Enc.pos : Enc) : Val) = .ctor (Enc.pos : Enc).ctorIdx #[] #[] := by with_unfolding_all rfl
    rw [hp]
    dsimp only [Reg.get?]
    conv => lhs; whnf
    rw [Array.mapM_eq_mapM_toList]
    simp

/-- `ColB.gather` is `kgather` of the column's `Enc`, at either ownership. -/
theorem ColB.gather_kgather : ∀ {o : Bool} {t : QAtomicType} {n m : USize} {ix : Enc} {x : ColB o t n}
    {y : ColB o t m}, ColB.gather m ix x = .ok y → kgather m ix n (ColB.enc x) = .ok (ColB.enc y)
  | false, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Arr.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h
  | true, _, n, m, ix, x, y, h => by
    simp only [ColB.gather, Opt.gather] at h
    split at h
    · next o ho => cases h; exact ho
    · cases h

/-- `gatherB m ix n e`, then `c`: the registers `m`, `n` hold the counts `mv`, `nv`, `ix` and `e` the `Enc`s `iv`,
    `ev`; the new register holds `kgather mv iv nv ev`. -/
theorem gatherB_builds {fg fg' : Array Fun × Array Fun} {rs out : Array Val} {m ix n e : Nat} {mv nv : USize}
    {iv ev ov : Enc} {c : Nat → Bld (Array Nat)}
    (hm : rs[m]? = some (.size mv)) (hi : rs[ix]? = some (Reg.put iv)) (hn : rs[n]? = some (.size nv))
    (he : rs[e]? = some (Reg.put ev)) (hk : kgather mv iv nv ev = .ok ov)
    (hc : Builds abiOf fg fg' (c rs.size) (rs.push (Reg.put ov)) out) :
    Builds abiOf fg fg' (gatherB m ix n e >>= c) rs out := by
  unfold gatherB
  refine Builds.call1 (vs := #[.size mv, Reg.put iv, .size nv, Reg.put ev]) (v := Reg.put ov)
    (by with_unfolding_all simp [abiOf, Rel.Lang.Plan.abi, List.find?]) (by with_unfolding_all rfl) ?_ ?_ rfl hc
  · rw [List.mapM_toArray]
    simp [reg, hm, hi, hn, he]
    rfl
  · have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
    simp [arg, hsz, enc_get_put, hk, Out.out]
    rfl

/-! ### `gatherCols_builds`: the columns of a side, and what renaming their registers keeps -/

/-- The columns `cs` lay out a side of `A` node for node as `ValsB` stores it (`Col`): an atom, or a sum in band
    (`Obj.band`), one `atom` column of that atom; an array an `arr` column over its payload's columns; a sum not in band
    a `sum` column over its summands'; a product its two sides' columns one after the other; `1` none. -/
inductive Fits : Obj → Cols → Prop
  | atom {t : QAtomicType} {p : String} {e : Nat} : Fits (.atom t) [.atom p t e]
  | band {a b : Obj} {t : QAtomicType} {p : String} {e : Nat} : Obj.band a b = some t → Fits (.sum a b) [.atom p t e]
  | arr {b : Obj} {p : String} {m lo hi : Nat} {f : Cols} : Fits b f → Fits (.arr b) [.arr p m lo hi f]
  | sum {a b : Obj} {p : String} {tag : Nat} {x y : Cols} : Obj.band a b = none → Fits a x → Fits b y →
      Fits (.sum a b) [.sum p tag x y]
  | prod {a b : Obj} {xs ys : Cols} : Fits a xs → Fits b ys → Fits (.prod a b) (xs ++ ys)
  | one : Fits .one []

/-- `Fits` reads only the columns' shape: the columns `withRegs` hands back (`regsOf_spec`) fit as the ones it renamed. -/
theorem Fits.shape {A : Obj} {cs : Cols} (h : Fits A cs) : ∀ {cs' : Cols}, Cols.shape cs' = Cols.shape cs → Fits A cs' := by
  have one : ∀ {cs' : Cols} {c : Col}, Cols.shape cs' = Cols.shape [c] → ∃ c', cs' = [c'] ∧ Col.shape c' = Col.shape c :=
    fun e => by
      rw [Cols.shape_eq_map, Cols.shape_eq_map, List.map_cons, List.map_nil, List.map_eq_singleton_iff] at e
      exact e
  induction h with
  | atom =>
    intro cs' e; obtain ⟨c, rfl, hc⟩ := one e
    cases c <;> simp only [Col.shape, Col.atom.injEq, reduceCtorEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc; exact .atom
  | band hb =>
    intro cs' e; obtain ⟨c, rfl, hc⟩ := one e
    cases c <;> simp only [Col.shape, Col.atom.injEq, reduceCtorEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc; exact .band hb
  | arr _ ih =>
    intro cs' e; obtain ⟨c, rfl, hc⟩ := one e
    cases c <;> simp only [Col.shape, Col.arr.injEq, reduceCtorEq, true_and] at hc
    obtain ⟨rfl, hf⟩ := hc; exact .arr (ih hf)
  | sum hb _ _ ihx ihy =>
    intro cs' e; obtain ⟨c, rfl, hc⟩ := one e
    cases c <;> simp only [Col.shape, Col.sum.injEq, reduceCtorEq, true_and] at hc
    obtain ⟨rfl, hx, hy⟩ := hc; exact .sum hb (ihx hx) (ihy hy)
  | prod _ _ ihx ihy =>
    intro cs' e
    rw [Cols.shape_eq_map, Cols.shape_eq_map, List.map_append, List.map_eq_append_iff] at e
    obtain ⟨xs', ys', rfl, hx, hy⟩ := e
    exact .prod (ihx (by rw [Cols.shape_eq_map, Cols.shape_eq_map]; exact hx))
      (ihy (by rw [Cols.shape_eq_map, Cols.shape_eq_map]; exact hy))
  | one =>
    intro cs' e
    rw [Cols.shape_eq_map] at e
    obtain rfl := List.map_eq_nil_iff.1 e
    exact .one

mutual
theorem Col.size_shape : ∀ c : Col, Col.size (Col.shape c) = Col.size c
  | .atom .. => rfl
  | .arr _ _ _ _ f => by simp only [Col.shape, Col.size, Col.sizes_shape f]
  | .sum _ _ x y => by simp only [Col.shape, Col.size, Col.sizes_shape x, Col.sizes_shape y]
theorem Col.sizes_shape : ∀ cs : Cols, Col.sizes (Cols.shape cs) = Col.sizes cs
  | [] => rfl
  | c :: cs => by simp only [Cols.shape, Col.sizes, Col.size_shape c, Col.sizes_shape cs]
end

/-- Columns of one shape are of one size: the guard `gatherCols` puts on the column `funC` hands back holds. -/
theorem Col.size_of_shape {c c' : Col} (h : Col.shape c' = Col.shape c) : Col.size c' = Col.size c := by
  rw [← Col.size_shape c', h, Col.size_shape]

/-- `gatherCols` gathers each column on its own (`attach` serves only its termination): a product side's columns are
    its two sides' gathered one after the other. -/
theorem gatherCols_append (m ix n : Nat) (xs ys : Cols) : gatherCols m ix n (xs ++ ys) =
    (do let a ← gatherCols m ix n xs; let b ← gatherCols m ix n ys; Pure.pure (a ++ b)) := by
  unfold gatherCols
  rw [List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.mapM_subtype (g := fun c => _) (fun _ _ => rfl),
    List.mapM_subtype (g := fun c => _) (fun _ _ => rfl), List.unattach_attach, List.unattach_attach,
    List.unattach_attach, List.mapM_append]

end Rel.Lang.Plan
