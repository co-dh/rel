import Rel.RepMerge
namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

theorem Tab.mergeDiff_holds {k v : Obj} {X T V U : Tab k v} (hX : X.WF) (hT : T.WF)
    (hs : ∀ i j : Fin X.n.toNat, i.1 < j.1 →
      (Obj.prod k v).lt (X.key.row i, X.val.row i) (X.key.row j, X.val.row j))
    (h : X.mergeDiff T = .ok (V, U)) : False := by
  unfold Tab.mergeDiff at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Tc, hTc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨r, hh⟩, hrk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nm, hnm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨d, sel⟩, hwh, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gk, hgk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gv, hgv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rD, hrD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨posD, hposD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ones, hones, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kg, hkg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨posX, hposX, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨N, hN, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix1, hix1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix2, hix2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cc, hcc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Vv, hVv, h⟩ := h
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  trace_state
  sorry
