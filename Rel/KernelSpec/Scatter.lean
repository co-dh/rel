import Rel.Kernel.Scatter

/-! `scatter`'s law (design §4: `out[ix[k]] = e[k]`), on the words `Enc.raw` reads from its arguments. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- The fold `scatterWords` runs, over the first `m` rows from any start `o`: it succeeds exactly when every index is
below `n`, keeps the size, leaves a cell no row names as it was, and holds in a named cell the last row naming it. -/
private theorem scatterFold (I : Nat → Nat) (X : Nat → UInt64) (n : Nat) (err : Nat → String)
    (o : Array UInt64) (m : Nat) :
    let step := fun (o : Array UInt64) k =>
      if I k < n then (Except.ok (o.setIfInBounds (I k) (X k)) : Except String _) else .error (err k)
    ((∃ ws, (List.range m).foldlM step o = .ok ws) ↔ ∀ k < m, I k < n) ∧
    ∀ ws, (List.range m).foldlM step o = .ok ws → ws.size = o.size ∧
      (∀ j, (∀ k < m, I k ≠ j) → ws[j]? = o[j]?) ∧
      ∀ k < m, (∀ k', k < k' → k' < m → I k' ≠ I k) → I k < o.size → ws[I k]? = some (X k) := by
  intro step
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true, and_true]
    exact ⟨⟨o, rfl⟩, fun ws h => by obtain rfl : o = ws := Except.ok.inj h; exact ⟨rfl, fun _ _ => rfl⟩⟩
  | succ m ih =>
    obtain ⟨ihx, ihw⟩ := ih
    rw [List.range_succ, List.foldlM_append]
    cases h1 : (List.range m).foldlM step o with
    | error s =>
      refine ⟨⟨fun ⟨ws, h⟩ => (by simp [bind, Except.bind] at h), fun h => ?_⟩,
        fun ws h => (by simp [bind, Except.bind] at h)⟩
      obtain ⟨ws, hw⟩ := ihx.2 fun k hk => h k (by omega)
      rw [h1] at hw; cases hw
    | ok w =>
      obtain ⟨hs, hfix, hlast⟩ := ihw w h1
      have hall := ihx.1 ⟨w, h1⟩
      by_cases hm : I m < n
      · have he : ((Except.ok w : Except String _) >>= fun o' => [m].foldlM step o') =
            .ok (w.setIfInBounds (I m) (X m)) := by simp [bind, Except.bind, List.foldlM, step, hm]; rfl
        rw [he]
        refine ⟨⟨fun _ k hk => ?_, fun _ => ⟨_, rfl⟩⟩, fun ws h => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact hall k hk
          · exact hm
        · cases h
          refine ⟨by simp [hs], fun j hj => ?_, fun k hk hl hko => ?_⟩
          · rw [Array.getElem?_setIfInBounds_ne (hj m (by omega)), hfix j fun k hk => hj k (by omega)]
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · rw [Array.getElem?_setIfInBounds_ne (hl m hk (by omega)),
                hlast k hk (fun k' a b => hl k' a (by omega)) hko]
            · rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
      · have he : ((Except.ok w : Except String _) >>= fun o' => [m].foldlM step o') = .error (err m) := by
          simp [bind, Except.bind, List.foldlM, step, hm]
        rw [he]
        exact ⟨⟨fun ⟨_, h⟩ => (by cases h), fun h => absurd (h m (by omega)) hm⟩, fun _ h => (by cases h)⟩

/-- A row's index as `scatterWords` reads it. -/
private abbrev ixAt (is : Array UInt64) (k : Nat) : Nat := (is[k]?.getD 0).toNat

/-- `scatterWords` answers exactly when every index is below `n`; its `n` cells are `fill` where no row names them,
and `es[k]` at `is[k]` where no later row names the same cell. -/
theorem scatterWords_spec (is es : Array UInt64) (n : Nat) (fill : UInt64) :
    ((∃ ws, scatterWords is es n fill = .ok ws) ↔ ∀ k < is.size, ixAt is k < n) ∧
    ∀ ws, scatterWords is es n fill = .ok ws → ws.size = n ∧
      (∀ j < n, (∀ k < is.size, ixAt is k ≠ j) → ws[j]? = some fill) ∧
      ∀ k < is.size, (∀ k', k < k' → k' < is.size → ixAt is k' ≠ ixAt is k) →
        ws[ixAt is k]? = some (es[k]?.getD 0) := by
  obtain ⟨hx, hw⟩ := scatterFold (ixAt is) (fun k => es[k]?.getD 0) n
    (fun k => s!"scatter: index {is[k]?.getD 0} at row {k} is not below n = {n}") (Array.replicate n fill) is.size
  refine ⟨hx, fun ws h => ?_⟩
  obtain ⟨hs, hfix, hlast⟩ := hw ws h
  have hall := hx.1 ⟨ws, h⟩
  refine ⟨by simpa using hs, fun j hj hn => by rw [hfix j hn]; simp [hj], fun k hk hl => hlast k hk hl ?_⟩
  simpa using hall k hk

/-- What `packedWords` answers is `Enc.raw` at a 64-bit column, `m` words of it. -/
theorem packedWords_raw (what : String) (m : USize) (e : Enc) (ws : Array UInt64)
    (h : packedWords what m e = .ok ws) : ws = raw .long m e ∧ ws.size = m.toNat := by
  unfold packedWords at h
  split at h
  · rename_i lg bases widths payload
    split at h
    · cases h
    · rename_i hp
      cases h
      refine ⟨rfl, ?_⟩
      simp [raw, unpack, hp]
  · cases h

/-- Design §4's `scatter` law: an answer of `kscatter` is `Coc.packedOf` at `lgEnc` of `n` words `ws`, read from the
`m` words `is` and `es` that `Enc.raw` reads from `ix` and `e`: every index is below `n`, a cell no row names is
`fill`, and `ws[is[k]] = es[k]` for every row `k` no later row overrides. -/
theorem raw_scatter (m : USize) (ix e : Enc) (n : USize) (fill : UInt64) (o : Enc)
    (h : kscatter m ix e n fill = .ok o) :
    let is := raw .long m ix
    let es := raw .long m e
    ∃ ws : Array UInt64, o = Coc.packedOf Column.lgEnc 8 (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8) ∧
      is.size = m.toNat ∧ es.size = m.toNat ∧ ws.size = n.toNat ∧
      (∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat) ∧
      (∀ j < n.toNat, (∀ k < m.toNat, (is[k]?.getD 0).toNat ≠ j) → ws[j]? = some fill) ∧
      ∀ k < m.toNat, (∀ k', k < k' → k' < m.toNat → is[k']?.getD 0 ≠ is[k]?.getD 0) →
        ws[(is[k]?.getD 0).toNat]? = some (es[k]?.getD 0) := by
  intro is es
  unfold kscatter at h
  cases hi : packedWords "scatter: ix" m ix with
  | error s => simp [hi, bind, Except.bind] at h
  | ok is' =>
    cases he : packedWords "scatter: e" m e with
    | error s => simp [hi, he, bind, Except.bind] at h
    | ok es' =>
      obtain ⟨rfl, hisz⟩ := packedWords_raw _ _ _ _ hi
      obtain ⟨rfl, hesz⟩ := packedWords_raw _ _ _ _ he
      cases hw : scatterWords (raw .long m ix) (raw .long m e) n.toNat fill with
      | error s => simp [hi, he, hw, bind, Except.bind] at h
      | ok ws =>
        simp only [hi, he, hw, bind, Except.bind, pure, Except.pure] at h
        have h8 : USize.ofNat32 8 (by decide) = 8 := USize.toNat_inj.mp (by simp)
        rw [h8] at h
        obtain ⟨hx, hok⟩ := scatterWords_spec (raw .long m ix) (raw .long m e) n.toNat fill
        obtain ⟨hs, hfix, hlast⟩ := hok ws hw
        have hall := hx.1 ⟨ws, hw⟩
        refine ⟨ws, (Except.ok.inj h).symm, hisz, hesz, hs, fun k hk => hall k (by omega), fun j hj hn => hfix j hj
          fun k hk => hn k (by omega), fun k hk hl => hlast k (by omega) fun k' a b hc => hl k' a (by omega) ?_⟩
        exact UInt64.toNat_inj.mp hc

end Rel.Verify
