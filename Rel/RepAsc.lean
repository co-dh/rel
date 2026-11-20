import Rel.RepWhere
import Rel.AscOrder
import Rel.Run.Asc

/-! The law of `Tab.asc` (`Rel/Run/Asc.lean`): each array to its stable sort permutation `ascL`. `kasc` sorts every
cell's elements at once, keyed by their cell; the one stable order of those keys (`stable_unique`) is the cells'
`ascL`s laid one after another, so `kasc`'s permutation equals it, not merely refines it. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc Rel.Rep

/-- **The bridge** for `asc`'s keys: `kasc` orders two rows by a cell column `G` (words below `2^63`, whose `i64`
order code is the word plus `2^63`), then by the elements' order codes `f`. -/
theorem lexLe_cell {T : USize} {G e : Enc} {t : QAtomicType} {f : UInt64 → UInt64} (hf : ascOrd t = some f)
    (hG : (raw .i64 T G).size = T.toNat) (he : (raw .i64 T e).size = T.toNat) {k k' : Nat} (hk : k < T.toNat)
    (hk' : k' < T.toNat) (ha : ((raw .i64 T G)[k]?.getD 0).toNat < 2 ^ 63)
    (ha' : ((raw .i64 T G)[k']?.getD 0).toNat < 2 ^ 63) :
    lexLe (ascKeys T [(.atom .i64, G), (.atom t, e)]) k k' = true ↔
      ((raw .i64 T G)[k]?.getD 0).toNat < ((raw .i64 T G)[k']?.getD 0).toNat ∨
        ((raw .i64 T G)[k]?.getD 0).toNat = ((raw .i64 T G)[k']?.getD 0).toNat ∧
          (f ((raw .i64 T e)[k]?.getD 0)).toNat ≤ (f ((raw .i64 T e)[k']?.getD 0)).toNat := by
  have hc : ∀ x : UInt64, x.toNat < 2 ^ 63 → (ordCode 8 false true x).toNat = x.toNat + 2 ^ 63 := fun x hx => by
    simpa using Lang.ordCode_i64_nonneg hx
  have h64 : ascOrd .i64 = some (ordCode 8 false true) := rfl
  rw [Array.getElem?_eq_getElem (show k < (raw .i64 T G).size by omega), Option.getD_some] at ha
  rw [Array.getElem?_eq_getElem (show k' < (raw .i64 T G).size by omega), Option.getD_some] at ha'
  simp only [ascKeys, ascKey, h64, hf, Option.getD_some, List.cons_append, List.nil_append, List.append_nil, lexLe,
    Array.getElem?_map, Array.getElem?_eq_getElem (show k < (raw .i64 T G).size by omega),
    Array.getElem?_eq_getElem (show k' < (raw .i64 T G).size by omega),
    Array.getElem?_eq_getElem (show k < (raw .i64 T e).size by omega),
    Array.getElem?_eq_getElem (show k' < (raw .i64 T e).size by omega), Option.map_some, Option.getD_some,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_true, UInt64.lt_iff_toNat_lt,
    ← UInt64.toNat_inj, hc _ ha, hc _ ha']
  omega

namespace Tab

open Classical in
/-- **`asc X` denotes `ascL`** on each array of `X`: `kasc`'s permutation of the expanded elements, keyed by cell
(`lexLe_cell`) and then by value (`Obj.key_ordCode`), is the cells' `ascL`s one after another (`stable_unique`), each
read back as offsets `u` within its run. -/
theorem asc_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {res : Tab (.arr B) (.arr .long)}
    (h : Tab.asc X = .ok res) (xs : List B.El) (ys : List Int64) :
    res.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys = (ascL B xs).map Int64.ofNat := by
  cases B
  all_goals try (obtain ⟨m, lo, up, f⟩ := X; first | cases h | simp [Tab.asc, throw, throwThe, MonadExceptOf.throw] at h; done)
  rename_i t
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.asc] at h
  split at h
  · rename_i wd sgn hL
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨v, hv, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, ha, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨gp, hgp, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨pay, hpay, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
    rw [canon_holds h]
    have hm63 : m.toNat < 2 ^ 63 := by omega
    have hn63 : n.toNat < 2 ^ 63 := by omega
    have hnm : n.toNat * m.toNat < 2 ^ 63 := by omega
    have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
    obtain ⟨SN, EN, hse', hb1, hrow⟩ := cellSpan_spec hse hm63 f
    obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i := ⟨_, fun _ => rfl⟩
    have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := by
      intro i hi
      have es := (colMap_raw hw).2.2.2 i hi
      rw [(hse' i hi).2, (hse' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, hwN, toUInt64_sub (hb1 i).1]
    have hwm : ∀ i, wN i ≤ m.toNat := fun i => by have := hb1 i; rw [hwN]; omega
    have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * m.toNat := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [sum_range_succ', Nat.succ_mul]; have := hwm k; omega
    have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by have := hsum n.toNat; omega
    obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
    -- the element at row `Σ_{<g} w + d` is cell `g`'s element `d`
    have hvt : ∀ g < n.toNat, ∀ d < wN g, ∀ (ht : ((List.range g).map wN).sum + d < T.toNat)
        (hd : SN g + d < m.toNat), Vals.row v ⟨_, ht⟩ = Vals.row f ⟨_, hd⟩ := by
      intro g hg d hdw ht hd
      obtain ⟨j, hj, hvj⟩ := Vals.gather_row f hv ⟨_, ht⟩
      rw [hvj]; congr 1; apply Fin.ext; rw [← hj]
      have hgS : ((List.range g).map wN).sum + wN g ≤ ((List.range n.toNat).map wN).sum := by
        rw [← sum_range_succ']; exact sum_range_mono wN hg
      obtain ⟨hG, hu⟩ := hrun g hg (((List.range g).map wN).sum + d) (by omega) (by omega)
      have es := (colMap_raw hix).2.2.2 _ ht
      rw [(kgather_word hsg _ ht).2, hG, toNat_toUInt64 (by omega), (hse' g hg).1, hu] at es
      simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, ← UInt64.ofNat_add, Nat.add_sub_cancel_left, toNat_toUInt64 (by omega)]
    obtain ⟨off, hoff⟩ : ∃ F : Nat → Nat, ∀ g, F g = ((List.range g).map wN).sum := ⟨_, fun _ => rfl⟩
    simp only [← hoff] at hrun hTn hvt
    have hrun' : ∀ g < n.toNat, off g + wN g ≤ T.toNat := fun g hg => by
      rw [hTn, hoff, hoff, ← sum_range_succ']; exact sum_range_mono wN hg
    -- `kasc`'s columns: both read, `T` words each, the elements' valid
    have hg : t ≠ .general := by rintro rfl; simp [ascLayout, orderKind] at hL
    have hs : t ≠ .sym := by rintro rfl; simp [ascLayout, orderKind] at hL
    have hf : ascOrd t = some (ordCode wd false sgn) := by simp [ascOrd, hL]
    obtain ⟨cs, hcs, hp, -⟩ := kasc_grade ha
    obtain ⟨hcl, hcf⟩ := mapM_ok hcs
    obtain ⟨⟨x0, k0⟩, ⟨x1, k1⟩, rfl⟩ : ∃ c0 c1, cs = [c0, c1] := by
      match cs, hcl with | [c0, c1], _ => exact ⟨c0, c1, rfl⟩
    have h0 := hcf 0 _ _ rfl rfl
    have h1 := hcf 1 _ _ rfl rfl
    obtain ⟨hx0, hs0, -, -⟩ := ascCol_ok h0
    obtain ⟨hx1, hs1, -, -⟩ := ascCol_ok h1
    have hGsz : (raw .i64 T G).size = T.toNat := hx0 ▸ hs0
    have hvsz : (raw .i64 T v.enc).size = T.toNat := hx1 ▸ hs1
    have hvval : Kernel.Enc.Valid T v.enc := ascCol_valid h1
    obtain ⟨rk, hrk⟩ : ∃ F : Nat → Nat, ∀ k, F k = (ordCode wd false sgn ((raw .i64 T v.enc)[k]?.getD 0)).toNat :=
      ⟨_, fun _ => rfl⟩
    -- an element's key is its order code (`Obj.key_ordCode`)
    have hkey : ∀ k (hk : k < T.toNat), (Obj.atom t).key (Vals.row (A := .atom t) v ⟨k, hk⟩) = [rk k] := fun k hk => by
      obtain ⟨a, ha, hu, hga⟩ := Arr.get_raw_atom v hvval hg hs ⟨k, hk⟩
      rw [Vals.row_atom, hga, hrk, ha, Option.getD_some]; exact Obj.key_ordCode hL hg a hu
    -- rows `off g + d` and `off g' + d'` in `kasc`'s order: by cell, then by code
    have hlex : ∀ g g' d d', g < n.toNat → g' < n.toNat → d < wN g → d' < wN g' →
        (lexLe (ascKeys T [(.atom .i64, G), (.atom t, v.enc)]) (off g + d) (off g' + d') = true ↔
          g < g' ∨ g = g' ∧ rk (off g + d) ≤ rk (off g' + d')) := by
      intro g g' d d' hg hg' hd hd'
      have hrg := hrun' g hg; have hrg' := hrun' g' hg'
      have e1 := (hrun g hg (off g + d) (by omega) (by omega)).1
      have e2 := (hrun g' hg' (off g' + d') (by omega) (by omega)).1
      rw [lexLe_cell hf hGsz hvsz (by omega) (by omega) (by rw [e1, toNat_toUInt64 (by omega)]; omega)
        (by rw [e2, toNat_toUInt64 (by omega)]; omega), e1, e2, toNat_toUInt64 (by omega),
        toNat_toUInt64 (by omega), hrk, hrk]
    -- cell `g` is `wN g` long, its element `d` the row `off g + d`
    have hxl : ∀ g (hg : g < n.toNat), (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩).length = wN g :=
      fun g hg => by rw [hrow ⟨g, hg⟩, List.length_map, List.length_range', hwN]
    have hcell : ∀ g (hg : g < n.toNat) d (hd : d < wN g),
        (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩)[d]? =
          some (Vals.row (A := .atom t) v ⟨off g + d, by have := hrun' g hg; omega⟩) := fun g hg d hd => by
      have hd' : SN g + d < m.toNat := by have := hb1 g; rw [hwN] at hd; omega
      rw [List.getElem?_eq_getElem (by rw [hxl g hg]; exact hd), hvt g hg d hd (by have := hrun' g hg; omega) hd']
      simp only [hrow ⟨g, hg⟩, List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos hd']
    have hle : ∀ g (hg : g < n.toNat) d d', d < wN g → d' < wN g →
        (ascLe (.atom t) (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩) d d' = true ↔
          rk (off g + d) ≤ rk (off g + d')) := fun g hg d d' hd hd' => by
      have hrg := hrun' g hg
      simp only [ascLe, hcell g hg d hd, hcell g hg d' hd', Option.getD_some, Bool.not_eq_true',
        decide_eq_false_iff_not, Obj.lt, hkey]
      simp [List.cons_lt_cons_iff]
    -- the candidate: cell `g`'s `ascL`, shifted to its run, one cell after another
    obtain ⟨σ, hσ⟩ : ∃ F : Nat → List Nat, ∀ g (hg : g < n.toNat),
        F g = ascL (.atom t) (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩) :=
      ⟨fun g => if hg : g < n.toNat then ascL _ (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩) else [],
        fun g hg => dif_pos hg⟩
    have hσp : ∀ g < n.toNat, (σ g).Perm (List.range (wN g)) := fun g hg => by
      rw [hσ g hg, ← hxl g hg]; exact (ascL_spec _ _).1
    have hσm : ∀ g < n.toNat, ∀ d ∈ σ g, d < wN g := fun g hg d hd =>
      List.mem_range.1 ((hσp g hg).mem_iff.1 hd)
    let R : Nat → Nat → Prop := fun k k' =>
      lexLe (ascKeys T [(.atom .i64, G), (.atom t, v.enc)]) k k' = true ∧
        (lexLe (ascKeys T [(.atom .i64, G), (.atom t, v.enc)]) k' k = true → k < k')
    have hLs : (((List.range n.toNat).map fun g => (σ g).map (off g + ·)).flatten).Pairwise R := by
      rw [List.pairwise_flatten, List.pairwise_map]
      refine ⟨fun l hl => ?_, List.pairwise_lt_range.imp_of_mem fun {g g'} hg hg' hlt => ?_⟩
      · obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hl
        have hg := List.mem_range.1 hgm
        have hs := (ascL_spec (.atom t) (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ ⟨g, hg⟩)).2
        rw [← hσ g hg] at hs
        rw [List.pairwise_map]
        refine hs.imp_of_mem fun {d d'} hd hd' hr => ?_
        have h1 := hσm g hg d hd; have h2 := hσm g hg d' hd'
        refine ⟨(hlex g g d d' hg hg h1 h2).2 (.inr ⟨rfl, (hle g hg d d' h1 h2).1 hr.1⟩), fun hr' => ?_⟩
        rcases (hlex g g d' d hg hg h2 h1).1 hr' with c | ⟨-, c⟩
        · omega
        · exact Nat.add_lt_add_left (hr.2 ((hle g hg d' d h2 h1).2 c)) _
      · have hg := List.mem_range.1 hg; have hg' := List.mem_range.1 hg'
        intro x hx y hy
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
        obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hy
        have h1 := hσm g hg d hd; have h2 := hσm g' hg' d' hd'
        refine ⟨(hlex g g' d d' hg hg' h1 h2).2 (.inl hlt), fun hr' => ?_⟩
        rcases (hlex g' g d' d hg' hg h2 h1).1 hr' with c | ⟨c, -⟩ <;> omega
    have hLp : (((List.range n.toNat).map fun g => (σ g).map (off g + ·)).flatten).Perm (List.range T.toNat) := by
      have hr := filter_runs wN (fun _ => true) n.toNat
      simp only [← hoff] at hr
      rw [List.filter_eq_self.2 fun _ _ => rfl, show (fun g => (List.range' (off g) (wN g)).filter fun _ => true) =
        fun g => List.range' (off g) (wN g) from funext fun g => List.filter_eq_self.2 fun _ _ => rfl] at hr
      rw [hTn, hr]
      have : ∀ l : List Nat, (∀ g ∈ l, g < n.toNat) → (l.map fun g => (σ g).map (off g + ·)).flatten.Perm
          (l.map fun g => List.range' (off g) (wN g)).flatten := by
        intro l; induction l with
        | nil => intro _; exact .refl _
        | cons g l ih =>
          intro hl; simp only [List.map_cons, List.flatten_cons]
          refine List.Perm.append ?_ (ih fun x hx => hl x (.tail _ hx))
          rw [List.range'_eq_map_range]; exact (hσp g (hl g (.head _))).map _
      exact this _ fun g hg => List.mem_range.1 hg
    obtain ⟨hperm, hsort⟩ := ascGrade_spec T.toNat (ascKeys T [(.atom .i64, G), (.atom t, v.enc)])
    -- the one stable order: `kasc`'s permutation is the candidate
    have hpsL := stable_unique (hperm.trans hLp.symm) hsort hLs
    have hpl : (ascGrade T.toNat (ascKeys T [(.atom .i64, G), (.atom t, v.enc)])).length = T.toNat := by
      simpa using hperm.length_eq
    suffices hY' : ∀ i : Fin n.toNat, Vals.row Y i =
        (ascL (.atom t) (Vals.row (A := .arr (.atom t)) ⟨m, lo, up, f⟩ i)).map Int64.ofNat by
      simp only [Tab.Holds]
      constructor
      · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hY' i⟩
      · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hY' i⟩
    intro i
    have hTo : T.toNat < 2 ^ 63 := by rw [hTn, hoff]; exact hsn
    have hiS := hrun' i.1 i.2
    rw [Vals.cells_row hY wN hww (by rw [hTn, hoff]; exact Nat.le_refl _) hTo i, ← hoff, ← hσ i.1 i.2]
    apply List.ext_getElem (by simp [List.length_range', (hσp i.1 i.2).length_eq])
    intro d h1 h2
    have hd : d < wN i.1 := by simpa using h1
    have hdσ : d < (σ i.1).length := by rw [(hσp i.1 i.2).length_eq, List.length_range]; exact hd
    have hk : off i.1 + d < T.toNat := by omega
    -- position `off i + d` of the candidate is cell `i`'s `σ` at `d`, shifted
    have hFd := getElem?_flatten_runs (fun g => (σ g).map (off g + ·)) n.toNat i.1 d i.2 (by simpa using hdσ)
    have hlen : ((List.range i.1).map fun g => ((σ g).map (off g + ·)).length) = (List.range i.1).map wN :=
      List.map_congr_left fun g hg => by
        rw [List.length_map, (hσp g (by have := List.mem_range.1 hg; omega)).length_eq, List.length_range]
    rw [hlen, ← hoff, ← hpsL, List.getElem?_map, List.getElem?_eq_getElem hdσ, Option.map_some] at hFd
    have hpk : (raw .i64 T p)[off i.1 + d]?.getD 0 = (off i.1 + (σ i.1)[d]).toUInt64 := by
      rw [hp, List.getElem?_toArray, List.getElem?_map, hFd, Option.map_some, Option.getD_some]
    have hσd := hσm i.1 i.2 _ (List.getElem_mem hdσ)
    have hpay : Vals.row (A := .long) pay ⟨off i.1 + d, hk⟩ = Int64.ofNat (σ i.1)[d] := by
      have es := (colMap_raw (colArr_ok hpay)).2.2.2 _ hk
      rw [colConst_raw hz, Array.getElem?_replicate, if_pos hk, Option.getD_some, (kgather_word hgp _ hk).2, hpk,
        toNat_toUInt64 (by omega), (hrun i.1 i.2 _ (by omega) (by omega)).2, Nat.add_sub_cancel_left] at es
      simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
      rw [Vals.row_atom, Arr.get_i64, ← es]; rfl
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos hk, hpay]
  · cases h

end Tab

end Rel
