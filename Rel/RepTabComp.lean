module

public import Rel.RepPack

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of `Tab.comp`'s blocks and the whole (`Rel/Run/Comp.lean`), after `Tab.pack` (`Rel/RepPack.lean`). -/

namespace Rel
open  Rel.Kernel Rel.Verify Enc

namespace Tab
variable {A B C : Obj}


/-- **`compBlocks` keeps `Tab.WF`**: each block by `compBlock_wf`, met by `∪` (`union_wf`). -/
theorem compBlocks_wf {R : Tab A B} {S : Tab B C} {nb : Nat} {bid : Arr .i64 R.n} {t : Tab A C}
    (h : compBlocks R S nb bid = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compBlocks, bind, Except.bind, ← Array.foldlM_toList, Array.toList_range] at h
  okSplit
  refine foldlM_keeps (P := Tab.WF) (fun b a b' hb hw => ?_) _ h (compBlock_wf ‹_› hR hS)
  split at hb; · cases hb
  rename_i P hP
  split at hb; · cases hb
  exact union_wf hb (pack_wf hP hw) (compBlock_wf ‹_› hR hS)

theorem compFrom_wf {bound : Nat} {R : Tab A B} {S : Tab B C} {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc}
    {t : Tab A C} (h : compFrom bound R S x = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compFrom, bind, Except.bind] at h
  okSplit
  all_goals first | exact compExpand_wf h hR hS | exact compBlocks_wf h hR hS

/-- **`R ≫ S` keeps `Tab.WF`** (`compOne_wf`, `compFrom_wf`). -/
theorem comp_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : R.comp S = .ok t) (hR : R.WF) (hS : S.WF) :
    t.WF := by
  simp only [Tab.comp, Tab.compWith, bind, Except.bind] at h
  okSplit
  all_goals first | exact compOne_wf h hR hS | exact compFrom_wf h hR hS

/-- A `∪` fold of the tables `f j` from `acc`, each `Tab.WF`: every `f j` answers, it holds what `acc` or some `f j`
holds, and past the first step it is a `canon`. The accumulator is `pack`ed before each `∪` (`compBlocks`). -/
theorem foldlM_union {k v : Obj} {f : Nat → Except String (Tab k v)} (hf : ∀ j X, f j = .ok X → X.WF) :
    ∀ (L : List Nat) (acc T : Tab k v), L.foldlM (fun acc j => do (← acc.pack).union (← f j)) acc = .ok T → acc.WF →
      (∀ j ∈ L, ∃ X, f j = .ok X) ∧ (L = [] → T = acc) ∧ (L ≠ [] → ∃ U : Tab k v, U.canon = .ok T ∧ U.WF) ∧
      ∀ a b, T.Holds a b ↔ acc.Holds a b ∨ ∃ j ∈ L, ∃ X, f j = .ok X ∧ X.Holds a b
  | [], acc, T, h, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | j :: L, acc, T, h, hacc => by
    rw [List.foldlM_cons] at h; simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨acc', h1, h2⟩ := h
    rw [Except.bind_eq_ok'] at h1; obtain ⟨P, hP, h1⟩ := h1
    rw [Except.bind_eq_ok'] at h1; obtain ⟨X, hX, hu⟩ := h1
    have hXw := hf j X hX
    have hPw := pack_wf hP hacc
    obtain ⟨hL, h0, hc, hH⟩ := foldlM_union hf L acc' T h2 (union_wf hu hPw hXw)
    refine ⟨fun i hi => ?_, by simp, fun _ => ?_, fun a b => ?_⟩
    · rcases List.mem_cons.1 hi with rfl | hi
      · exact ⟨X, hX⟩
      · exact hL i hi
    · by_cases hL0 : L = []
      · obtain rfl := h0 hL0; obtain ⟨C, hCc, hC⟩ := union_sorted hu; exact ⟨C, hC, concat_wf hCc hPw hXw⟩
      · exact hc hL0
    · rw [hH, union_holds hu hPw hXw, pack_holds hP hacc]; constructor
      · rintro ((h | h) | ⟨i, hi, Y, hY, h⟩)
        · exact .inl h
        · exact .inr ⟨j, by simp, X, hX, h⟩
        · exact .inr ⟨i, by simp [hi], Y, hY, h⟩
      · rintro (h | ⟨i, hi, Y, hY, h⟩)
        · exact .inl (.inl h)
        · rcases List.mem_cons.1 hi with rfl | hi
          · rw [hX] at hY; cases hY; exact .inl (.inr h)
          · exact .inr ⟨i, hi, Y, hY, h⟩

/-- **Block `j` denotes `R ≫ S` from the rows of `R` whose word in `c` is `j`.** -/
theorem compBlock_holds {R : Tab A B} {S : Tab B C} {c : Enc} {j : Nat} {X : Tab A C}
    (h : compBlock R S c j = .ok X) (hR : R.WF) (hS : S.WF) (a : A.El) (d : C.El) :
    X.Holds a d ↔ ∃ b, (∃ i : Fin R.n.toNat, (raw .i64 R.n c)[i.1]?.getD 0 = j.toUInt64 ∧ R.key.row i = a ∧
      R.val.row i = b) ∧ S.Holds b d := by
  unfold compBlock at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨m, hm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Rj, hRj, h⟩ := h
  have hmi : ∀ i < R.n.toNat, (raw .i64 R.n m)[i]?.getD 0 =
      if (raw .i64 R.n c)[i]?.getD 0 = j.toUInt64 then 1 else 0 := fun i hi => by
    have e1 := (colMap_post hm).2 i hi
    have e2 : Op.eval .eq j.toUInt64 ((raw .i64 R.n c)[i]?.getD 0) =
        .ok (if (raw .i64 R.n c)[i]?.getD 0 = j.toUInt64 then 1 else 0) := by
      show Except.ok (if (j.toUInt64 == (raw .i64 R.n c)[i]?.getD 0) = true then 1 else 0) = _
      by_cases hq : (raw .i64 R.n c)[i]?.getD 0 = j.toUInt64
      · simp [hq]
      · simp [hq, Ne.symm hq]
    rw [e2] at e1; exact (Except.ok.inj e1).symm
  obtain ⟨U, hU, hUw, hH⟩ := compOne_canon h (keep_wf hRj hR) hS
  rw [canon_holds hU hUw, hH]
  refine exists_congr fun b => and_congr_left fun _ => ?_
  rw [keep_holds hRj (fun i hi => by rw [hmi i hi]; split <;> decide)]
  refine exists_congr fun i => and_congr_left fun _ => ?_
  rw [hmi i.1 i.2]; split <;> simp_all

/-- **`compBlocks` denotes `R ≫ S` and is a `canon`**, whatever the block words `bid`: clamped into `[0, nb - 1]`,
every row of `R` is in one block, and every block is in the `∪`. -/
theorem compBlocks_canon {R : Tab A B} {S : Tab B C} {nb : Nat} {bid : Arr .i64 R.n} {T : Tab A C}
    (h : compBlocks R S nb bid = .ok T) (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ U.WF ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  unfold compBlocks at h
  split at h; · cases h
  rename_i hnb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T0, h0, h⟩ := h
  rw [← Array.foldlM_toList, Array.toList_range] at h
  obtain ⟨hL, hnil, hcan, hH⟩ := foldlM_union (f := fun j => compBlock R S c.enc (j + 1))
    (fun _ _ hX => compBlock_wf hX hR hS) _ _ _ h (compBlock_wf h0 hR hS)
  -- each row's clamped word is a block `j ≤ nb - 1`
  have hj : ∀ i : Fin R.n.toNat, ∃ j ≤ nb - 1, (raw .i64 R.n c.enc)[i.1]?.getD 0 = j.toUInt64 := fun i => by
    have e := Arr.clampShift_get (by simp; omega) hc i
    rw [Arr.get_i64 c] at e
    have h00 : ((0 : UInt64).toNat : Int) = 0 := rfl
    rw [h00, Int.add_zero] at e
    have hn := toInt64_nonneg (x := (raw .i64 R.n c.enc)[i.1]?.getD 0) (by rw [e]; omega)
    refine ⟨((raw .i64 R.n c.enc)[i.1]?.getD 0).toNat, ?_, by simp⟩
    have : ((nb - 1).toUInt64.toNat : Int) = (nb - 1 : Nat) := by rw [toNat_toUInt64 (by omega)]
    omega
  have hT : ∀ a d, T.Holds a d ↔ ∃ b, R.Holds a b ∧ S.Holds b d := fun a d => by
    rw [hH, compBlock_holds h0 hR hS]; constructor
    · rintro (⟨b, ⟨i, -, h1, h2⟩, hs⟩ | ⟨j, -, X, hX, hx⟩)
      · exact ⟨b, ⟨i, h1, h2⟩, hs⟩
      · obtain ⟨b, ⟨i, -, h1, h2⟩, hs⟩ := (compBlock_holds hX hR hS a d).1 hx; exact ⟨b, ⟨i, h1, h2⟩, hs⟩
    · rintro ⟨b, ⟨i, h1, h2⟩, hs⟩
      obtain ⟨j, hjn, hji⟩ := hj i
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact .inl ⟨b, ⟨i, hji, h1, h2⟩, hs⟩
      · have hmem : j - 1 ∈ List.range (nb - 1) := List.mem_range.2 (by omega)
        obtain ⟨X, hX⟩ := hL _ hmem
        refine .inr ⟨j - 1, hmem, X, hX, (compBlock_holds hX hR hS a d).2 ⟨b, ⟨i, ?_, h1, h2⟩, hs⟩⟩
        rw [hji, Nat.sub_add_cancel hpos]
  by_cases hL0 : List.range (nb - 1) = []
  · obtain rfl := hnil hL0
    have h0' := h0; unfold compBlock at h0'; simp only [bind] at h0'
    rw [Except.bind_eq_ok'] at h0'; obtain ⟨_, -, h0'⟩ := h0'
    rw [Except.bind_eq_ok'] at h0'; obtain ⟨_, hk0, h0'⟩ := h0'
    obtain ⟨U, hU, hUw, -⟩ := compOne_canon h0' (keep_wf hk0 hR) hS
    exact ⟨U, hU, hUw, fun a d => by rw [← hT, canon_holds hU hUw]⟩
  · obtain ⟨U, hU, hUw⟩ := hcan hL0
    exact ⟨U, hU, hUw, fun a d => by rw [← hT, canon_holds hU hUw]⟩

/-- **`R.compWith bound S` is `canon` of a table denoting `R ≫ S`**, at every `bound`; `Tab.comp` is `bound =
blockRows`. -/
theorem compFrom_canon {bound : Nat} {R : Tab A B} {S : Tab B C}
    {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc} {T : Tab A C} (hx : compGroups R S = .ok x)
    (h : compFrom bound R S x = .ok T) (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ U.WF ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  simp only [compFrom, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, -, h⟩ := h
  rcases o with _ | ⟨nb, bid⟩
  · exact compOne_canon (by rw [compOne, hx]; exact h) hR hS
  · exact compBlocks_canon h hR hS

theorem comp_canon {bound : Nat} {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : compWith bound R S = .ok T)
    (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ U.WF ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  unfold compWith at h
  split at h
  · exact compOne_canon h hR hS
  · simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
    exact compFrom_canon hx h hR hS

/-- **`R.comp S` denotes `R ≫ S`** (`Rep.rep_comp`'s statement, pointwise). -/
theorem comp_holds {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : R.comp S = .ok T) (hR : R.WF) (hS : S.WF)
    (a : A.El) (c : C.El) :
    T.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  obtain ⟨U, hU, hUw, hH⟩ := comp_canon h hR hS; rw [canon_holds hU hUw]; exact hH a c

/-- **`R.conv` denotes `R°`** (`Rep.rep_conv`'s statement, pointwise). -/
theorem conv_holds {R : Tab A B} {S : Tab B A} (h : R.conv = .ok S) (hR : R.WF) (b : B.El) (a : A.El) :
    S.Holds b a ↔ R.Holds a b := by
  rw [canon_holds h ⟨hR.2, hR.1⟩]; exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

end Tab

/-! ## Checks on `foR` tables -/



end Rel
