module

public import Rel.RepCanon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `kasc ≫ kseen` (PLAN D.12): `kseen` answers only rows in `kasc` order (`kseen_sorted`), and `kasc`'s sorted
columns are such rows, so the composition never takes `kseen`'s error (`kasc_kseen`). Its answer is `kseen_ok`'s over
the sorted rows, whose key at `q` is input row `ps[q]`'s (`kasc_grade`), and its groups are runs (`kseen_runs`). -/

namespace Rel
open  Rel.Kernel Rel.Verify

/-- `lexLe` reads two rows only through their codes: rows `i`, `j` of `ks` with the codes of rows `i'`, `j'` of `ks'`
compare as those do. -/
theorem lexLe_congr : ∀ {ks ks' : List (Array UInt64)} {i j i' j' : Nat},
    ks.map (·[i]?.getD 0) = ks'.map (·[i']?.getD 0) → ks.map (·[j]?.getD 0) = ks'.map (·[j']?.getD 0) →
    lexLe ks i j = lexLe ks' i' j'
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _, _, _, _, hi, hj => by
    simp only [List.map_cons, List.cons.injEq] at hi hj
    simp only [lexLe, hi.1, hj.1, lexLe_congr hi.2 hj.2]

theorem mapM_ok_of {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ r, l.mapM f = .ok r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨r, hr⟩ := mapM_ok_of (l := l) fun a ha => h a (List.mem_cons_of_mem _ ha)
    exact ⟨b :: r, by simp [List.mapM_cons, hb, hr, bind, Except.bind, pure, Except.pure]⟩

/-- **A key column reads again after a sort**: where `ascCol` reads `c`, it reads `c`'s key over words `ws` of its row
count, each one of `c`'s words, since only a `cells` key reads the words themselves, to check each names a cell. -/
theorem ascCol_perm {m : USize} {c : AscKey × Enc} {x : Array UInt64} {k : List (Array UInt64)}
    (h : ascCol m c = .ok (x, k)) {ws : Array UInt64} (hws : m.toNat = ws.size) (hw : ∀ a ∈ ws, a ∈ x) :
    ∃ r, ascCol m (c.1, wordsFoR ws) = .ok r := by
  have hfo : ∀ w, foRWords w m (wordsFoR ws) = .ok ws := fun w => by
    rw [(foRWords_valid w m _).1 (wordsFoR_closed ws hws).1, (wordsFoR_closed ws hws).2.1]
  obtain ⟨c, e⟩ := c
  cases c with
  | atom t =>
    obtain ⟨f, hf⟩ := (ascCol_ok h).2.2.2 t rfl
    have hw' : ascWords m (t, wordsFoR ws) = .ok ws := by
      rw [← hfo "asc"]; cases t <;> rfl
    exact ⟨_, by simp only [ascCol, hf, hw']; rfl⟩
  | cells n c lo hi els =>
    simp only [ascCol, bind, Except.bind] at h ⊢
    split at h; · cases h
    rename_i ix hix
    have hx := (ascCol_ok (m := m) (c := (.cells n c lo hi els, e)) (by
      simp only [ascCol, bind, Except.bind, hix]; exact h)).1
    rw [← (foRWords_raw _ _ _ _ hix).1] at hx
    split at h; · cases h
    split at h; · cases h
    rename_i hnone
    have hfind : ws.find? (fun x => decide (n.toNat ≤ x.toNat)) = none :=
      Array.find?_eq_none.2 fun a ha => Array.find?_eq_none.1 hnone a (hx ▸ hw a ha)
    have hnn : noNul "asc: cells" m (wordsFoR ws) = .ok () := by simp [noNul, hasNul_wordsFoR]
    simp only [hfo, hnn, hfind]
    revert h
    cases foRWords "asc: cells lo" n lo <;> cases noNul "asc: cells lo" n lo <;> cases foRWords "asc: cells hi" n hi <;>
      cases noNul "asc: cells hi" n hi <;> cases ascCodes c els <;> intro h <;> first | exact ⟨_, rfl⟩ | cases h

/-- **`kasc ≫ kseen` answers**: over `kasc`'s sorted columns `vs`, keyed as `es`, `kseen` takes neither error: each
column reads again (`ascCol_perm`) and the rows are in `kasc` order (`ascGrade_spec` through `kasc_grade`). What it
answers is `kseen_ok`'s, the groups `Order.groupIn` numbers over the sorted rows' keys, row `q`'s key being input row
`ps[q]`'s (`kasc_grade`). -/
theorem kasc_kseen {n : USize} {es : List (AscKey × Enc)} {vs : List Enc} {p : Enc} (ha : kasc n es = .ok (vs, p))
    (hwf : ∀ x ∈ es, ∃ t, Enc.WF t n x.2) (hpl : ∀ x ∈ es, hasNul x.2 = false) :
    ∃ r, kseen n ((es.map (·.1)).zip vs) = .ok r := by
  obtain ⟨ps, -, hperm, hvl, hcol⟩ := asc_perm n es vs p ha
  obtain ⟨cs, hc, -⟩ := kasc_ok ha
  obtain ⟨-, -, -, hkey⟩ := kasc_grade ha hwf
  obtain ⟨hlc, hf⟩ := mapM_ok hc
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hread : ∀ c ∈ (es.map (·.1)).zip vs, ∃ r, ascCol n c = .ok r := fun c hc' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have hie : i < es.length := by simp at hi; omega
    have hic : i < cs.length := by omega
    obtain ⟨ws, nul, hv, hws, hwq, hnul, -⟩ := hcol i es[i] (vs[i]'(by omega)) (List.getElem?_eq_getElem hie)
      (List.getElem?_eq_getElem _)
    obtain rfl := hnul (hpl _ (List.getElem_mem hie))
    have h0 := hf i es[i] cs[i] (List.getElem?_eq_getElem hie) (List.getElem?_eq_getElem hic)
    have hx := (ascCol_ok h0).1
    simp only [List.getElem_zip, List.getElem_map, hv]
    refine ascCol_perm h0 hws.symm fun a ha => ?_
    obtain ⟨q, hq, rfl⟩ := Array.getElem_of_mem ha
    have e := hwq q (by omega)
    rw [Array.getElem?_eq_getElem hq, ← hx] at e
    exact Array.mem_of_getElem? e.symm
  obtain ⟨kss, hkss⟩ := mapM_ok_of (f := fun (c, i) => (fun x : Array UInt64 × List (Array UInt64) => x.2) <$>
    (ascCol n c).mapError (s!"seen: es[{i}]: " ++ ·)) (l := ((es.map (·.1)).zip vs).zipIdx) fun ci hci => by
    obtain ⟨r, hr⟩ := hread ci.1 (List.fst_mem_of_mem_zipIdx hci)
    exact ⟨r.2, by simp [hr, Functor.map, Except.map, Except.mapError]⟩
  have hflat := kseen_keys hkss
  obtain ⟨-, hsort⟩ := ascGrade_spec n.toNat (ascKeys n es)
  have hgl : (ascGrade n.toNat (ascKeys n es)).length = n.toNat := by
    simpa using (ascGrade_spec n.toNat (ascKeys n es)).1.length_eq
  have hnone : (List.range (n.toNat - 1)).find? (fun i => !lexLe kss.flatten i (i + 1)) = none :=
    List.find?_eq_none.2 fun i hi => by
      have hi := List.mem_range.1 hi
      rw [hflat, lexLe_congr (hkey i (by omega)) (hkey (i + 1) (by omega))]
      simpa using (List.pairwise_iff_getElem.1 hsort i (i + 1) (by omega) (by omega) (by omega)).1
  unfold kseen
  simp only [bind, Except.bind, hkss, hnone]
  exact ⟨_, rfl⟩

end Rel
