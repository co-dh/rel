import Rel.Kernel.Db.Csv

/-! The CSV round trip (IO design C.6): whatever `csvText` accepts, `csvWords` reads back word for word. It holds with
no exception because the writer refuses what text cannot hold: `cell` writes a word only if its text reads back as
it. The records part is proved over the lexer: a written record is lexed back as its fields, quoted or not. -/

namespace Rel.Db.Csv

theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem lex_plain (all r : List UInt8) (c : UInt8) (p : Nat) (fld row st acc) (h : special c = false) :
    lex all (c :: r) .plain p fld row st acc = lex all r .plain (p + 1) (fld ++ [c]) row st acc := by
  simp only [special, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := h
  simp [lex, h1, h2, h4]

/-- An unquoted field is lexed byte by byte. -/
theorem lex_unquoted (all rest : List UInt8) : ∀ (f : List UInt8) (p : Nat) fld row st acc, f.any special = false →
    ∃ p', lex all (f ++ rest) .plain p fld row st acc = lex all rest .plain p' (fld ++ f) row st acc
  | [], p, fld, row, st, acc, _ => ⟨p, by simp⟩
  | c :: f, p, fld, row, st, acc, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    obtain ⟨p', hp⟩ := lex_unquoted all rest f (p + 1) (fld ++ [c]) row st acc h.2
    exact ⟨p', by rw [List.cons_append, lex_plain _ _ _ _ _ _ _ _ h.1, hp]; simp⟩

/-- A quoted field's inside, `"` doubled, and its closing `"`. -/
theorem lex_quoted (all rest : List UInt8) (o : Nat) (hr : rest.head? ≠ some 34) :
    ∀ (f : List UInt8) (p : Nat) fld row st acc,
    ∃ p', lex all (f.flatMap quote ++ 34 :: rest) (.quoted o) p fld row st acc = lex all rest .closed p' (fld ++ f) row st acc
  | [], p, fld, row, st, acc => by
    cases rest with
    | nil => exact ⟨p + 1, by simp [lex]⟩
    | cons d r =>
      have : d ≠ 34 := by simpa using hr
      exact ⟨p + 1, by simp [lex, this]⟩
  | c :: f, p, fld, row, st, acc => by
    by_cases hc : c = 34
    · subst hc
      obtain ⟨p', hp⟩ := lex_quoted all rest o hr f (p + 2) (fld ++ [34]) row st acc
      exact ⟨p', by simp [quote, lex, hp]⟩
    · obtain ⟨p', hp⟩ := lex_quoted all rest o hr f (p + 1) (fld ++ [c]) row st acc
      refine ⟨p', ?_⟩
      simp only [List.flatMap_cons, quote, if_neg hc, List.cons_append, List.nil_append]
      rw [lex.eq_def]
      simp [hc, hp]

/-- A written field is lexed back as itself; after it the lexer is in a field's end state. -/
theorem lex_field (all rest : List UInt8) (hr : rest.head? ≠ some 34) (f : List UInt8) (p : Nat) (row st acc) :
    ∃ p', lex all (field f ++ rest) .plain p [] row st acc =
      lex all rest (if f.any special then .closed else .plain) p' f row st acc := by
  unfold field
  by_cases hs : f.any special = true
  · obtain ⟨p', hp⟩ := lex_quoted all rest p hr f (p + 1) [] row st acc
    refine ⟨p', ?_⟩
    simp only [hs, if_true, List.cons_append, List.append_assoc]
    simpa [lex] using hp
  · simp only [Bool.not_eq_true] at hs
    obtain ⟨p', hp⟩ := lex_unquoted all rest f p [] row st acc hs
    exact ⟨p', by simpa [hs] using hp⟩

theorem lex_comma (all r f : List UInt8) (p : Nat) (row st acc) :
    lex all (44 :: r) (if f.any special then .closed else .plain) p f row st acc =
      lex all r .plain (p + 1) [] (row ++ [f]) st acc := by
  split <;> simp [lex]

theorem lex_newline (all r f : List UInt8) (p : Nat) (row st acc) :
    lex all (10 :: r) (if f.any special then .closed else .plain) p f row st acc =
      lex all r .plain (p + 1) [] [] (p + 1) (acc ++ [(st, row ++ [f])]) := by
  split
  · simp [lex]
  · rename_i h
    have : f.getLast? ≠ some 13 := fun h13 => by
      have := List.any_eq_false.mp (Bool.not_eq_true _ ▸ h) 13 (List.mem_of_getLast? h13)
      simp [special] at this
    simp [lex, this]

/-- A written record and its `\n` are lexed back as its fields. -/
theorem lex_record (all rest : List UInt8) : ∀ (fs : List (List UInt8)), fs ≠ [] → ∀ (p : Nat) row st acc,
    ∃ p', lex all (record fs ++ 10 :: rest) .plain p [] row st acc =
      lex all rest .plain p' [] [] p' (acc ++ [(st, row ++ fs)])
  | [], h, _, _, _, _ => absurd rfl h
  | [f], _, p, row, st, acc => by
    obtain ⟨p1, h1⟩ := lex_field all (10 :: rest) (by simp) f p row st acc
    exact ⟨p1 + 1, by simp only [record]; rw [h1, lex_newline]⟩
  | f :: g :: fs, _, p, row, st, acc => by
    obtain ⟨p1, h1⟩ := lex_field all (44 :: (record (g :: fs) ++ 10 :: rest)) (by simp) f p row st acc
    obtain ⟨p2, h2⟩ := lex_record all rest (g :: fs) (by simp) (p1 + 1) (row ++ [f]) st acc
    exact ⟨p2, by simp only [record, List.append_assoc, List.cons_append]; rw [h1, lex_comma, h2]; simp⟩

/-- Written records are lexed back as their fields. -/
theorem lex_records (all : List UInt8) : ∀ (rs : List (List (List UInt8))), (∀ r ∈ rs, r ≠ []) → ∀ (p : Nat) acc,
    ∃ out, lex all (records rs) .plain p [] [] p acc = .ok out ∧ out.map (·.2) = acc.map (·.2) ++ rs
  | [], _, p, acc => ⟨acc, by simp [records, lex], by simp⟩
  | r :: rs, h, p, acc => by
    obtain ⟨p', h1⟩ := lex_record all (records rs) r (h r (by simp)) p [] p acc
    obtain ⟨out, h2, h3⟩ := lex_records all rs (fun x hx => h x (by simp [hx])) p' (acc ++ [(p, [] ++ r)])
    have : records (r :: rs) = record r ++ 10 :: records rs := by simp [records]
    exact ⟨out, by rw [this, h1, h2], by simp [h3]⟩

/-- A written cell reads back as its word. -/
theorem cell_read {c : QAtomicType × List String} {w : UInt64} {s : List UInt8} (h : cell c w = some s) :
    readCell c s = some w := by
  simp only [cell, Option.bind_eq_some_iff] at h
  obtain ⟨s', _, h⟩ := h
  split at h
  · cases h; assumption
  · cases h

theorem getCell_putCell {r r' l : Nat} {x : String × QAtomicType × List String} {a : Array UInt64} {s : List UInt8}
    (h : putCell r (x, a) = .ok s) : getCell r' l (x, s) = .ok (a.getD r 0) := by
  obtain ⟨c, t, ns⟩ := x
  simp only [putCell] at h
  split at h
  · rename_i s' hs
    cases h
    simp [getCell, cell_read hs]
  · cases h

/-- A written row reads back as its words. -/
theorem mapM_getCell (r r' l : Nat) : ∀ (cols : CsvCols) (ws : List (Array UInt64)) (fs : List (List UInt8)),
    ws.length = cols.length → (cols.zip ws).mapM (putCell r) = .ok fs →
    fs.length = cols.length ∧ (cols.zip fs).mapM (getCell r' l) = .ok (ws.map (·.getD r 0))
  | [], ws, fs, hl, h => by
    simp at hl; subst hl
    simp only [List.zip_nil_right, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [pure, Except.pure]
  | x :: cols, [], fs, hl, _ => by simp at hl
  | x :: cols, a :: ws, fs, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, ok_bind] at h
    obtain ⟨s, hs, fs', hfs, h⟩ := h
    cases h
    obtain ⟨h1, h2⟩ := mapM_getCell r r' l cols ws fs' (by simpa using hl) hfs
    refine ⟨by simp [h1], ?_⟩
    simp [List.mapM_cons, getCell_putCell hs, h2, bind, Except.bind, pure, Except.pure]

/-- Written rows read back as their words, whatever the records' first bytes. -/
theorem rows_back (cols : CsvCols) (ws : List (Array UInt64)) (hl : ws.length = cols.length) (all : List UInt8) :
    ∀ (n s : Nat) (rs : List (List (List UInt8))), (List.range' s n).mapM (fun r => (cols.zip ws).mapM (putCell r)) = .ok rs →
    rs.length = n ∧ (∀ f ∈ rs, f.length = cols.length) ∧ ∀ (tail : List (Nat × List (List UInt8))) (r0 : Nat),
      tail.map (·.2) = rs → rows cols all r0 tail = .ok ((List.range' s n).map fun i => ws.map (·.getD i 0))
  | 0, s, rs, h => by
    simp only [List.range'_zero, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨rfl, by simp, fun tail r0 ht => ?_⟩
    simp at ht; subst ht; simp [rows]
  | n + 1, s, rs, h => by
    simp only [List.range'_succ, List.mapM_cons, ok_bind] at h
    obtain ⟨fs, hfs, rs', hrs, h⟩ := h
    cases h
    obtain ⟨hlen, hall, hrows⟩ := rows_back cols ws hl all n (s + 1) rs' hrs
    refine ⟨by simp [hlen], ?_, fun tail r0 ht => ?_⟩
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with hf | hf
      · rw [hf]; exact (mapM_getCell s 0 0 cols ws fs hl hfs).1
      · exact hall f hf
    · cases tail with
      | nil => simp at ht
      | cons pf tail =>
        obtain ⟨p, f⟩ := pf
        simp only [List.map_cons, List.cons.injEq] at ht
        obtain ⟨rfl, ht⟩ := ht
        obtain ⟨h1, h2⟩ := mapM_getCell s r0 (lineAt all p) cols ws f hl hfs
        simp [rows, row, h1, h2, hrows tail (r0 + 1) ht, bind, Except.bind, pure, Except.pure, List.range'_succ]

theorem forM_ok {ε α : Type} {f : α → Except ε Unit} : ∀ {xs : List α} {u : Unit}, xs.forM f = .ok u →
    ∀ x ∈ xs, f x = .ok ()
  | [], _, _ => by simp
  | x :: xs, u, h => by
    unfold List.forM at h
    obtain ⟨u', h1, h2⟩ := ok_bind.mp h
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact h1
    · exact forM_ok h2 y hy

end Rel.Db.Csv

open Rel.Db.Csv in
/-- **Read after write is the identity** (IO design C.6), on the models of `qlean_csv_read` and `qlean_csv_write`:
whatever the writer accepts, the reader gives back, row count and every column word for word. No hypothesis: the
writer refuses what text cannot hold (`cell`). -/
theorem Rel.Db.csvWords_csvText {cols : Rel.Db.CsvCols} {n : Nat} {ws : List (Array UInt64)} {b : List UInt8}
    (h : Rel.Db.csvText cols n ws = .ok b) : Rel.Db.csvWords cols b = .ok (n, ws) := by
  simp only [Rel.Db.csvText, ok_bind] at h
  obtain ⟨u, hs, u2, hl, u3, hsz, rs, hrs, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  have hl : ws.length = cols.length := by split at hl <;> simp_all
  have hne : cols ≠ [] := by intro h0; simp [schema, h0] at hs
  rw [List.range_eq_range'] at hrs
  obtain ⟨hlen, hall, hrows⟩ := rows_back cols ws hl (records (cols.map (bytes ·.1) :: rs)) n 0 rs hrs
  obtain ⟨out, hlex, hout⟩ := lex_records (records (cols.map (bytes ·.1) :: rs)) (cols.map (bytes ·.1) :: rs)
    (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simpa using hne
      · intro h0; have := hall r hr; simp [h0] at this; exact hne (List.length_eq_zero_iff.mp this.symm))
    0 []
  cases out with
  | nil => simp at hout
  | cons ph tail =>
    simp only [List.map_nil, List.nil_append, List.map_cons, List.cons.injEq] at hout
    obtain ⟨hh, ht⟩ := hout
    have hsz' : ∀ c (hc : c < ws.length), ws[c].size = n := by
      intro c hc
      have := forM_ok hsz (cols[c]'(hl ▸ hc), ws[c]) (by
        rw [List.mem_iff_getElem]; exact ⟨c, by simp [hl] at hc ⊢; omega, by simp⟩)
      simpa using this
    have hlt : tail.length = n := by rw [← List.length_map (f := (·.2)), ht, hlen]
    simp only [Rel.Db.csvWords, hs, hlex, bind, Except.bind, List.head?_cons, Option.map_some, Option.getD_some,
      List.tail_cons, hrows tail 0 ht, pure, Except.pure, hh, header, if_true, hlt]
    congr 1
    refine Prod.ext (by simp) (List.ext_getElem (by simp [hl]) fun c h1 h2 => ?_)
    simp only [List.getElem_map, List.getElem_range, List.map_map]
    rw [← Array.toArray_toList (xs := ws[c])]
    congr 1
    refine List.ext_getElem (by simp [hsz' c h2]) fun i i1 i2 => ?_
    have hc : c < ws.length := by simpa using h2
    have hi : i < ws[c].size := by simpa using i2
    simp [List.getElem_range', List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hc,
      Array.getElem?_eq_getElem hi]
