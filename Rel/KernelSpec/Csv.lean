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

end Rel.Db.Csv
