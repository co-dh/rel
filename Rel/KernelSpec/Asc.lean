import Rel.Kernel.Asc
import Rel.KernelSpec.Scatter
import Rel.KernelSpec.Search

/-! `asc`'s laws (design §4, `asc_sorted` and `asc_perm`), on the words `Enc.raw` reads from its arguments: the
permutation is a stable lexicographic sort of the rows by their order codes, and each answer column is its input
column read through the permutation. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

theorem lexLe_total : ∀ (ks : List (Array UInt64)) (i j : Nat), (lexLe ks i j || lexLe ks j i) = true
  | [], _, _ => rfl
  | c :: cs, i, j => by
    have ih := lexLe_total cs i j
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.lt_iff_toNat_lt,
      ← UInt64.toNat_inj] at ih ⊢
    rcases ih with ih | ih <;> rcases Nat.lt_trichotomy (c[i]?.getD 0).toNat (c[j]?.getD 0).toNat with h | h | h <;>
      simp_all

theorem lexLe_trans : ∀ (ks : List (Array UInt64)) (i j k : Nat), lexLe ks i j = true → lexLe ks j k = true →
    lexLe ks i k = true
  | [], _, _, _, _, _ => rfl
  | c :: cs, i, j, k, h1, h2 => by
    have ih := lexLe_trans cs i j k
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.lt_iff_toNat_lt,
      ← UInt64.toNat_inj] at h1 h2 ⊢
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr ⟨by omega, ih h1 h2⟩

theorem ascIns_perm (le : Nat → Nat → Bool) (x : Nat) : ∀ l : List Nat, (ascIns le x l).Perm (x :: l)
  | [] => .refl _
  | y :: ys => by
    unfold ascIns
    split
    · exact ((ascIns_perm le x ys).cons y).trans (.swap x y ys)
    · exact .refl _

/-- Inserting an index above every one present keeps a stable order: `le` first, ties by index. -/
theorem ascIns_pairwise {le : Nat → Nat → Bool} (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (x : Nat) :
    ∀ l : List Nat, (∀ y ∈ l, y < x) → l.Pairwise (fun i j => le i j = true ∧ (le j i = true → i < j)) →
      (ascIns le x l).Pairwise (fun i j => le i j = true ∧ (le j i = true → i < j))
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hx, hp => by
    rw [List.pairwise_cons] at hp
    unfold ascIns
    split
    · rename_i hyx
      refine List.pairwise_cons.2 ⟨fun z hz => ?_,
        ascIns_pairwise trans total x ys (fun z hz => hx z (.tail _ hz)) hp.2⟩
      rcases List.mem_cons.1 ((ascIns_perm le x ys).mem_iff.1 hz) with rfl | hz
      · exact ⟨hyx, fun _ => hx _ (.head _)⟩
      · exact hp.1 z hz
    · rename_i hyx
      have hxy : le x y = true := by have := total x y; cases h : le y x <;> simp_all
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 hp⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hxy, fun h => absurd h hyx⟩
      · obtain ⟨hyz, _⟩ := hp.1 z hz
        exact ⟨trans _ _ _ hxy hyz, fun h => absurd (trans _ _ _ hyz h) hyx⟩

/-- The sort phase answers a permutation of `til m`, ordered by `lexLe ks` with ties in index order. -/
theorem ascGrade_spec (m : Nat) (ks : List (Array UInt64)) :
    (ascGrade m ks).Perm (List.range m) ∧
      (ascGrade m ks).Pairwise fun i j => lexLe ks i j = true ∧ (lexLe ks j i = true → i < j) := by
  induction m with
  | zero => exact ⟨by simp [ascGrade], by simp [ascGrade]⟩
  | succ m ih =>
    unfold ascGrade at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hp, hs⟩ := ih
    exact ⟨((ascIns_perm _ m _).trans (hp.cons m)).trans (List.perm_append_singleton m (List.range m)).symm,
      ascIns_pairwise (lexLe_trans ks) (lexLe_total ks) m _ (fun y hy => List.mem_range.1 (hp.mem_iff.1 hy)) hs⟩

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      r.length = l.length ∧ ∀ (i : Nat) a b, l[i]? = some a → r[i]? = some b → f a = .ok b
  | [], r, h => by cases h; simp
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [ha, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hf⟩ := mapM_ok hl
        refine ⟨by simp [hlen], fun i a' b' h1 h2 => ?_⟩
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1 h2; exact ha
        | succ i => simp only [List.getElem?_cons_succ] at h1 h2; exact hf i a' b' h1 h2

/-- `ascWords` answers `foRWords`' words or an error. -/
theorem ascWords_foR {m : USize} {c : QAtomicType × Enc} {x : Array UInt64} (hw : ascWords m c = .ok x) :
    foRWords "asc" m c.2 = .ok x := by
  obtain ⟨t, e⟩ := c
  cases e <;> cases t <;> first | exact hw | cases hw | (simp only [ascWords] at hw; split at hw <;> first
    | exact hw | cases hw)

theorem ascCol_ok {m : USize} {c : QAtomicType × Enc} {x k : Array UInt64} (h : ascCol m c = .ok (x, k)) :
    x = raw .i64 m c.2 ∧ x.size = m.toNat ∧ ∃ f, ascOrd c.1 = some f ∧ k = x.map f := by
  unfold ascCol at h
  cases ho : ascOrd c.1 with
  | none => simp [ho] at h
  | some f =>
    cases hw : ascWords m c with
    | error s => simp [ho, hw, Functor.map, Except.map] at h
    | ok w =>
      simp only [ho, hw, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hk⟩ := h
      have hf : foRWords "asc" m c.2 = .ok x := hx ▸ ascWords_foR hw
      obtain ⟨rfl, hs⟩ := foRWords_raw _ _ _ _ hf
      exact ⟨rfl, hs, f, rfl, by rw [← hk, hx]⟩

/-- The order codes `kasc` sorts by: each column's words (`foRWords`) through its type's `ascOrd`. -/
def ascKeys (m : USize) (es : List (QAtomicType × Enc)) : List (Array UInt64) :=
  es.map fun e => (raw .i64 m e.2).map ((ascOrd e.1).getD id)

/-- `scatterWords` twice through a permutation `ps` of `til M`: `til M` through `ps` puts `k` at `ps[k]`, and `x`
through that puts `x[ps[k]]` at `k`. -/
theorem scatter_grade {M : Nat} (hM : M < 2 ^ 64) {ps : List Nat} (hp : ps.Perm (List.range M))
    {r x v : Array UInt64}
    (hr : scatterWords .last (ps.map Nat.toUInt64).toArray ((List.range M).map Nat.toUInt64).toArray M 0 = .ok r)
    (hx : x.size = M) (hv : scatterWords .last r x M 0 = .ok v) :
    v.size = M ∧ ∀ k (hk : k < ps.length), v[k]? = x[ps[k]]? := by
  have hnd : ps.Nodup := hp.nodup_iff.2 List.nodup_range
  have hlen : ps.length = M := by simpa using hp.length_eq
  have hlt : ∀ k (hk : k < ps.length), ps[k] < M := fun k hk => List.mem_range.1 (hp.mem_iff.1 (List.getElem_mem hk))
  have hcast : ∀ a, a < M → a.toUInt64.toNat = a := fun a ha => by simp; omega
  obtain ⟨-, hok1⟩ := scatterWords_spec (ps.map Nat.toUInt64).toArray ((List.range M).map Nat.toUInt64).toArray M 0
  obtain ⟨hrs, -, hlast1⟩ := hok1 r hr
  have hrk : ∀ k (hk : k < ps.length), r[ps[k]]? = some k.toUInt64 := by
    intro k hk
    have h1 := hlast1 k (by simpa using hk) fun k' hkk' hk' heq => by
      change ((ps.map Nat.toUInt64).toArray[k']?.getD 0).toNat = ((ps.map Nat.toUInt64).toArray[k]?.getD 0).toNat at heq
      have hk2 : k' < ps.length := by simpa using hk'
      simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hk2, List.getElem?_eq_getElem hk,
        Option.map_some, Option.getD_some, hcast _ (hlt _ hk2), hcast _ (hlt _ hk)] at heq
      exact List.pairwise_iff_getElem.1 hnd k k' hk hk2 hkk' heq.symm
    change r[((ps.map Nat.toUInt64).toArray[k]?.getD 0).toNat]? =
      some (((List.range M).map Nat.toUInt64).toArray[k]?.getD 0) at h1
    simpa [List.getElem?_eq_getElem hk, hcast _ (hlt _ hk), List.getElem?_range (show k < M by omega)] using h1
  obtain ⟨-, hok2⟩ := scatterWords_spec r x M 0
  obtain ⟨hvs, -, hlast2⟩ := hok2 v hv
  refine ⟨hvs, fun k hk => ?_⟩
  have hix : ∀ k (hk : k < ps.length), (r[ps[k]]?.getD 0).toNat = k := fun k hk => by
    rw [hrk k hk]; exact hcast _ (by omega)
  have h2 := hlast2 ps[k] (by rw [hrs]; exact hlt k hk) fun i' hi' hi'r heq => by
    obtain ⟨k', hk', rfl⟩ := List.mem_iff_getElem.1 (hp.mem_iff.2 (List.mem_range.2 (show i' < M by omega)))
    change (r[ps[k']]?.getD 0).toNat = (r[ps[k]]?.getD 0).toNat at heq
    rw [hix k' hk', hix k hk] at heq
    subst heq; omega
  change v[(r[ps[k]]?.getD 0).toNat]? = some (x[ps[k]]?.getD 0) at h2
  rw [hix k hk] at h2
  rw [Array.getElem?_eq_getElem (show ps[k] < x.size by rw [hx]; exact hlt k hk)] at h2 ⊢
  simpa using h2

/-- What `kasc` answers, unfolded: the key columns `cs`, the destinations `r` and the sorted words `wss`. -/
theorem kasc_ok {m : USize} {es : List (QAtomicType × Enc)} {vs : List Enc} {p : Enc} (h : kasc m es = .ok (vs, p)) :
    ∃ cs, es.mapM (ascCol m) = .ok cs ∧ ∃ r, scatterWords .last ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray
      ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 = .ok r ∧
      ∃ wss, cs.mapM (fun c => scatterWords .last r c.1 m.toNat 0) = .ok wss ∧ vs = wss.map wordsFoR ∧
        p = wordsFoR ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray := by
  unfold kasc at h
  cases hc : es.mapM (ascCol m) with
  | error s => simp [hc, bind, Except.bind] at h
  | ok cs =>
    cases hr : scatterWords .last ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray
        ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 with
    | error s => simp [hc, hr, bind, Except.bind] at h
    | ok r =>
      cases hw : cs.mapM (fun c => scatterWords .last r c.1 m.toNat 0) with
      | error s => simp [hc, hr, hw, bind, Except.bind] at h
      | ok wss =>
        simp only [hc, hr, hw, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨cs, rfl, r, hr, wss, hw, h.1.symm, h.2.symm⟩

/-- The key columns' codes are `ascKeys`. -/
theorem ascCol_keys {m : USize} {es : List (QAtomicType × Enc)} {cs} (hc : es.mapM (ascCol m) = .ok cs) :
    cs.map (·.2) = ascKeys m es := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  apply List.ext_getElem? fun i => ?_
  cases hci : cs[i]? with
  | none =>
    have : es[i]? = none := List.getElem?_eq_none_iff.2 (by rw [← hlen]; exact List.getElem?_eq_none_iff.1 hci)
    simp [ascKeys, hci, this]
  | some c =>
    cases hei : es[i]? with
    | none =>
      have h1 := List.getElem?_eq_none_iff.1 hei
      have h2 := (List.getElem?_eq_some_iff.1 hci).1
      omega
    | some e =>
      obtain ⟨hx, -, f, hof, hk⟩ := ascCol_ok (hf i e c hei hci)
      simp [ascKeys, hci, hei, hof, hk, hx]

/-- **`asc_sorted`** (design §4): the permutation `kasc` answers lists the rows ordered lexicographically by their
order codes (`ascKeys`), the first column the most significant, and **stably**: a row comes before a row whose codes
equal its own only when it came before it in the input. -/
theorem asc_sorted (m : USize) (es : List (QAtomicType × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m es = .ok (vs, p)) :
    ∃ ps : List Nat, p = wordsFoR (ps.map Nat.toUInt64).toArray ∧
      ps.Pairwise fun i j => lexLe (ascKeys m es) i j = true ∧ (lexLe (ascKeys m es) j i = true → i < j) := by
  obtain ⟨cs, hc, -, -, -, -, -, hp⟩ := kasc_ok h
  rw [ascCol_keys hc] at hp
  exact ⟨_, hp, (ascGrade_spec _ _).2⟩

/-- **`asc_perm`** (design §4): the permutation `kasc` answers is a permutation `ps` of `til m`, and the answer for each
key column `e` holds `m` words, word `k` being `e`'s raw word at row `ps[k]`. -/
theorem asc_perm (m : USize) (es : List (QAtomicType × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m es = .ok (vs, p)) :
    ∃ ps : List Nat, p = wordsFoR (ps.map Nat.toUInt64).toArray ∧ ps.Perm (List.range m.toNat) ∧
      vs.length = es.length ∧ ∀ (c : Nat) e v, es[c]? = some e → vs[c]? = some v →
        ∃ ws : Array UInt64, v = wordsFoR ws ∧ ws.size = m.toNat ∧
          ∀ k (hk : k < ps.length), ws[k]? = (raw .i64 m e.2)[ps[k]]? := by
  obtain ⟨cs, hc, r, hr, wss, hw, rfl, rfl⟩ := kasc_ok h
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  obtain ⟨wlen, wf⟩ := mapM_ok hw
  have hM : m.toNat < 2 ^ 64 := by have := m.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  have hperm := (ascGrade_spec m.toNat (cs.map (·.2))).1
  refine ⟨_, rfl, hperm, by simp [wlen, hlen], fun c e v hec hvc => ?_⟩
  simp only [List.getElem?_map] at hvc
  cases hwc : wss[c]? with
  | none => simp [hwc] at hvc
  | some ws =>
    simp only [hwc, Option.map_some, Option.some.injEq] at hvc
    subst hvc
    cases hcc : cs[c]? with
    | none =>
      have h1 := List.getElem?_eq_none_iff.1 hcc
      have h2 := (List.getElem?_eq_some_iff.1 hwc).1
      omega
    | some cc =>
      obtain ⟨hx, hxs, -⟩ := ascCol_ok (hf c e cc hec hcc)
      obtain ⟨hvs, hk⟩ := scatter_grade hM hperm hr hxs (wf c cc ws hcc hwc)
      exact ⟨ws, rfl, hvs, fun k hk' => by rw [hk k hk', hx]⟩

theorem mapM_append_ok {α β ε : Type} {f : α → Except ε β} {l1 l2 : List α} {r : List β}
    (h : (l1 ++ l2).mapM f = .ok r) : ∃ r1 r2, l1.mapM f = .ok r1 ∧ l2.mapM f = .ok r2 ∧ r = r1 ++ r2 := by
  rw [List.mapM_append] at h
  cases h1 : l1.mapM f with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    cases h2 : l2.mapM f with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨r1, r2, rfl, rfl, h.symm⟩

theorem lexLe_append (ks2 : List (Array UInt64)) (i j : Nat) (h : lexLe ks2 i j = true) :
    ∀ ks, lexLe (ks ++ ks2) i j = lexLe ks i j
  | [] => h
  | c :: cs => by simp only [List.cons_append, lexLe, lexLe_append ks2 i j h cs]

theorem ascIns_congr {le le' : Nat → Nat → Bool} {x : Nat} :
    ∀ l : List Nat, (∀ y ∈ l, le y x = le' y x) → ascIns le x l = ascIns le' x l
  | [], _ => rfl
  | y :: ys, h => by simp only [ascIns, h y (.head _), ascIns_congr ys fun z hz => h z (.tail _ hz)]

/-- Keys `ks2` that put every row no later than every later row decide nothing a stable sort by `ks` does not. -/
theorem ascGrade_append {m : Nat} {ks2 : List (Array UInt64)} (h : ∀ y x, y < x → x < m → lexLe ks2 y x = true)
    (ks : List (Array UInt64)) : ascGrade m (ks ++ ks2) = ascGrade m ks := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e := ih fun y x hyx hx => h y x hyx (by omega)
    have hmem := fun y (hy : y ∈ ascGrade m ks) => List.mem_range.1 ((ascGrade_spec m ks).1.mem_iff.1 hy)
    unfold ascGrade at e hmem ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_append, e]
    simp only [List.foldl_cons, List.foldl_nil]
    exact ascIns_congr _ fun y hy => lexLe_append _ _ _ (h y m (hmem y hy) (by omega)) ks

/-- A `pos` key below `2^63` rows puts every row before every later row: its order code at `i64` is `i + 2^63`. -/
theorem lexLe_pos {m : USize} (hm : m.toNat ≤ 2 ^ 63) (rest : List (QAtomicType × Enc)) {y x : Nat} (hyx : y < x)
    (hx : x < m.toNat) : lexLe (ascKeys m ((.i64, .pos) :: rest)) y x = true := by
  have hc : ∀ i, i < 2 ^ 63 → (ordKey 8 false true (UInt64.ofNat i)).toNat = i + 2 ^ 63 := fun i hi => by
    have := ordKey_signed (w := 8) (by omega) (by omega) (UInt64.ofNat i)
    simp only [sx, UInt64.toNat_ofNat'] at this
    split at this <;> omega
  have hpr : raw .i64 m (.pos : Enc) = (Array.range m.toNat).map UInt64.ofNat := rfl
  simp only [ascKeys, List.map_cons, lexLe, hpr, Array.getElem?_map, Array.getElem?_range,
    show y < m.toNat by omega, hx, if_true, Option.map_some, Option.getD_some, Bool.or_eq_true, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt]
  left
  show (ordKey 8 false true (UInt64.ofNat y)).toNat < (ordKey 8 false true (UInt64.ofNat x)).toNat
  rw [hc y (by omega), hc x (by omega)]; omega

/-- `ascCol` reads a `pos` column of at most `2^63` rows: past that it is `ascWords`' error. -/
theorem ascCol_pos {m : USize} {rest : List (QAtomicType × Enc)} {cs : List (Array UInt64 × Array UInt64)}
    (h : ((.i64, .pos) :: rest).mapM (ascCol m) = .ok cs) : m.toNat ≤ 2 ^ 63 := by
  rw [List.mapM_cons] at h
  refine Classical.byContradiction fun hm => ?_
  simp [ascCol, ascWords, ascOrd, ascLayout, orderKind, hm, bind, Except.bind, Functor.map, Except.map] at h

/-- **Law A1** (PLAN 6.13): a `pos` key column has no ties and is in row order (`ascWords` admits it only there), so it
and every later column decide nothing: `kasc` with them answers the permutation of `kasc` without them, and the same
leading columns. -/
theorem kasc_pos_key (m : USize) (ks rest : List (QAtomicType × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m (ks ++ (.i64, .pos) :: rest) = .ok (vs, p)) : kasc m ks = .ok (vs.take ks.length, p) := by
  obtain ⟨cs, hc, r, hr, wss, hw, rfl, rfl⟩ := kasc_ok h
  obtain ⟨cs1, cs2, hc1, hc2, rfl⟩ := mapM_append_ok hc
  have hm := ascCol_pos hc2
  have hg : ascGrade m.toNat ((cs1 ++ cs2).map (·.2)) = ascGrade m.toNat (cs1.map (·.2)) := by
    rw [List.map_append, ascCol_keys hc2]
    exact ascGrade_append (fun y x hyx hx => lexLe_pos hm rest hyx hx) _
  rw [hg] at hr
  obtain ⟨w1, w2, hw1, -, rfl⟩ := mapM_append_ok hw
  have hl : (w1.map wordsFoR).length = ks.length := by rw [List.length_map, (mapM_ok hw1).1, (mapM_ok hc1).1]
  rw [hg, List.map_append, List.take_left' hl]
  unfold kasc
  simp only [hc1, hr, hw1, bind, Except.bind, pure, Except.pure]

/-- **Law A2** (PLAN 6.13): with a `pos` column first the rows are already in order: the permutation is the `pos`
column and every answer column is its own words. -/
theorem kasc_pos_first (m : USize) (rest : List (QAtomicType × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m ((.i64, .pos) :: rest) = .ok (vs, p)) :
    p = wordsFoR (raw .i64 m (.pos : Enc)) ∧ vs = ((.i64, .pos) :: rest).map fun e => wordsFoR (raw .i64 m e.2) := by
  obtain ⟨cs, hc, r, hr, wss, hw, rfl, rfl⟩ := kasc_ok h
  have hm := ascCol_pos hc
  -- a strictly sorted permutation of `til m` is `til m`
  have hg : ascGrade m.toNat (cs.map (·.2)) = List.range m.toNat := by
    rw [ascCol_keys hc, ← List.nil_append (ascKeys m _), ascGrade_append (fun y x hyx hx => lexLe_pos hm rest hyx hx)]
    obtain ⟨hp, hs⟩ := ascGrade_spec m.toNat []
    exact hp.eq_of_pairwise (fun a _ _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl a))
      (hs.imp fun h => h.2 rfl) List.pairwise_lt_range
  rw [hg] at hr
  have hM : m.toNat < 2 ^ 64 := by have := m.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  obtain ⟨wlen, wf⟩ := mapM_ok hw
  have hpr : ((List.range m.toNat).map Nat.toUInt64).toArray = raw .i64 m (.pos : Enc) := by
    show _ = (Array.range m.toNat).map UInt64.ofNat
    apply Array.ext (by simp) fun k h1 h2 => ?_
    simp [Nat.toUInt64_eq]
  refine ⟨by rw [hg, hpr], List.ext_getElem (by simp [wlen, hlen]) fun c h1 h2 => ?_⟩
  rw [List.length_map] at h1 h2
  rw [List.getElem_map, List.getElem_map]
  have hcl : c < cs.length := by omega
  obtain ⟨hx, hxs, -⟩ := ascCol_ok (hf c _ _ (List.getElem?_eq_getElem h2) (List.getElem?_eq_getElem hcl))
  obtain ⟨hvs, hk⟩ := scatter_grade hM (List.Perm.refl _) hr hxs (wf c _ _ (List.getElem?_eq_getElem hcl)
    (List.getElem?_eq_getElem h1))
  refine congrArg wordsFoR (Array.ext_getElem? fun k => ?_)
  rw [← hx]
  by_cases hkm : k < m.toNat
  · have := hk k (by rw [List.length_range]; exact hkm)
    rwa [List.getElem_range] at this
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- The float branch of `ordCode` is one to one on the masked word `u`: `^^^ M` and `||| T` are each one to one where
they apply, and they disagree at `T`, the sign bit, which `M` covers. -/
theorem ordCode_float_inj {M T ua ub : UInt64} (hMT : M &&& T = T)
    (h : (if ua &&& T != 0 then ua ^^^ M else ua ||| T) = (if ub &&& T != 0 then ub ^^^ M else ub ||| T)) :
    ua = ub := by
  have back : ∀ x : UInt64, x &&& T = 0 → (x ||| T) ^^^ T = x := fun x hx => UInt64.toBitVec_inj.1 <| BitVec.eq_of_getLsbD_eq fun i _ => by
    have := congrArg (fun z : UInt64 => z.toBitVec.getLsbD i) hx
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_xor, UInt64.toBitVec_zero, BitVec.getLsbD_zero] at this ⊢
    revert this; generalize x.toBitVec.getLsbD i = p; generalize T.toBitVec.getLsbD i = q; revert p q; decide
  have atT : ∀ x y : UInt64, x &&& T ≠ 0 → y &&& T = 0 → x ^^^ M ≠ y ||| T := fun x y hx _ e => hx (by
    refine UInt64.toBitVec_inj.1 <| BitVec.eq_of_getLsbD_eq fun i _ => ?_
    have := congrArg (fun z : UInt64 => (z &&& T).toBitVec.getLsbD i) e
    have hm := congrArg (fun z : UInt64 => z.toBitVec.getLsbD i) hMT
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_xor, UInt64.toBitVec_zero, BitVec.getLsbD_zero] at this hm ⊢
    revert this hm; generalize x.toBitVec.getLsbD i = p; generalize T.toBitVec.getLsbD i = q
    generalize M.toBitVec.getLsbD i = r; generalize y.toBitVec.getLsbD i = s; revert p q r s; decide)
  by_cases ha : ua &&& T = 0 <;> by_cases hb : ub &&& T = 0 <;> simp only [ha, hb, bne_self_eq_false, bne_iff_ne,
    ne_eq, not_false_eq_true, if_true, if_false, Bool.false_eq_true] at h
  · rw [← back ua ha, h, back ub hb]
  · exact absurd h.symm (atT ub ua hb ha)
  · exact absurd h (atT ua ub ha hb)
  · exact (UInt64.xor_left_inj _).1 h

/-- **`ordCode` is one to one on the `w`-byte word**: equal codes, equal low `8 * w` bits. -/
theorem ordCode_inj {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) {float signed : Bool} {a b : UInt64}
    (h : ordCode w float signed a = ordCode w float signed b) : a.toNat % 2 ^ (8 * w) = b.toNat % 2 ^ (8 * w) := by
  rw [← toNat_and_mask h1 h8, ← toNat_and_mask h1 h8]
  refine congrArg UInt64.toNat ?_
  have hMT : (if w == 8 then (0xffffffffffffffff : UInt64) else (2 ^ (8 * w) - 1).toUInt64) &&&
      (2 ^ (8 * w - 1)).toUInt64 = (2 ^ (8 * w - 1)).toUInt64 := by
    have hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by omega
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  unfold ordCode at h
  cases float <;> cases signed <;> simp only [Bool.false_eq_true, if_false, if_true] at h
  · exact h
  · exact (UInt64.xor_left_inj _).1 h
  · exact ordCode_float_inj hMT h
  · exact ordCode_float_inj hMT h

/-- **Equal order codes, equal atoms**, at every type with an order code (`ascOrd`): the code is one to one on the
type's stored bits (`ordCode_inj`), and the atom reads only those bits; a `u1` word is `0` or `1`. -/
theorem ascOrd_atom {t : QAtomicType} {f : UInt64 → UInt64} (ht : ascOrd t = some f) (hg : t ≠ .general)
    {a b : UInt64} (hu : t = .u1 → a < 2 ∧ b < 2) (h : f a = f b) :
    Column.atomOfBits t a hg = Column.atomOfBits t b hg := by
  have key : ∀ {w}, t.width = some w → t ≠ .u1 → a.toNat % 2 ^ (8 * w) = b.toNat % 2 ^ (8 * w) →
      Column.atomOfBits t a hg = Column.atomOfBits t b hg := fun hw hb e =>
    (atomOfBits_mod hw hb a).symm.trans (e ▸ atomOfBits_mod hw hb b)
  cases t <;> simp only [ascOrd, ascLayout, orderKind, Option.map_some, Option.map_none, reduceCtorEq,
    Option.some.injEq] at ht <;> subst ht
  case u1 =>
    obtain ⟨ha, hb⟩ := hu rfl
    have e : a.toNat % 2 ^ 8 = b.toNat % 2 ^ 8 := ordCode_inj (w := 1) (by decide) (by decide) h
    have ha' : a.toNat < 2 := ha
    have hb' : b.toNat < 2 := hb
    rw [UInt64.toNat_inj.1 (by omega : a.toNat = b.toNat)]
  all_goals exact key rfl (by decide) (ordCode_inj (by decide) (by decide) h)

end Rel.Verify

/-- info: 'Rel.Verify.asc_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.asc_perm

/-- info: 'Rel.Verify.kasc_pos_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.kasc_pos_first

/-- info: 'Rel.Verify.kasc_pos_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.kasc_pos_key
