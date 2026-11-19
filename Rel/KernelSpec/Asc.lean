import Rel.Kernel.Asc
import Rel.KernelSpec.Scatter

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
      -- `ascWords` answers `foRWords`' words or an error
      have hf : foRWords "asc" m c.2 = .ok x := by
        rw [← hx]; obtain ⟨t, e⟩ := c
        cases e <;> cases t <;> first | exact hw | cases hw
      obtain ⟨rfl, hs⟩ := foRWords_raw _ _ _ _ hf
      exact ⟨rfl, hs, f, rfl, by rw [← hk, hx]⟩

/-- The order codes `kasc` sorts by: each column's words (`foRWords`) through its type's `ascOrd`. -/
def ascKeys (m : USize) (es : List (QAtomicType × Enc)) : List (Array UInt64) :=
  es.map fun e => (raw .i64 m e.2).map ((ascOrd e.1).getD id)

/-- `scatterWords` twice through a permutation `ps` of `til M`: `til M` through `ps` puts `k` at `ps[k]`, and `x`
through that puts `x[ps[k]]` at `k`. -/
theorem scatter_grade {M : Nat} (hM : M < 2 ^ 64) {ps : List Nat} (hp : ps.Perm (List.range M))
    {r x v : Array UInt64}
    (hr : scatterWords (ps.map Nat.toUInt64).toArray ((List.range M).map Nat.toUInt64).toArray M 0 = .ok r)
    (hx : x.size = M) (hv : scatterWords r x M 0 = .ok v) :
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
    ∃ cs, es.mapM (ascCol m) = .ok cs ∧ ∃ r, scatterWords ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray
      ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 = .ok r ∧
      ∃ wss, cs.mapM (fun c => scatterWords r c.1 m.toNat 0) = .ok wss ∧ vs = wss.map wordsFoR ∧
        p = wordsFoR ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray := by
  unfold kasc at h
  cases hc : es.mapM (ascCol m) with
  | error s => simp [hc, bind, Except.bind] at h
  | ok cs =>
    cases hr : scatterWords ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray
        ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 with
    | error s => simp [hc, hr, bind, Except.bind] at h
    | ok r =>
      cases hw : cs.mapM (fun c => scatterWords r c.1 m.toNat 0) with
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

end Rel.Verify

/-- info: 'Rel.Verify.asc_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.asc_perm
