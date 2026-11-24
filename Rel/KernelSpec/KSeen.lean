module

public import Rel.Kernel.Seen
public import Rel.KernelSpec.Asc
public import Rel.KernelSpec.Codes

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `seen`'s laws (PLAN D.12): `kseen_ok` reads its answer as `firstsOf`/`groupOf` of the rows' order codes
(`seenKey`), `kseen_sorted` says it answers only rows in `kasc` order, and the first-occurrence laws hold over any key (`firsts_spec`, `firsts_runs`, `firsts_all`). That `kasc ≫ kseen` takes neither error
is `kasc_kseen` (`Rel/RepSeen.lean`), which needs `kasc`'s grade laws. -/

namespace Rel.Verify
open Rel.Kernel Enc

/-- Row `i`'s key as `kseen` compares it: its order code in every column (`ascKeys`, `kasc`'s codes). -/
def seenKey (n : USize) (es : List (AscKey × Enc)) (i : Nat) : List UInt64 := (ascKeys n es).map (·[i]?.getD 0)

/-- The columns `kseen` reads are `kasc`'s codes: where its `ascCol` pass over `es` answers `ks`, `ks = ascKeys n es`. -/
theorem kseen_keys {n : USize} {es : List (AscKey × Enc)} {kss : List (List (Array UInt64))}
    (heq : es.zipIdx.mapM (fun (c, i) => (fun x : Array UInt64 × List (Array UInt64) => x.2) <$>
      (ascCol n c).mapError (s!"seen: es[{i}]: " ++ ·)) = .ok kss) :
    kss.flatten = ascKeys n es := by
  have hflat : ∀ es : List (AscKey × Enc), ascKeys n es = (es.map (ascKey n)).flatten := fun es => by
    induction es with
    | nil => rw [ascKeys]; rfl
    | cons e es ih => rw [ascKeys, List.map_cons, List.flatten_cons, ih]
  rw [hflat]
  congr 1
  obtain ⟨hlen, hf⟩ := mapM_ok heq
  rw [List.length_zipIdx] at hlen
  apply List.ext_getElem? fun i => ?_
  cases hei : es[i]? with
  | none =>
    have := List.getElem?_eq_none_iff.1 hei
    simp [hei, List.getElem?_eq_none_iff.2 (show kss.length ≤ i by omega)]
  | some e =>
    have hi := (List.getElem?_eq_some_iff.1 hei).1
    obtain ⟨b, hb⟩ : ∃ b, kss[i]? = some b := ⟨kss[i], List.getElem?_eq_getElem (by omega)⟩
    have he := hf i (e, i) b (by simp [List.getElem?_zipIdx, hei]) hb
    cases hce : ascCol n e with
    | error s => simp [hce, Functor.map, Except.map, Except.mapError] at he
    | ok xk =>
      simp only [hce, Functor.map, Except.map, Except.mapError, Except.ok.injEq] at he
      simp [hb, hei, ← he, (ascCol_ok hce).2.2.1]

/-- **`kseen` answers only rows in `kasc` order**: where it answers, each row is `lexLe` the next under `kasc`'s codes
(`ascKeys`), so on its answers a group is a run of adjacent equal rows (`firsts_runs`). -/
theorem kseen_sorted {n : USize} {es : List (AscKey × Enc)} {r : Nat × Enc × Enc} (h : kseen n es = .ok r) :
    ∀ i, i + 1 < n.toNat → lexLe (ascKeys n es) i (i + 1) = true := by
  unfold kseen at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ks heq
    rw [← kseen_keys heq]
    split at h
    · cases h
    · rename_i hs
      intro i hi
      cases hf : (List.range (n.toNat - 1)).find? (fun i => !lexLe ks.flatten i (i + 1)) with
      | some j => rw [hf] at hs; nomatch hs
      | none => simpa using List.find?_eq_none.1 hf i (List.mem_range.2 (by omega))

/-- **Rows in `lexLe` order are runs**: where each row below `n` is `lexLe` the next, a row between two rows of one key
has that key, because it is `lexLe` both ways with them (`lexLe_trans`, `keys_of_lexLe`). -/
theorem lexLe_runs (ks : List (Array UInt64)) {n : Nat} (hs : ∀ i, i + 1 < n → lexLe ks i (i + 1) = true) :
    ∀ a b c, a ≤ b → b ≤ c → c < n →
      ks.map (·[a]?.getD 0) = ks.map (·[c]?.getD 0) → ks.map (·[b]?.getD 0) = ks.map (·[a]?.getD 0) := by
  have up : ∀ d i, i + d < n → lexLe ks i (i + d) = true := by
    intro d; induction d with
    | zero => intro i _; exact lexLe_of_keys _ rfl
    | succ d ih => intro i hi; exact lexLe_trans _ _ _ _ (ih i (by omega)) (hs (i + d) (by omega))
  have up' : ∀ i j, i ≤ j → j < n → lexLe ks i j = true := fun i j hij hj => by
    have := up (j - i) i (by omega); rwa [Nat.add_sub_of_le hij] at this
  intro a b c hab hbc hc e
  exact (keys_of_lexLe _ (up' a b hab (by omega))
    (lexLe_trans _ _ _ _ (up' b c hbc hc) (lexLe_of_keys _ e.symm))).symm

/-- **`kseen` answers `firstsOf` and `groupOf` of `seenKey`**: the count of first rows, each row's group as `n` words
and the first rows ascending as `k` words, each as `wordsFoR`. -/
theorem kseen_ok {n : USize} {es : List (AscKey × Enc)} {k : Nat} {g f : Enc} (h : kseen n es = .ok (k, g, f)) :
    k = (firstsOf (seenKey n es) n.toNat).length ∧
      g = wordsFoR (Array.ofFn (n := n.toNat) fun i => (groupOf (seenKey n es) n.toNat i.1).toUInt64) ∧
      f = wordsFoR ((firstsOf (seenKey n es) n.toNat).map Nat.toUInt64).toArray := by
  unfold kseen at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ks heq
    have hk := kseen_keys heq
    simp only [hk] at h
    split at h
    · cases h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hf : Order.firstsBy n.toNat (seenKey n es) = firstsOf (seenKey n es) n.toNat := firstsBy_eq _ _
    refine ⟨congrArg List.length hf, ?_, by rw [← hf]; rfl⟩
    show wordsFoR (Array.ofFn fun i => (Order.groupIn (Order.firstsBy n.toNat (seenKey n es)) (seenKey n es) i.1).toUInt64) = _
    simp only [groupIn_firstsBy]

/-- **The first-occurrence laws** over a key `g` on the rows below `m`, `F = firstsOf g m` and `G = groupOf g m`:
`F` ascends, holds exactly the rows whose key no earlier row has (law a), `G` is constant exactly on equal keys and
numbers `F` in order (law b), and row `i`'s group is `j` exactly when `F[j]` holds its key: `G = g ≫ (F ≫ g)°` (law e),
whose first row is the earliest with that key. -/
theorem firsts_spec {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat) :
    (firstsOf g m).Pairwise (· < ·) ∧ (∀ p, p ∈ firstsOf g m ↔ p < m ∧ ∀ q < p, g q ≠ g p) ∧
      (∀ i < m, ∀ j < m, groupOf g m i = groupOf g m j ↔ g i = g j) ∧
      (∀ j (hj : j < (firstsOf g m).length), groupOf g m (firstsOf g m)[j] = j) ∧
      (∀ i < m, ∀ j, groupOf g m i = j ↔ ∃ hj : j < (firstsOf g m).length, g (firstsOf g m)[j] = g i) ∧
      ∀ i < m, ∃ hj : groupOf g m i < (firstsOf g m).length, (firstsOf g m)[groupOf g m i] ≤ i ∧
        g (firstsOf g m)[groupOf g m i] = g i ∧ ∀ q < (firstsOf g m)[groupOf g m i], g q ≠ g i := by
  have hmem : ∀ p, p ∈ firstsOf g m ↔ p < m ∧ ∀ q < p, g q ≠ g p := fun p => by
    unfold firstsOf
    simp only [List.mem_filter, List.mem_range, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  have he : ∀ i < m, ∀ j, groupOf g m i = j ↔ ∃ hj : j < (firstsOf g m).length, g (firstsOf g m)[j] = g i :=
    fun i hi j => ⟨fun e => ⟨e ▸ groupOf_lt hi, by subst e; exact groupOf_get hi⟩,
      fun ⟨hj, e⟩ => (groupOf_eq_iff hi hj).2 e.symm⟩
  refine ⟨(pairwise_range m).filter _, hmem, fun i hi j hj => groupOf_iff hi hj, fun j hj => ?_, he,
    fun i hi => ⟨groupOf_lt hi, ?_⟩⟩
  · exact (he _ (firsts_lt g m (List.getElem_mem hj)) j).2 ⟨hj, rfl⟩
  · have hf := (hmem _).1 (List.getElem_mem (groupOf_lt hi))
    have hg := groupOf_get (g := g) hi
    refine ⟨Nat.le_of_not_lt fun hlt => hf.2 i hlt hg.symm, hg, fun q hq => hg ▸ hf.2 q hq⟩


/-- **Law c**: where equal keys sit in one run of rows (a sorted key, `kasc`'s answer), the first rows are the run
starts, the rows whose key differs from the row before, the answer the retired `kdistinct` gave. -/
theorem firsts_runs {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (h : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) (p : Nat) :
    p ∈ firstsOf g m ↔ p < m ∧ ∀ q, q + 1 = p → g q ≠ g p := by
  rw [(firsts_spec g m).2.1]
  refine ⟨fun ⟨hp, hq⟩ => ⟨hp, fun q e => hq q (by omega)⟩, fun ⟨hp, hq⟩ => ⟨hp, fun q hqp e => ?_⟩⟩
  exact hq (p - 1) (by omega) ((h q (p - 1) p (by omega) (by omega) hp e).trans e)

/-- **Law d**: a key with no two equal rows below `m` (a `pos` column, `kseen_pos`) makes every row new: the first rows
are all rows and each row is its own group. -/
theorem firsts_all {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (h : ∀ i < m, ∀ j < m, g i = g j → i = j) : firstsOf g m = List.range m ∧ ∀ i < m, groupOf g m i = i := by
  have hf : firstsOf g m = List.range m := List.filter_eq_self.2 fun i hi => by
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
    exact fun j hj e => absurd (h j (by have := List.mem_range.1 hi; omega) i (List.mem_range.1 hi) e) (by omega)
  refine ⟨hf, fun i hi => ((firsts_spec g m).2.2.2.2.1 i hi i).2 ⟨by rw [hf, List.length_range]; exact hi, ?_⟩⟩
  rw [List.getElem_of_eq hf, List.getElem_range]

/-- **Law d for `kseen`**: with a `pos` column in its key every row is new, `k = n`, `first = til n` and `g = til n`. -/
theorem kseen_pos {n : USize} {ks rest : List (AscKey × Enc)} {k : Nat} {g f : Enc}
    (h : kseen n (ks ++ (.atom .i64, .pos) :: rest) = .ok (k, g, f)) :
    firstsOf (seenKey n (ks ++ (.atom .i64, .pos) :: rest)) n.toNat = List.range n.toNat ∧
      ∀ i < n.toNat, groupOf (seenKey n (ks ++ (.atom .i64, .pos) :: rest)) n.toNat i = i := by
  refine firsts_all fun i hi j hj e => ?_
  have hm : n.toNat ≤ 2 ^ 63 := by
    unfold kseen at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i cs heq
      obtain ⟨hlen, hf⟩ := mapM_ok heq
      have he := hf ks.length ((.atom .i64, .pos), ks.length) (cs[ks.length]'(by simp [List.length_zipIdx] at hlen; omega))
        (by simp) (List.getElem?_eq_getElem _)
      refine Classical.byContradiction fun hm => ?_
      simp [ascCol, ascWords, ascOrd, ascLayout, orderKind, hm, Functor.map, Except.map, Except.mapError] at he
  have hc : ∀ i, i < 2 ^ 63 → (ordKey 8 false true (UInt64.ofNat i)).toNat = i + 2 ^ 63 := fun i hi => by
    have := ordKey_signed (w := 8) (by omega) (by omega) (UInt64.ofNat i)
    simp only [sx, UInt64.toNat_ofNat'] at this
    split at this <;> omega
  have e := congrArg (·[(ascKeys n ks).length]?) e
  have hpr : raw .i64 n (.pos : Enc) = (Array.range n.toNat).map UInt64.ofNat := rfl
  simp only [seenKey, ascKeys_append, ascKeys, ascKey, nulCodes, nulWords, hasNul, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.map_append, List.map_cons, hpr, Array.getElem?_map, Array.getElem?_range, hi, hj,
    if_true, Option.map_some, Option.getD_some] at e
  rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)] at e
  simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at e
  have := congrArg UInt64.toNat e
  change (ordKey 8 false true (UInt64.ofNat i)).toNat = (ordKey 8 false true (UInt64.ofNat j)).toNat at this
  rw [hc i (by omega), hc j (by omega)] at this; omega

end Rel.Verify
