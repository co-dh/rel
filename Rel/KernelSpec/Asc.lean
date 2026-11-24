module

public import Rel.Kernel.Asc
public import Rel.KernelSpec.Scatter
public import Rel.KernelSpec.Search

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `asc`'s laws (design §4, `asc_sorted` and `asc_perm`), on the words `Enc.raw` reads from its arguments: the
permutation is a stable lexicographic sort of the rows by their order codes, and each answer column is its input
column read through the permutation. -/

namespace Rel.Verify
open Rel.Kernel Enc

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

/-- Rows with equal codes are `lexLe` both ways. -/
theorem lexLe_of_keys : ∀ (ks : List (Array UInt64)) {i j : Nat},
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0) → lexLe ks i j = true
  | [], _, _, _ => rfl
  | c :: cs, i, j, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [lexLe, h.1, lexLe_of_keys cs h.2]

/-- Rows `lexLe` both ways have equal codes. -/
theorem keys_of_lexLe : ∀ (ks : List (Array UInt64)) {i j : Nat}, lexLe ks i j = true → lexLe ks j i = true →
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0)
  | [], _, _, _, _ => rfl
  | c :: cs, i, j, h1, h2 => by
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2
    simp only [List.map_cons, List.cons.injEq]
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · have := UInt64.lt_iff_toNat_lt.1 h1; have := UInt64.lt_iff_toNat_lt.1 h2; omega
    · rw [e2] at h1; exact absurd (UInt64.lt_iff_toNat_lt.1 h1) (Nat.lt_irrefl _)
    · rw [e1] at h2; exact absurd (UInt64.lt_iff_toNat_lt.1 h2) (Nat.lt_irrefl _)
    · exact ⟨e1, keys_of_lexLe cs h1 h2⟩

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

mutual
/-- The order codes of one key column at `m` rows, `ascCol`'s on the words `Enc.raw` reads: an `atom` column's words
through its type's `ascOrd`, a `cells` column's words through `cellFns` over its payload's `ascKeys`. A null row's
word is never read (`nulWords`): `ascCol` refuses a null in a `cells` column, but `AscKey × Enc` admits one. A cell
whose `lo` or `hi` is null is the empty cell, as in `ascCol`. -/
def ascKey (m : USize) : AscKey × Enc → List (Array UInt64)
  | (.atom t, e) => nulCodes m e ((raw .i64 m e).map ((ascOrd t).getD id))
  | (.cells n c lo hi els, e) =>
    (cellFns c.toNat (nulWords n lo (raw .i64 n lo)) (nulWords n lo (nulWords n hi (raw .i64 n hi))) (ascKeys c els)).map
      fun f => (nulWords m e (raw .i64 m e)).map f

/-- The order codes `kasc` sorts by: each key column's `ascKey`, in the order of `es`. -/
def ascKeys (m : USize) : List (AscKey × Enc) → List (Array UInt64)
  | [] => []
  | e :: es => ascKey m e ++ ascKeys m es
end

theorem ascKeys_append (m : USize) (e1 e2 : List (AscKey × Enc)) : ascKeys m (e1 ++ e2) = ascKeys m e1 ++ ascKeys m e2 := by
  induction e1 with
  | nil => rw [List.nil_append, ascKeys, List.nil_append]
  | cons e es ih => simp only [List.cons_append, ascKeys, ih, List.append_assoc]

/-- `nulCodes` at row `q` is a function of the column's null test (`hasNul`, which decides how many code columns it
has), its null flag and its word there where that is no null (`nulWords`): a null's code is `0` whatever its word. -/
theorem nulCodes_row {m m' : USize} {e e' : Enc} {c c' : Array UInt64} {g : UInt64 → UInt64} {q q' : Nat}
    (hh : hasNul e = hasNul e') (hf : (foRNuls m e)[q]? = (foRNuls m' e')[q']?)
    (hc : (nulWords m e c)[q]? = (nulWords m' e' c')[q']?) :
    (nulCodes m e (c.map g)).map (·[q]?.getD 0) = (nulCodes m' e' (c'.map g)).map (·[q']?.getD 0) := by
  unfold nulCodes nulWords at *; rw [hh] at hc ⊢
  cases hN : hasNul e' <;> simp only [hN, Bool.false_eq_true, ↓reduceIte] at hc ⊢
  · simp [Array.getElem?_map, hc]
  · simp only [List.singleton_append, List.map_cons, List.map_nil, Array.getElem?_mapIdx, Array.getElem?_map, hf]
      at hc ⊢
    cases h1 : c[q]? <;> cases h2 : c'[q']? <;> simp only [h1, h2, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hc ⊢ <;> by_cases hF : ((foRNuls m' e')[q']?.getD 0 == 0) = true <;>
      simp_all

/-- `nulWords` leaves the words of a column with no null row alone: `noNul`'s answer `ok`. -/
theorem nulWords_noNul {w : String} {m : USize} {e : Enc} {u : Unit} (h : noNul w m e = .ok u) (c : Array UInt64) :
    nulWords m e c = c := by
  unfold noNul at h; unfold nulWords
  split; rotate_left; · rfl
  rename_i hN; simp only [hN, ↓reduceIte] at h
  split at h; · cases h
  rename_i hn
  have h0 := Array.findIdx?_eq_none_iff.1 hn
  refine Array.ext (by simp) fun i h1 _ => ?_
  simp only [Array.getElem_mapIdx]
  cases hi : (foRNuls m e)[i]? with
  | none => rfl
  | some x => have := h0 x (Array.mem_of_getElem? hi); simp_all

/-- **A row's codes are a function of its words and null flags**: two key lists of one shape whose columns have one
null test, one null flag at rows `q` and `q'`, and one word there where that is no null (`nulWords`), have one code at
those rows in every column of `ascKeys`, so a permuted column has the permuted codes. -/
theorem ascKeys_row {m m' : USize} {q q' : Nat} : ∀ {K K' : List (AscKey × Enc)}, K.map (·.1) = K'.map (·.1) →
    (∀ c (h : c < K.length) (h' : c < K'.length),
      (nulWords m K[c].2 (raw .i64 m K[c].2))[q]? = (nulWords m' K'[c].2 (raw .i64 m' K'[c].2))[q']?) →
    (∀ c (h : c < K.length) (h' : c < K'.length), hasNul K[c].2 = hasNul K'[c].2 ∧
      (foRNuls m K[c].2)[q]? = (foRNuls m' K'[c].2)[q']?) →
    (ascKeys m K).map (·[q]?.getD 0) = (ascKeys m' K').map (·[q']?.getD 0)
  | [], [], _, _, _ => by simp only [ascKeys]; rfl
  | [], _ :: _, hk, _, _ => by simp at hk
  | _ :: _, [], hk, _, _ => by simp at hk
  | (k, e) :: K, (k', e') :: K', hk, hw, hn => by
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨rfl, hk⟩ := hk
    have h0 := hw 0 (by simp) (by simp)
    have hn0 := hn 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0 hn0
    simp only [ascKeys, List.map_append]
    congr 1
    · cases k
      · simp only [ascKey]; exact nulCodes_row hn0.1 hn0.2 h0
      · simp only [ascKey, List.map_map, Function.comp_def, Array.getElem?_map, h0]
    · exact ascKeys_row hk (fun c h h' => hw (c + 1) (by simp; omega) (by simp; omega))
        fun c h h' => hn (c + 1) (by simp; omega) (by simp; omega)

mutual
/-- What `ascCol` answers: the column's words as `Enc.raw` reads them, `m` of them, and its codes `ascKey`; an `atom`
column's type has an order. -/
theorem ascCol_ok : ∀ {m : USize} {c : AscKey × Enc} {x : Array UInt64} {k : List (Array UInt64)},
    ascCol m c = .ok (x, k) → x = raw .i64 m c.2 ∧ x.size = m.toNat ∧ k = ascKey m c ∧
      ∀ t, c.1 = .atom t → ∃ f, ascOrd t = some f
  | m, (.atom t, e), x, k, h => by
    rw [ascCol] at h
    cases ho : ascOrd t with
    | none => simp [ho] at h
    | some f =>
      cases hw : ascWords m (t, e) with
      | error s => simp [ho, hw, Functor.map, Except.map] at h
      | ok w =>
        simp only [ho, hw, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hx, hk⟩ := h
        have hf : foRWords "asc" m e = .ok x := hx ▸ ascWords_foR hw
        obtain ⟨rfl, hs⟩ := foRWords_raw _ _ _ _ hf
        refine ⟨rfl, hs, ?_, fun t' ht => ⟨f, by cases ht; exact ho⟩⟩
        rw [← hk, hx, ascKey, ho, Option.getD_some]
  | m, (.cells n c lo hi els, e), x, k, h => by
    rw [ascCol] at h
    cases hix : foRWords "asc: cells" m e with
    | error s => simp [hix, bind, Except.bind] at h
    | ok ix =>
      cases hn0 : noNul "asc: cells" m e with
      | error s => simp [hix, hn0, bind, Except.bind] at h
      | ok u0 =>
      cases hf : ix.find? (n.toNat ≤ ·.toNat) with
      | some r => simp [hix, hn0, hf, bind, Except.bind] at h
      | none =>
        cases hl : foRWords "asc: cells lo" n lo with
        | error s => simp [hix, hn0, hf, hl, bind, Except.bind] at h
        | ok l =>
          cases hh : foRWords "asc: cells hi" n hi with
          | error s => simp [hix, hn0, hf, hl, hh, bind, Except.bind] at h
          | ok hw =>
            cases hks : ascCodes c els with
            | error s => simp [hix, hn0, hf, hl, hh, hks, bind, Except.bind] at h
            | ok ks =>
              simp only [hix, hn0, hf, hl, hh, hks, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨rfl, hs⟩ := foRWords_raw _ _ _ _ hix
              obtain ⟨rfl, -⟩ := foRWords_raw _ _ _ _ hl
              obtain ⟨rfl, -⟩ := foRWords_raw _ _ _ _ hh
              refine ⟨rfl, hs, ?_, fun t ht => by cases ht⟩
              rw [ascKey, ascCodes_ok hks, nulWords_noNul hn0]

/-- What `ascCodes` answers: `ascKeys`. -/
theorem ascCodes_ok : ∀ {m : USize} {es : List (AscKey × Enc)} {ks : List (Array UInt64)},
    ascCodes m es = .ok ks → ks = ascKeys m es
  | _, [], ks, h => by rw [ascCodes] at h; cases h; rw [ascKeys]
  | m, e :: es, ks, h => by
    rw [ascCodes] at h
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc
    split at h; · cases h
    rename_i ks' hks
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h, ascKeys, (ascCol_ok hc).2.2.1, ascCodes_ok hks]
end

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
theorem kasc_ok {m : USize} {es : List (AscKey × Enc)} {vs : List Enc} {p : Enc} (h : kasc m es = .ok (vs, p)) :
    ∃ cs, es.mapM (ascCol m) = .ok cs ∧ ∃ r, scatterWords .last ((ascGrade m.toNat (cs.flatMap (·.2))).map Nat.toUInt64).toArray
      ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 = .ok r ∧
      ∃ wss, cs.mapM (fun c => scatterWords .last r c.1 m.toNat 0) = .ok wss ∧
      ∃ ns, es.mapM (fun x : AscKey × Enc => if hasNul x.2 = true then
        nulMap <$> scatterWords .last r (foRNuls m x.2) m.toNat 0 else pure ByteArray.empty) = .ok ns ∧
        vs = wss.zipWith (fun v n => wordsFoR v n) ns ∧
        p = wordsFoR ((ascGrade m.toNat (cs.flatMap (·.2))).map Nat.toUInt64).toArray := by
  unfold kasc at h
  cases hc : es.mapM (ascCol m) with
  | error s => simp [hc, bind, Except.bind] at h
  | ok cs =>
    cases hr : scatterWords .last ((ascGrade m.toNat (cs.flatMap (·.2))).map Nat.toUInt64).toArray
        ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0 with
    | error s => simp [hc, hr, bind, Except.bind] at h
    | ok r =>
      cases hw : cs.mapM (fun c => scatterWords .last r c.1 m.toNat 0) with
      | error s => simp [hc, hr, hw, bind, Except.bind] at h
      | ok wss =>
        cases hn : es.mapM (fun x : AscKey × Enc => if hasNul x.2 = true then
            nulMap <$> scatterWords .last r (foRNuls m x.2) m.toNat 0 else pure ByteArray.empty) with
        | error s => simp [hc, hr, hw, hn, bind, Except.bind] at h
        | ok ns =>
          simp only [hc, hr, hw, bind, Except.bind] at h; rw [hn] at h
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨cs, rfl, r, hr, wss, hw, ns, hn, h.1.symm, h.2.symm⟩

/-- The key columns' codes are `ascKeys`. -/
theorem ascCol_keys {m : USize} {es : List (AscKey × Enc)} {cs} (hc : es.mapM (ascCol m) = .ok cs) :
    cs.flatMap (·.2) = ascKeys m es := by
  induction es generalizing cs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hc; subst hc; rw [ascKeys]; rfl
  | cons e es ih =>
    rw [List.mapM_cons] at hc
    cases he : ascCol m e with
    | error s => simp [he, bind, Except.bind] at hc
    | ok c =>
      cases hes : es.mapM (ascCol m) with
      | error s => simp [he, hes, bind, Except.bind] at hc
      | ok cs' =>
        simp only [he, hes, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hc
        subst hc
        rw [List.flatMap_cons, ih hes, ascKeys, (ascCol_ok he).2.2.1]


/-- **`asc_perm`** (design §4): the permutation `kasc` answers is a permutation `ps` of `til m`, and the answer for each
key column `e` holds `m` words, word `k` being `e`'s raw word at row `ps[k]`. -/
theorem asc_perm (m : USize) (es : List (AscKey × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m es = .ok (vs, p)) :
    ∃ ps : List Nat, p = wordsFoR (ps.map Nat.toUInt64).toArray ∧ ps.Perm (List.range m.toNat) ∧
      vs.length = es.length ∧ ∀ (c : Nat) e v, es[c]? = some e → vs[c]? = some v →
        ∃ (ws : Array UInt64) (nul : ByteArray), v = wordsFoR ws nul ∧ ws.size = m.toNat ∧
          (∀ k (hk : k < ps.length), ws[k]? = (raw .i64 m e.2)[ps[k]]?) ∧
          (hasNul e.2 = false → nul = .empty) ∧
          (hasNul e.2 = true → ∃ nf : Array UInt64, nul = nulMap nf ∧ nf.size = m.toNat ∧
            ∀ k (hk : k < ps.length), nf[k]? = (foRNuls m e.2)[ps[k]]?) := by
  obtain ⟨cs, hc, r, hr, wss, hw, ns, hn, rfl, rfl⟩ := kasc_ok h
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  obtain ⟨wlen, wf⟩ := mapM_ok hw
  obtain ⟨nlen, nf⟩ := mapM_ok hn
  have hM : m.toNat < 2 ^ 64 := by have := m.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  have hperm := (ascGrade_spec m.toNat (cs.flatMap (·.2))).1
  refine ⟨_, rfl, hperm, by simp [wlen, hlen, nlen], fun c e v hec hvc => ?_⟩
  cases hwc : wss[c]? with
  | none => simp [List.getElem?_zipWith, hwc] at hvc
  | some ws =>
    cases hnc : ns[c]? with
    | none => simp [List.getElem?_zipWith, hwc, hnc] at hvc
    | some nl =>
    simp only [List.getElem?_zipWith, hwc, hnc, Option.some.injEq] at hvc
    subst hvc
    cases hcc : cs[c]? with
    | none =>
      have h1 := List.getElem?_eq_none_iff.1 hcc
      have h2 := (List.getElem?_eq_some_iff.1 hwc).1
      omega
    | some cc =>
      obtain ⟨hx, hxs, -, -⟩ := ascCol_ok (hf c e cc hec hcc)
      obtain ⟨hvs, hk⟩ := scatter_grade hM hperm hr hxs (wf c cc ws hcc hwc)
      have hne := nf c e nl hec hnc
      refine ⟨ws, nl, rfl, hvs, fun k hk' => by rw [hk k hk', hx], fun h0 => ?_, fun h1 => ?_⟩
      · simp only [h0, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hne; exact hne.symm
      · simp only [h1, ↓reduceIte] at hne
        cases hs : scatterWords .last r (foRNuls m e.2) m.toNat 0 with
        | error s => simp [hs, Functor.map, Except.map] at hne
        | ok fl =>
          simp only [hs, Functor.map, Except.map, Except.ok.injEq] at hne
          obtain ⟨hfs, hfk⟩ := scatter_grade hM hperm hr (foRNuls_size m e.2) hs
          exact ⟨fl, hne.symm, hfs, hfk⟩

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
theorem lexLe_pos {m : USize} (hm : m.toNat ≤ 2 ^ 63) (rest : List (AscKey × Enc)) {y x : Nat} (hyx : y < x)
    (hx : x < m.toNat) : lexLe (ascKeys m ((.atom .i64, .pos) :: rest)) y x = true := by
  have hc : ∀ i, i < 2 ^ 63 → (ordKey 8 false true (UInt64.ofNat i)).toNat = i + 2 ^ 63 := fun i hi => by
    have := ordKey_signed (w := 8) (by omega) (by omega) (UInt64.ofNat i)
    simp only [sx, UInt64.toNat_ofNat'] at this
    split at this <;> omega
  have hpr : raw .i64 m (.pos : Enc) = (Array.range m.toNat).map UInt64.ofNat := rfl
  simp only [ascKeys, ascKey, nulCodes, nulWords, hasNul, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, lexLe, hpr, Array.getElem?_map, Array.getElem?_range,
    show y < m.toNat by omega, hx, if_true, Option.map_some, Option.getD_some, Bool.or_eq_true, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt]
  left
  show (ordKey 8 false true (UInt64.ofNat y)).toNat < (ordKey 8 false true (UInt64.ofNat x)).toNat
  rw [hc y (by omega), hc x (by omega)]; omega

/-- `ascCol` reads a `pos` column of at most `2^63` rows: past that it is `ascWords`' error. -/
theorem ascCol_pos {m : USize} {rest : List (AscKey × Enc)} {cs : List (Array UInt64 × List (Array UInt64))}
    (h : ((.atom .i64, .pos) :: rest).mapM (ascCol m) = .ok cs) : m.toNat ≤ 2 ^ 63 := by
  rw [List.mapM_cons] at h
  refine Classical.byContradiction fun hm => ?_
  simp [ascCol, ascWords, ascOrd, ascLayout, orderKind, hm, bind, Except.bind, Functor.map, Except.map] at h

/-- **Law A1** (PLAN 6.13): a `pos` key column has no ties and is in row order (`ascWords` admits it only there), so it
and every later column decide nothing: `kasc` with them answers the permutation of `kasc` without them, and the same
leading columns. -/
theorem kasc_pos_key (m : USize) (ks rest : List (AscKey × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m (ks ++ (.atom .i64, .pos) :: rest) = .ok (vs, p)) : kasc m ks = .ok (vs.take ks.length, p) := by
  obtain ⟨cs, hc, r, hr, wss, hw, ns, hn, rfl, rfl⟩ := kasc_ok h
  obtain ⟨cs1, cs2, hc1, hc2, rfl⟩ := mapM_append_ok hc
  have hm := ascCol_pos hc2
  have hg : ascGrade m.toNat ((cs1 ++ cs2).flatMap (·.2)) = ascGrade m.toNat (cs1.flatMap (·.2)) := by
    rw [List.flatMap_append, ascCol_keys hc2]
    exact ascGrade_append (fun y x hyx hx => lexLe_pos hm rest hyx hx) _
  rw [hg] at hr
  obtain ⟨w1, w2, hw1, -, rfl⟩ := mapM_append_ok hw
  obtain ⟨n1, n2, hn1, -, rfl⟩ := mapM_append_ok hn
  have hwn : w1.length = n1.length := by rw [(mapM_ok hw1).1, (mapM_ok hc1).1, (mapM_ok hn1).1]
  have hl : (w1.zipWith (fun v n => wordsFoR v n) n1).length = ks.length := by
    rw [List.length_zipWith, hwn, (mapM_ok hn1).1, Nat.min_self]
  rw [hg, List.zipWith_append hwn, List.take_left' hl]
  unfold kasc
  simp only [hc1, hr, hw1, bind, Except.bind]; rw [hn1]; rfl

/-- **Law A2** (PLAN 6.13): with a `pos` column first the rows are already in order: the permutation is the `pos`
column and every answer column is its own words. -/
theorem kasc_pos_first (m : USize) (rest : List (AscKey × Enc)) (vs : List Enc) (p : Enc)
    (h : kasc m ((.atom .i64, .pos) :: rest) = .ok (vs, p)) :
    p = wordsFoR (raw .i64 m (.pos : Enc)) ∧ vs = ((.atom .i64, .pos) :: rest).map fun e =>
      wordsFoR (raw .i64 m e.2) (if hasNul e.2 then nulMap (foRNuls m e.2) else .empty) := by
  obtain ⟨cs, hc, r, hr, wss, hw, ns, hn, rfl, rfl⟩ := kasc_ok h
  have hm := ascCol_pos hc
  -- a strictly sorted permutation of `til m` is `til m`
  have hg : ascGrade m.toNat (cs.flatMap (·.2)) = List.range m.toNat := by
    rw [ascCol_keys hc, ← List.nil_append (ascKeys m _), ascGrade_append (fun y x hyx hx => lexLe_pos hm rest hyx hx)]
    obtain ⟨hp, hs⟩ := ascGrade_spec m.toNat []
    exact hp.eq_of_pairwise (fun a _ _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl a))
      (hs.imp fun h => h.2 rfl) List.pairwise_lt_range
  rw [hg] at hr
  have hM : m.toNat < 2 ^ 64 := by have := m.toNat_lt_size; rcases USize.size_eq with h | h <;> omega
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  obtain ⟨wlen, wf⟩ := mapM_ok hw
  obtain ⟨nlen, nf⟩ := mapM_ok hn
  have hpr : ((List.range m.toNat).map Nat.toUInt64).toArray = raw .i64 m (.pos : Enc) := by
    show _ = (Array.range m.toNat).map UInt64.ofNat
    apply Array.ext (by simp) fun k h1 h2 => ?_
    simp [Nat.toUInt64_eq]
  -- scattering by the identity permutation keeps a column
  have hid : ∀ {x v : Array UInt64}, x.size = m.toNat → scatterWords .last r x m.toNat 0 = .ok v → v = x :=
    fun hxs hv => by
    obtain ⟨hvs, hk⟩ := scatter_grade hM (List.Perm.refl _) hr hxs hv
    refine Array.ext_getElem? fun k => ?_
    by_cases hkm : k < m.toNat
    · have := hk k (by rw [List.length_range]; exact hkm)
      rwa [List.getElem_range] at this
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  refine ⟨by rw [hg, hpr], List.ext_getElem (by simp [wlen, hlen, nlen]) fun c h1 h2 => ?_⟩
  rw [List.length_zipWith] at h1
  rw [List.length_map] at h2
  rw [List.getElem_zipWith, List.getElem_map]
  have hcl : c < cs.length := by omega
  have hwl : c < wss.length := by omega
  have hnl : c < ns.length := by omega
  obtain ⟨hx, hxs, -, -⟩ := ascCol_ok (hf c _ _ (List.getElem?_eq_getElem h2) (List.getElem?_eq_getElem hcl))
  have hne := nf c _ _ (List.getElem?_eq_getElem h2) (List.getElem?_eq_getElem hnl)
  rw [hid hxs (wf c _ _ (List.getElem?_eq_getElem hcl) (List.getElem?_eq_getElem hwl)), hx]
  congr 1
  generalize ((.atom .i64, .pos) :: rest : List (AscKey × Enc))[c] = E at hne ⊢
  cases h0 : hasNul E.2
  · simp only [h0, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hne ⊢; exact hne.symm
  · simp only [h0, ↓reduceIte] at hne ⊢
    cases hs : scatterWords .last r (foRNuls m E.2) m.toNat 0 with
    | error s => simp [hs, Functor.map, Except.map] at hne
    | ok fl =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at hne
      rw [← hne, hid (foRNuls_size _ _) hs]

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

/-- `atomOfBits_mod`'s converse: the atom determines the low `8 * w` bits it was read from (`Column.bitsOf` reads them
back). -/
theorem mod_of_atomOfBits {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hb : t ≠ .u1) {a b : UInt64}
    (h : Column.atomOfBits t a (QAtomicType.ne_general_of_width ht) =
      Column.atomOfBits t b (QAtomicType.ne_general_of_width ht)) :
    a.toNat % 2 ^ (8 * w) = b.toNat % 2 ^ (8 * w) := by
  have e := congrArg Column.bitsOf h
  cases t <;> simp [QAtomicType.width] at ht <;> subst ht <;> first | exact absurd rfl hb |
    (simp only [Column.atomOfBits, Column.bitsOf] at e; try simp at e) <;>
    first | (subst e; rfl) | simpa [UInt64.toNat_mod] using congrArg UInt64.toNat e

/-- **Equal order codes iff equal atoms**, at every type with an order code (`ascOrd`): the code is one to one on the
type's stored bits (`ordCode_inj`) and reads only those (`toNat_and_mask`), and the atom is one to one on them too
(`atomOfBits_mod`, `mod_of_atomOfBits`); a `u1` word is `0` or `1`. -/
theorem ascOrd_atom {t : QAtomicType} {f : UInt64 → UInt64} (ht : ascOrd t = some f) (hg : t ≠ .general)
    {a b : UInt64} (hu : t = .u1 → a < 2 ∧ b < 2) :
    f a = f b ↔ Column.atomOfBits t a hg = Column.atomOfBits t b hg := by
  have key : ∀ {w fl s}, f = ordCode w fl s → 1 ≤ w → w ≤ 8 → t.width = some w → t ≠ .u1 →
      (f a = f b ↔ Column.atomOfBits t a hg = Column.atomOfBits t b hg) := fun hf h1 h8 hw hb => by
    subst hf
    refine ⟨fun h => (atomOfBits_mod hw hb a).symm.trans (ordCode_inj h1 h8 h ▸ atomOfBits_mod hw hb b), fun h => ?_⟩
    have e := mod_of_atomOfBits hw hb h
    have hm := UInt64.toNat_inj.1 ((toNat_and_mask h1 h8 a).trans (e.trans (toNat_and_mask h1 h8 b).symm))
    simp only [ordCode, hm]
  cases t <;> simp only [ascOrd, ascLayout, orderKind, Option.map_some, Option.map_none, reduceCtorEq,
    Option.some.injEq] at ht
  case u1 =>
    obtain ⟨ha, hb⟩ := hu rfl
    have ha' : a.toNat < 2 := ha
    have hb' : b.toNat < 2 := hb
    have bit : ∀ x : UInt64, x.toNat < 2 → x = 0 ∨ x = 1 := fun x hx => by
      rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with e | e
      · exact .inl (UInt64.toNat_inj.1 (by simpa using e))
      · exact .inr (UInt64.toNat_inj.1 (by simpa using e))
    rcases bit a ha' with rfl | rfl <;> rcases bit b hb' with rfl | rfl <;> subst ht <;> simp only [Column.atomOfBits, QAtom.u1.injEq] <;> decide
  all_goals exact key ht.symm (by decide) (by decide) rfl (by decide)

end Rel.Verify



