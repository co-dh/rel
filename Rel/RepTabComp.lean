import Rel.Run.Comp
import Rel.RepCols
import Rel.RepCanon
import Rel.Run.CRelDef

/-! The laws of `Tab.conv` and `Tab.comp` (`Rel/Run/Comp.lean`), from the five kernels' laws and `Tab.canon_holds`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


/-- A predicate closed under betweenness, least at `a` wherever it holds, and only below `N`, holds exactly on
`[a, a + c)`, `c` the count of its rows below `N`: a group of sorted rows is one run from its first row. -/
theorem interval_count {P : Nat → Bool} {a N : Nat} (hcl : ∀ x y z, x ≤ y → y ≤ z → P x → P z → P y)
    (hlo : ∀ q, P q → a ≤ q) (hN : ∀ q, P q → q < N) (ha : ∀ q, P q → P a) :
    ∀ q, P q ↔ a ≤ q ∧ q < a + (List.range N).countP P := by
  have key : ∀ M, (∀ q < M, (P q ↔ a ≤ q ∧ q < a + (List.range M).countP P)) ∧
      ((List.range M).countP P = 0 ∨ a + (List.range M).countP P ≤ M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [List.range_succ, List.countP_append]
      generalize (List.range M).countP P = c at h1 h2
      by_cases hM : P M
      · have hc' : a + c = M := by
          rcases Nat.eq_zero_or_pos c with h0 | hpos
          · subst h0
            have := hlo M hM
            have hpa := ha M hM
            rcases Nat.lt_or_ge a M with hlt | hge
            · have := (h1 a hlt).1 hpa; omega
            · omega
          · rcases h2 with h2 | h2; · omega
            have hlast : P (a + c - 1) := (h1 (a + c - 1) (by omega)).2 ⟨by omega, by omega⟩
            rcases Nat.lt_or_ge (a + c) M with hlt | hge
            · have := (h1 (a + c) hlt).1 (hcl _ (a + c) M (by omega) (by omega) hlast hM); omega
            · omega
        simp only [List.countP_singleton, hM, if_true]
        refine ⟨fun q hq => ?_, Or.inr (by omega)⟩
        by_cases hqM : q = M
        · subst hqM; exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => hM⟩
        · rw [h1 q (by omega)]; omega
      · simp only [List.countP_singleton, hM, Bool.false_eq_true, if_false, Nat.add_zero]
        refine ⟨fun q hq => ?_, by omega⟩
        by_cases hqM : q = M
        · subst hqM; simp only [hM, Bool.false_eq_true, false_iff]; omega
        · exact h1 q (by omega)
  intro q
  by_cases hq : q < N
  · exact (key N).1 q hq
  · have h := (key N).2
    exact ⟨fun h1 => absurd (hN q h1) hq, fun h3 => by omega⟩

/-- `lexLe` reads its second row only through its codes. -/
theorem lexLe_congr_right : ∀ (ks : List (Array UInt64)) {i j j' : Nat},
    ks.map (·[j]?.getD 0) = ks.map (·[j']?.getD 0) → lexLe ks i j = lexLe ks i j'
  | [], _, _, _, _ => rfl
  | c :: cs, i, j, j', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [lexLe, h.1, lexLe_congr_right cs h.2]

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

/-- Splitting a count by a second predicate. -/
theorem countP_split (p q : Nat → Bool) : ∀ l : List Nat,
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x)
  | [] => rfl
  | x :: l => by
    simp only [List.countP_cons, countP_split p q l]
    cases p x <;> cases q x <;> simp <;> omega

private theorem sum_append_nat : ∀ l1 l2 : List Nat, (l1 ++ l2).sum = l1.sum + l2.sum
  | [], _ => by simp
  | x :: l, l2 => by simp [sum_append_nat l l2, Nat.add_assoc]

/-- **Counting by groups**: where every row's group `gr` is below `K`, the `K` groups' counts of rows with `P` sum
to the count of all rows with `P`. -/
theorem sum_countP_groups (gr : Nat → Nat) (P : Nat → Bool) (l : List Nat) :
    ∀ K, ((List.range K).map fun G => l.countP fun q => gr q == G && P q).sum =
      l.countP fun q => decide (gr q < K) && P q
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.map_append, sum_append_nat, sum_countP_groups gr P l K,
      countP_split (fun q => decide (gr q < K + 1) && P q) (fun q => gr q == K) l]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.add_comm]
    congr 1 <;> apply List.countP_congr <;> intro x _ <;> by_cases h : gr x = K <;>
      simp [h] <;> omega

/-- A word below `2^63` read signed is its `Nat`. -/
theorem toInt64_toInt {x : UInt64} (h : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat := by
  rw [show x.toInt64.toInt = x.toBitVec.toInt from rfl, BitVec.toInt]; simp only [UInt64.toNat_toBitVec]
  omega

/-- Folding `.add` over `0`/`1` words counts the ones. -/
theorem foldl_add_count (P : Nat → Bool) : ∀ (l : List Nat) (a : UInt64),
    (l.map fun q => if P q then (1 : UInt64) else 0).foldl (· + ·) a = a + (l.countP P).toUInt64
  | [], a => by simp
  | q :: l, a => by
    simp only [List.map_cons, List.foldl_cons, foldl_add_count P l, List.countP_cons]
    cases P q <;> simp [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm]

/-- Folding signed `max` over words below `2^63`: the answer is the start or an element, at least each. -/
theorem foldl_max_spec : ∀ (l : List UInt64) (a : UInt64), (∀ x ∈ l, x.toNat < 2 ^ 63) → a.toNat < 2 ^ 63 →
    let r := l.foldl (fun a x => if a.toInt64 < x.toInt64 then x else a) a
    a.toNat ≤ r.toNat ∧ (∀ x ∈ l, x.toNat ≤ r.toNat) ∧ (r = a ∨ r ∈ l)
  | [], a, _, _ => by simp
  | x :: l, a, hl, ha => by
    have hx := hl x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    have hlt : a.toInt64 < x.toInt64 ↔ a.toNat < x.toNat := by
      rw [Int64.lt_iff_toInt_lt, toInt64_toInt ha, toInt64_toInt hx]; omega
    have ha' : (if a.toInt64 < x.toInt64 then x else a).toNat < 2 ^ 63 := by split <;> assumption
    obtain ⟨h1, h2, h3⟩ := foldl_max_spec l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ha'
    have hge : a.toNat ≤ (if a.toInt64 < x.toInt64 then x else a).toNat ∧
        x.toNat ≤ (if a.toInt64 < x.toInt64 then x else a).toNat := by
      split <;> rename_i h <;> rw [hlt] at h <;> omega
    refine ⟨Nat.le_trans hge.1 h1, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Nat.le_trans hge.2 h1
      · exact h2 y hy
    · rcases h3 with e | e
      · rw [e]; split
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ e)

/-- A `Nat` below `2^64` is its word's `Nat`. -/
theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by simp; omega

theorem toInt64_toInt_nat {x : Nat} (h : x < 2 ^ 63) : x.toUInt64.toInt64.toInt = x := by
  rw [toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega)]

/-- The words of `Nat`s below `2^63` under the signed integer ops `comp` runs: `lt`, `max`, `div`, `mod` are `Nat`'s. -/
theorem eval_lt_nat {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    Op.eval .lt x.toUInt64 y.toUInt64 = .ok (if x < y then 1 else 0) := by
  have e : x.toUInt64.toInt64 < y.toUInt64.toInt64 ↔ x < y := by
    rw [Int64.lt_iff_toInt_lt, toInt64_toInt_nat hx, toInt64_toInt_nat hy]; omega
  show Except.ok (if decide (x.toUInt64.toInt64 < y.toUInt64.toInt64) = true then 1 else 0) = _
  simp only [decide_eq_true_eq, e]

theorem eval_max {a x : UInt64} (ha : a.toNat < 2 ^ 63) (hx : x.toNat < 2 ^ 63) :
    Op.eval .max a x = .ok (if a.toNat < x.toNat then x else a) := by
  show Except.ok (if a.toInt64 < x.toInt64 then x else a) = _
  simp only [Int64.lt_iff_toInt_lt, toInt64_toInt ha, toInt64_toInt hx]
  simp

theorem eval_div_nat {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (h0 : 0 < y) :
    Op.eval .div x.toUInt64 y.toUInt64 = .ok (x / y).toUInt64 := by
  have hne : (y.toUInt64 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg UInt64.toNat e; rw [toNat_toUInt64 (by omega)] at this; simp at this; omega
  show (if (y.toUInt64 == 0) = true then Except.error "Op.div: integer division by 0"
    else Except.ok (Int64.ofInt (Int.fdiv x.toUInt64.toInt64.toInt y.toUInt64.toInt64.toInt)).toUInt64) = _
  rw [hne, toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega),
    toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
    ← Int.ofNat_fdiv]
  exact congrArg Except.ok (UInt64.eq_of_toBitVec_eq rfl)

theorem eval_mod_nat {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (h0 : 0 < y) :
    Op.eval .mod x.toUInt64 y.toUInt64 = .ok (x % y).toUInt64 := by
  have hne : (y.toUInt64 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg UInt64.toNat e; rw [toNat_toUInt64 (by omega)] at this; simp at this; omega
  show (if (y.toUInt64 == 0) = true then Except.error "Op.mod: integer remainder by 0"
    else Except.ok (Int64.ofInt (Int.fmod x.toUInt64.toInt64.toInt y.toUInt64.toInt64.toInt)).toUInt64) = _
  rw [hne, toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega),
    toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
    ← Int.ofNat_fmod]
  exact congrArg Except.ok (UInt64.eq_of_toBitVec_eq rfl)

/-- `x - y` of words is `Nat`'s where `y ≤ x`. -/
theorem toUInt64_sub {x y : Nat} (h : y ≤ x) : (x - y).toUInt64 = x.toUInt64 - y.toUInt64 := by
  have e : x = (x - y) + y := by omega
  have e2 := UInt64.ofNat_add (x - y) y; rw [Nat.sub_add_cancel h] at e2
  show UInt64.ofNat (x - y) = UInt64.ofNat x - UInt64.ofNat y; rw [e2, UInt64.add_sub_cancel]

/-- **`kasc`'s grade**: `p` reads as the stable grade `ps` of the codes, and the `kseen` key of sorted row `q` (over
the sorted columns `vs`) is input row `ps[q]`'s. -/
theorem kasc_grade {N : USize} {es : List (QAtomicType × Enc)} {vs : List Enc} {p : Enc}
    (ha : kasc N es = .ok (vs, p)) :
    ∃ cs, es.mapM (ascCol N) = .ok cs ∧
      raw .i64 N p = ((ascGrade N.toNat (ascKeys N es)).map Nat.toUInt64).toArray ∧
      ∀ q (hq : q < (ascGrade N.toNat (ascKeys N es)).length),
        seenKey N ((es.map (·.1)).zip vs) q = seenKey N es (ascGrade N.toNat (ascKeys N es))[q] := by
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm N es vs p ha
  obtain ⟨cs, hc, -, -, -, -, -, hpk⟩ := kasc_ok ha
  rw [ascCol_keys hc] at hpk
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  have hperm' := (ascGrade_spec N.toNat (ascKeys N es)).1
  have hlen' : (ascGrade N.toNat (ascKeys N es)).length = N.toNat := by simpa using hperm'.length_eq
  have hn := N.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < N.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hrp : Enc.raw .i64 N p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hpsg : ps = ascGrade N.toNat (ascKeys N es) := by
    have e : ((ascGrade N.toNat (ascKeys N es)).map Nat.toUInt64).toArray = (ps.map Nat.toUInt64).toArray := by
      rw [← hrp, hpk]; exact ((wordsFoR_closed _ (by simp [hlen'])).2.1).symm
    refine List.ext_getElem (by rw [hlen, hlen']) fun q h1 h2 => ?_
    have e2 := congrArg (fun a : Array UInt64 => a[q]?) e
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at e2
    rw [← hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem h1))),
      ← hc64 _ (List.mem_range.1 (hperm'.mem_iff.1 (List.getElem_mem h2))), e2]
  refine ⟨cs, hc, hpsg ▸ hrp, fun q hq => ?_⟩
  revert hq; rw [← hpsg]; intro hq
  simp only [seenKey, ascKeys, List.map_map]
  apply List.ext_getElem (by simp [hvl])
  intro c h1 h2
  have hc2 : c < es.length := by simpa using h2
  obtain ⟨ws, hv, hws, hwq⟩ := hcol c es[c] (vs[c]'(by omega)) (List.getElem?_eq_getElem hc2)
    (List.getElem?_eq_getElem _)
  simp only [List.getElem_map, List.getElem_zip, Function.comp_apply, hv, (wordsFoR_closed ws hws.symm).2.1,
    Array.getElem?_map, hwq q hq]

/-- **`kscatter (.add)` of `0`/`1` words by group** is each group's count of rows with `P`. -/
theorem scatter_add_count {N K : USize} {g e o : Enc} (h : kscatter .add N g e K 0 = .ok o) (gr : Nat → Nat)
    (P : Nat → Bool) (hg : ∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (gr q).toUInt64)
    (hgr : ∀ q < N.toNat, gr q < 2 ^ 64) (he : ∀ q < N.toNat, (raw .i64 N e)[q]?.getD 0 = if P q then 1 else 0) :
    ∀ G < K.toNat, (raw .i64 K o)[G]?.getD 0 = ((List.range N.toNat).countP fun q => gr q == G && P q).toUInt64 := by
  obtain ⟨hgs, -, hw⟩ := kscatter_words h
  obtain ⟨-, hc⟩ := scatterWords_fold (f := (· + ·)) (fun _ _ => rfl) hw
  intro G hG
  rw [hc G hG, hgs]
  have hf : (List.range N.toNat).filter (fun k => ((raw .i64 N g)[k]?.getD 0).toNat = G) =
      (List.range N.toNat).filter (fun q => gr q == G) := List.filter_congr fun q hq => by
    rw [hg q (List.mem_range.1 hq), toNat_toUInt64 (hgr q (List.mem_range.1 hq))]; by_cases e : gr q = G <;> simp [e]
  rw [hf, List.map_congr_left (g := fun q => if P q then (1 : UInt64) else 0)
    (fun q hq => he q (List.mem_range.1 (List.mem_filter.1 hq).1)), foldl_add_count, List.countP_filter]
  simp [Bool.and_comm]

/-- **`colPrefix (.add)` is the running sum**: where word `G` of `w` is `wN G`, word `G` of the answer is the sum of
`wN` over `0 … G`. -/
theorem colPrefix_add_sum {K : USize} {w P : Enc} (h : colPrefix .add K w = .ok P) (wN : Nat → Nat)
    (hw : ∀ G < K.toNat, (raw .i64 K w)[G]?.getD 0 = (wN G).toUInt64) :
    ∀ G < K.toNat, (raw .i64 K P)[G]?.getD 0 = ((List.range (G + 1)).map wN).sum.toUInt64 := by
  obtain ⟨-, -, hr⟩ := colPrefix_raw h
  intro G hG
  induction G with
  | zero =>
    have := hr 0 hG
    simp only [if_pos rfl, Op.eval, hw 0 hG, Except.ok.injEq] at this
    rw [← this]; simp
  | succ G ih =>
    have := hr (G + 1) hG
    rw [if_neg (by omega), Nat.add_sub_cancel, ih (by omega), hw _ hG] at this
    simp only [Op.eval, Except.ok.injEq] at this
    rw [← this]; simp only [List.range_succ, List.map_append, sum_append_nat, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]; exact (UInt64.ofNat_add _ _).symm

/-- `kscan`'s answer is a `foR` column. -/
theorem kscan_foR {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Enc} {es : List Enc} {o : Enc}
    (h : kscan op rev s t n seg es = .ok o) : ∃ md pk, o = .foR md pk := by
  unfold kscan at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨_, _, h.symm⟩

/-- **`lastCount` reads the last word**: `x` where the last of the `K` words is `x < 2^63`, `0` at `K = 0`. -/
theorem lastCount_eq {K : USize} {P : Enc} (hw : Enc.WF .i64 K P) (hf : ∃ md pk, P = .foR md pk) {x : Nat}
    (hx : x < 2 ^ 63) (hl : 0 < K.toNat → (raw .i64 K P)[K.toNat - 1]?.getD 0 = x.toUInt64)
    (h0 : K.toNat = 0 → x = 0) : lastCount K P hw = x := by
  unfold lastCount
  split
  · rename_i hk
    obtain ⟨md, pk, rfl⟩ := hf
    rw [Arr.get_raw_foR (Arr.mk _ hw) rfl]; change ((raw .i64 K (Enc.foR md pk))[K.toNat - 1]?.getD 0).toInt64.toNatClampNeg = x
    rw [hl hk, ← Int64.toNat_toInt,
      toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega)]
    simp
  · exact (h0 (by omega)).symm

/-- **The group of each output row** (EXPAND): `kscatter (.max)` of the group ids `0 … K-1` at their offsets `oN`,
filled forward by `colPrefix (.max)`: row `t` holds at least every group whose offset is at most `t`, and is `0` or
one of them. -/
theorem expand_groups {K M : USize} {o sc pm : Enc} (hsc : kscatter .max K o .pos M 0 = .ok sc)
    (hpm : colPrefix .max M sc = .ok pm) (oN : Nat → Nat)
    (ho : ∀ G < K.toNat, (raw .i64 K o)[G]?.getD 0 = (oN G).toUInt64) (hoN : ∀ G < K.toNat, oN G < 2 ^ 64)
    (hK : K.toNat < 2 ^ 63) :
    ∀ t < M.toNat, ((raw .i64 M pm)[t]?.getD 0).toNat < 2 ^ 63 ∧
      (∀ G < K.toNat, oN G ≤ t → G ≤ ((raw .i64 M pm)[t]?.getD 0).toNat) ∧
      (((raw .i64 M pm)[t]?.getD 0).toNat = 0 ∨
        ∃ G < K.toNat, oN G ≤ t ∧ ((raw .i64 M pm)[t]?.getD 0).toNat = G) := by
  obtain ⟨hgs, -, hw⟩ := kscatter_words hsc
  obtain ⟨-, hcell⟩ := scatterWords_fold (f := fun a x => if a.toInt64 < x.toInt64 then x else a)
    (fun _ _ => rfl) hw
  obtain ⟨-, -, hpre⟩ := colPrefix_raw hpm
  have hpos : ∀ G < K.toNat, (raw .i64 K (.pos : Enc))[G]?.getD 0 = G.toUInt64 := fun G hG => by
    simp only [raw, Array.getElem?_map, Array.getElem?_range, hG, if_true, Option.map_some, Option.getD_some]
  -- each cell holds the largest group whose offset is exactly that cell
  have cell : ∀ x < M.toNat, ((raw .i64 M sc)[x]?.getD 0).toNat < 2 ^ 63 ∧
      (∀ G < K.toNat, oN G = x → G ≤ ((raw .i64 M sc)[x]?.getD 0).toNat) ∧
      (((raw .i64 M sc)[x]?.getD 0).toNat = 0 ∨
        ∃ G < K.toNat, oN G = x ∧ ((raw .i64 M sc)[x]?.getD 0).toNat = G) := by
    intro x hx
    rw [hcell x hx]
    have hmem : ∀ y ∈ (((List.range (raw .i64 K o).size).filter fun k => ((raw .i64 K o)[k]?.getD 0).toNat = x).map
        ((raw .i64 K (.pos : Enc))[·]?.getD 0)), ∃ G < K.toNat, oN G = x ∧ y = G.toUInt64 := by
      intro y hy
      obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hy
      obtain ⟨hG1, hG2⟩ := List.mem_filter.1 hG
      have hGK : G < K.toNat := by rw [List.mem_range, hgs] at hG1; exact hG1
      rw [ho G hGK, toNat_toUInt64 (hoN G hGK)] at hG2
      exact ⟨G, hGK, of_decide_eq_true hG2, hpos G hGK⟩
    obtain ⟨-, h2, h3⟩ := foldl_max_spec _ 0 (fun y hy => by
      obtain ⟨G, hG, -, rfl⟩ := hmem y hy; rw [toNat_toUInt64 (by omega)]; omega) (by decide)
    refine ⟨?_, fun G hG hGx => ?_, ?_⟩
    · rcases h3 with e | e
      · rw [e]; decide
      · obtain ⟨G, hG, -, e'⟩ := hmem _ e; rw [e', toNat_toUInt64 (by omega)]; omega
    · have := h2 G.toUInt64 (List.mem_map.2 ⟨G, List.mem_filter.2 ⟨List.mem_range.2 (by rw [hgs]; exact hG),
        by rw [ho G hG, toNat_toUInt64 (hoN G hG)]; simp [hGx]⟩, hpos G hG⟩)
      rwa [toNat_toUInt64 (by omega)] at this
    · rcases h3 with e | e
      · exact Or.inl (by rw [e]; rfl)
      · obtain ⟨G, hG, hGx, e'⟩ := hmem _ e
        exact Or.inr ⟨G, hG, hGx, by rw [e', toNat_toUInt64 (by omega)]⟩
  -- one step of the running max from the previous row's value `pv`
  have step : ∀ t < M.toNat, ∀ pv : UInt64, pv.toNat < 2 ^ 63 → (∀ G < K.toNat, oN G < t → G ≤ pv.toNat) →
      (pv.toNat = 0 ∨ ∃ G < K.toNat, oN G < t ∧ pv.toNat = G) →
      Op.eval .max pv ((raw .i64 M sc)[t]?.getD 0) = .ok ((raw .i64 M pm)[t]?.getD 0) →
      ((raw .i64 M pm)[t]?.getD 0).toNat < 2 ^ 63 ∧
      (∀ G < K.toNat, oN G ≤ t → G ≤ ((raw .i64 M pm)[t]?.getD 0).toNat) ∧
      (((raw .i64 M pm)[t]?.getD 0).toNat = 0 ∨
        ∃ G < K.toNat, oN G ≤ t ∧ ((raw .i64 M pm)[t]?.getD 0).toNat = G) := by
    intro t ht pv h1 h2 h3 e
    obtain ⟨c1, c2, c3⟩ := cell t ht
    rw [eval_max h1 c1, Except.ok.injEq] at e
    generalize (raw .i64 M pm)[t]?.getD 0 = r at e ⊢
    generalize (raw .i64 M sc)[t]?.getD 0 = c at e c1 c2 c3
    subst e
    split
    · rename_i hlt
      refine ⟨c1, fun G hG hGt => ?_, ?_⟩
      · rcases Nat.lt_or_ge (oN G) t with h | h
        · have := h2 G hG h; omega
        · exact c2 G hG (by omega)
      · rcases c3 with e | ⟨G, hG, hGx, e⟩
        · exact Or.inl e
        · exact Or.inr ⟨G, hG, by omega, e⟩
    · rename_i hlt
      refine ⟨h1, fun G hG hGt => ?_, ?_⟩
      · rcases Nat.lt_or_ge (oN G) t with h | h
        · exact h2 G hG h
        · have := c2 G hG (by omega); omega
      · rcases h3 with e | ⟨G, hG, hGx, e⟩
        · exact Or.inl e
        · exact Or.inr ⟨G, hG, by omega, e⟩
  intro t ht
  induction t with
  | zero =>
    have e := hpre 0 ht
    simp only [if_pos rfl] at e
    exact step 0 ht 0 (by decide) (fun _ _ h => absurd h (Nat.not_lt_zero _)) (Or.inl rfl) e
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    have e := hpre (t + 1) ht
    rw [if_neg (by omega), Nat.add_sub_cancel] at e
    refine step (t + 1) ht _ i1 (fun G hG h => i2 G hG (by omega)) ?_ e
    rcases i3 with e3 | ⟨G, hG, hGx, e3⟩
    · exact Or.inl e3
    · exact Or.inr ⟨G, hG, by omega, e3⟩


/-- **A group of stably sorted rows** (`kasc ≫ kseen`): sorted row `q` is input row `ps[q]`, its key `Kk q` that row's
codes. Group `G` is the run of `cnt` sorted rows from its first row `F[G]`, and, the sort being stable, its rows from
input rows below `n` are the first `cR` of them. -/
theorem sorted_groups {N n : Nat} {ps : List Nat} {ks : List (Array UInt64)} {Kk : Nat → List UInt64}
    (hlen : ps.length = N) (hsort : ps.Pairwise fun i j => lexLe ks i j = true ∧ (lexLe ks j i = true → i < j))
    (hkey : ∀ q (hq : q < ps.length), Kk q = ks.map (·[ps[q]]?.getD 0)) {G : Nat}
    (hG : G < (firstsOf Kk N).length) :
    (∀ q, (q < N ∧ Verify.groupOf Kk N q = G) ↔ (firstsOf Kk N)[G] ≤ q ∧
      q < (firstsOf Kk N)[G] + (List.range N).countP (fun q => Verify.groupOf Kk N q == G && true)) ∧
    (∀ q, (q < N ∧ Verify.groupOf Kk N q = G ∧ ps[q]?.getD 0 < n) ↔ (firstsOf Kk N)[G] ≤ q ∧
      q < (firstsOf Kk N)[G] + (List.range N).countP (fun q => Verify.groupOf Kk N q == G && decide (ps[q]?.getD 0 < n))) := by
  have fs := firsts_spec Kk N
  have hF : (firstsOf Kk N)[G] < N := firsts_lt Kk N (List.getElem_mem hG)
  have hgF : Verify.groupOf Kk N (firstsOf Kk N)[G] = G := fs.2.2.2.1 G hG
  have hlo : ∀ q < N, Verify.groupOf Kk N q = G → (firstsOf Kk N)[G] ≤ q := fun q hq e => by
    obtain ⟨_, h1, -⟩ := fs.2.2.2.2.2 q hq; simp only [e] at h1; exact h1
  have hps : ∀ q (hq : q < N), ps[q]?.getD 0 = ps[q]'(by omega) := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  -- equal keys keep the input order; a key's rows are one run
  have stab : ∀ a b, a < b → b < N → Kk a = Kk b → ps[a]?.getD 0 < ps[b]?.getD 0 := fun a b hab hb e => by
    rw [hps a (by omega), hps b hb]
    rw [hkey a (by omega), hkey b (by omega)] at e
    exact (List.pairwise_iff_getElem.1 hsort a b (by omega) (by omega) hab).2 (lexLe_of_keys ks e.symm)
  have contig : ∀ a b c, a ≤ b → b ≤ c → c < N → Kk a = Kk c → Kk b = Kk a := fun a b c hab hbc hc e => by
    rcases Nat.lt_or_eq_of_le hab with hab | rfl
    · rcases Nat.lt_or_eq_of_le hbc with hbc | rfl
      · have l1 := (List.pairwise_iff_getElem.1 hsort a b (by omega) (by omega) hab).1
        have l2 := (List.pairwise_iff_getElem.1 hsort b c (by omega) (by omega) hbc).1
        rw [hkey a (by omega), hkey c (by omega)] at e
        rw [lexLe_congr_right ks e.symm] at l2
        rw [hkey a (by omega), hkey b (by omega)]
        exact (keys_of_lexLe ks l1 l2).symm
      · exact e.symm
    · rfl
  have grp : ∀ x y z, x ≤ y → y ≤ z → z < N → Verify.groupOf Kk N x = G → Verify.groupOf Kk N z = G →
      Verify.groupOf Kk N y = G := fun x y z hxy hyz hz ex ez => by
    have e := (fs.2.2.1 x (by omega) z hz).1 (ex.trans ez.symm)
    rw [← ex]; exact (fs.2.2.1 y (by omega) x (by omega)).2 (contig x y z hxy hyz hz e)
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have := interval_count (P := fun q => decide (q < N) && (Verify.groupOf Kk N q == G)) (a := (firstsOf Kk N)[G]) (N := N)
      (fun x y z hxy hyz hx hz => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx hz ⊢
        exact ⟨by omega, grp x y z hxy hyz hz.1 hx.2 hz.2⟩)
      (fun q hq => by simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq; exact hlo q hq.1 hq.2)
      (fun q hq => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hq; exact hq.1)
      (fun _ _ => by simp [hF, hgF]) q
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rw [this, List.countP_congr (q := fun q => Verify.groupOf Kk N q == G && true) fun x hx => by
      simp [List.mem_range.1 hx]]
  · have := interval_count (P := fun q => decide (q < N) && (Verify.groupOf Kk N q == G) && decide (ps[q]?.getD 0 < n))
      (a := (firstsOf Kk N)[G]) (N := N)
      (fun x y z hxy hyz hx hz => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx hz ⊢
        have gy := grp x y z hxy hyz hz.1.1 hx.1.2 hz.1.2
        refine ⟨⟨by omega, gy⟩, ?_⟩
        rcases Nat.lt_or_eq_of_le hyz with h | rfl
        · have := stab y z h hz.1.1 ((fs.2.2.1 y (by omega) z hz.1.1).1 (gy.trans hz.1.2.symm)); omega
        · exact hz.2)
      (fun q hq => by simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq; exact hlo q hq.1.1 hq.1.2)
      (fun q hq => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hq; exact hq.1.1)
      (fun q hq => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq ⊢
        refine ⟨⟨hF, hgF⟩, ?_⟩
        rcases Nat.lt_or_eq_of_le (hlo q hq.1.1 hq.1.2) with h | e
        · have := stab _ q h hq.1.1 ((fs.2.2.1 _ hF q hq.1.1).1 (hgF.trans hq.1.2.symm)); omega
        · rw [e]; exact hq.2) q
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rw [← and_assoc, this, List.countP_congr
      (q := fun q => Verify.groupOf Kk N q == G && decide (ps[q]?.getD 0 < n)) fun x hx => by simp [List.mem_range.1 hx]]

/-- `n` of the first `M` rows lie below `n ≤ M`. -/
theorem countP_range_lt (n : Nat) : ∀ M, (List.range M).countP (fun q => decide (q < n)) = min M n
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_lt n M]
    by_cases h : M < n <;> simp [h] <;> omega

/-- Summing products whose right factors are at most `m`. -/
theorem sum_mul_le (a b : Nat → Nat) (m : Nat) (hb : ∀ G, b G ≤ m) :
    ∀ k, ((List.range k).map fun G => a G * b G).sum ≤ m * ((List.range k).map a).sum
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, sum_append_nat, sum_append_nat, Nat.mul_add]
    have := sum_mul_le a b m hb k
    have := Nat.mul_le_mul_left (a k) (hb k)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.mul_comm m (a k)]; omega


namespace Tab
variable {A B C : Obj}

/-- **`R.conv` denotes `R°`** (`Rep.rep_conv`'s statement, pointwise). -/
theorem conv_holds {R : Tab A B} {S : Tab B A} (h : R.conv = .ok S) (b : B.El) (a : A.El) :
    S.Holds b a ↔ R.Holds a b := by
  rw [canon_holds h]; exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks


#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2)]).conv.toOption.map Tab.toList) == some [(1, 3), (2, -1), (2, 1)]
#guard ((tab [(3, 1), (1, 2), (-1, 2), (1, 2)]).comp (tab [(2, 5), (1, -3), (2, 6), (7, 7)])).toOption.map Tab.toList ==
  some [(-1, 5), (-1, 6), (1, 5), (1, 6), (3, -3)]
-- the five-kernel `comp` and `conv` against the old `CRel.comp` and `ofC (R°)` on the same tables: duplicates,
-- negatives, an empty side, no common middle value, a group whose run product is past 1
#guard
  let ts : List (List (Int64 × Int64)) := [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
    [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], [(4, 8)], []]
  ts.all fun ps => (ts.all fun qs => ((tab ps).comp (tab qs)).toOption.isSome &&
    ((tab ps).comp (tab qs)).toOption.map Tab.toList == (CRel.comp (some (tab ps)) (some (tab qs))).map Tab.toList) &&
    (tab ps).conv.toOption.isSome && ((tab ps).conv.toOption.map Tab.toList) ==
      (let c := Alg.canonC (⟨(tab ps).n, (tab ps).val, (tab ps).key⟩ : Tab .long .long)
       if c.2 then some c.1.toList else none)

end Checks

#print axioms Tab.conv_holds

end Rel
