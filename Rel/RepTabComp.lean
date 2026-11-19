import Rel.Run.Comp
import Rel.Run.SetOps
import Rel.Run.CRelFoldDef
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

/-- Word `t` of the index column `.pos` is `t`. -/
theorem raw_pos_word {n : USize} {t : Nat} (ht : t < n.toNat) : (raw .i64 n (.pos : Enc))[t]?.getD 0 = t.toUInt64 := by
  simp only [raw, Array.getElem?_map, Array.getElem?_range, ht, if_true, Option.map_some, Option.getD_some]

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
      exact ⟨G, hGK, of_decide_eq_true hG2, raw_pos_word hGK⟩
    obtain ⟨-, h2, h3⟩ := foldl_max_spec _ 0 (fun y hy => by
      obtain ⟨G, hG, -, rfl⟩ := hmem y hy; rw [toNat_toUInt64 (by omega)]; omega) (by decide)
    refine ⟨?_, fun G hG hGx => ?_, ?_⟩
    · rcases h3 with e | e
      · rw [e]; decide
      · obtain ⟨G, hG, -, e'⟩ := hmem _ e; rw [e', toNat_toUInt64 (by omega)]; omega
    · have := h2 G.toUInt64 (List.mem_map.2 ⟨G, List.mem_filter.2 ⟨List.mem_range.2 (by rw [hgs]; exact hG),
        by rw [ho G hG, toNat_toUInt64 (hoN G hG)]; simp [hGx]⟩, raw_pos_word hG⟩)
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

theorem sum_range_succ' (f : Nat → Nat) (j : Nat) :
    ((List.range (j + 1)).map f).sum = ((List.range j).map f).sum + f j := by
  rw [List.range_succ, List.map_append, sum_append_nat]; simp

theorem sum_range_mono (f : Nat → Nat) {i : Nat} : ∀ {j}, i ≤ j →
    ((List.range i).map f).sum ≤ ((List.range j).map f).sum
  | 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | j + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [sum_range_succ']; have := sum_range_mono f (i := i) (j := j) (by omega); omega
    · exact Nat.le_refl _

/-- A row below the total of `k` widths lies in one group's run of widths. -/
theorem exists_group (f : Nat → Nat) : ∀ k t, t < ((List.range k).map f).sum →
    ∃ G < k, ((List.range G).map f).sum ≤ t ∧ t < ((List.range G).map f).sum + f G
  | 0, t, h => by simp at h
  | k + 1, t, h => by
    rw [sum_range_succ'] at h
    by_cases ht : t < ((List.range k).map f).sum
    · obtain ⟨G, hG, h1, h2⟩ := exists_group f k t ht; exact ⟨G, by omega, h1, h2⟩
    · exact ⟨k, by omega, by omega, h⟩

/-- **`kgather` on words**: row `j` of the answer is word `ix[j]` of `e`, and `ix[j]` is below `n`. -/
theorem kgather_word {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) :
    ∀ j < m.toNat, ((raw .i64 m ix)[j]?.getD 0).toNat < n.toNat ∧
      (raw .i64 m o)[j]?.getD 0 = (raw .i64 n e)[((raw .i64 m ix)[j]?.getD 0).toNat]?.getD 0 := by
  obtain ⟨his, -, hlt, ho⟩ := raw_kgather m ix n e o h
  intro j hj
  refine ⟨hlt j hj, ?_⟩
  rw [ho, (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1]
  simp [Array.getElem?_eq_getElem (show j < (raw .i64 m ix).size by omega)]

theorem Except.bind_eq_ok' {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β} :
    e.bind f = .ok b ↔ ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e <;> simp [Except.bind]

/-- **`R.comp S` is `canon` of a table denoting `R ≫ S`**: so `T` holds `R ≫ S` (`Tab.comp_holds`) and is sorted
without duplicates (`Tab.canon_sorted` at `U`). -/
theorem Tab.comp_canon {A B C : Obj}
    {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : R.comp S = .ok T) :
    ∃ U : Tab A C, U.canon = .ok T ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  dsimp only [Tab.comp] at h
  split at h; · cases h
  rename_i hnm
  simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, hcat, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cn, hcn, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cR, hcR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cS, hcS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  split at h; · cases h
  rename_i P hP
  split at h; · cases h
  rename_i hTU
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  have hPf : ∃ md pk, P = .foR md pk := by
    unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
    exact kscan_foR hP
  generalize hT : lastCount _ P _ = Tn at h hTU
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, ho, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pm, hpm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Gc, hGc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ft, hft, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨og, hog, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨u, hu, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ct, hct, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dv, hdv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ir, hir, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iR, hiR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cr, hcr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a1, ha1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨md, hmd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨qS, hqS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pq, hpq, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c3, hc3, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iS, hiS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X, hX, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
  refine ⟨_, h, fun a c => ?_⟩
  ------------------------------------------------------------------ the sorted rows and their groups
  obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  obtain ⟨cs, hcs, hp, hkq⟩ := kasc_grade hasc
  obtain ⟨hperm, hsort⟩ := ascGrade_spec N.toNat (ascKeys N es)
  obtain ⟨hk, hg, hf⟩ := kseen_ok hseen
  generalize ascGrade N.toNat (ascKeys N es) = ps at hp hkq hperm hsort
  generalize seenKey N ((es.map (·.1)).zip vs) = Kk at hk hg hf hkq
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  have hpsN : ∀ q < N.toNat, ps[q]?.getD 0 < N.toNat := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hkN : k ≤ N.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hpw : ∀ q < N.toNat, (raw .i64 N p)[q]?.getD 0 = (ps[q]?.getD 0).toUInt64 := fun q hq => by
    rw [hp]; simp [List.getElem?_eq_getElem (show q < ps.length by omega)]
  have hgw : ∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (Verify.groupOf Kk N.toNat q).toUInt64 := fun q hq => by
    rw [hg, (wordsFoR_closed _ (by simp)).2.1]; simp [hq]
  have hfw : ∀ G < k, (raw .i64 k.toUSize f)[G]?.getD 0 = ((firstsOf Kk N.toNat)[G]?.getD 0).toUInt64 :=
    fun G hG => by
      rw [hf, (wordsFoR_closed _ (by rw [hK, hk]; simp)).2.1]
      simp [List.getElem?_eq_getElem (show G < (firstsOf Kk N.toNat).length by omega)]
  have hgr : ∀ q < N.toNat, Verify.groupOf Kk N.toNat q < k := fun q hq => by
    have := groupOf_lt (g := Kk) (m := N.toNat) hq; omega
  ------------------------------------------------------------------ per group: `cR`, `cS`, `w`, `P`, `o`
  have hnU : R.n.toUInt64 = R.n.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
  have hltw : ∀ q < N.toNat, (raw .i64 N lt)[q]?.getD 0 =
      if decide (ps[q]?.getD 0 < R.n.toNat) then 1 else 0 := fun q hq => by
    have e := (colMap_raw hlt).2.2.2 q hq
    rw [hpw q hq, colConst_raw hcn, Array.getElem?_replicate, if_pos hq, Option.getD_some, hnU,
      eval_lt_nat (by have := hpsN q hq; omega) (by omega), Except.ok.injEq] at e
    rw [← e]; simp
  obtain ⟨cRN, hcRN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && decide (ps[q]?.getD 0 < R.n.toNat) := ⟨_, rfl⟩
  obtain ⟨cntN, hcntN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && true := ⟨_, rfl⟩
  have hcRw : ∀ G < k, (raw .i64 k.toUSize cR)[G]?.getD 0 = (cRN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcR (Verify.groupOf Kk N.toNat) (fun q => decide (ps[q]?.getD 0 < R.n.toNat)) hgw
      (fun q hq => by have := hgr q hq; omega) hltw G (by omega), hcRN]
  have hcntw : ∀ G < k, (raw .i64 k.toUSize cnt)[G]?.getD 0 = (cntN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcnt (Verify.groupOf Kk N.toNat) (fun _ => true) hgw
      (fun q hq => by have := hgr q hq; omega) (fun q hq => by rw [colConst_raw hc1]; simp [hq]) G (by omega), hcntN]
  have hle : ∀ G, cRN G ≤ cntN G := fun G => by
    rw [hcRN, hcntN]; exact List.countP_mono_left fun x _ hx => by simp at hx ⊢; exact hx.1
  have hmap : (List.range N.toNat).map (fun q => ps[q]?.getD 0) = ps :=
    List.ext_getElem (by simp [hlen]) fun i h1 h2 => by simp [List.getElem?_eq_getElem h2]
  have hcntR : (List.range N.toNat).countP (fun q => decide (ps[q]?.getD 0 < R.n.toNat)) = R.n.toNat := by
    have := List.countP_map (p := fun x => decide (x < R.n.toNat)) (f := fun q => ps[q]?.getD 0)
      (l := List.range N.toNat)
    rw [hmap, hperm.countP_eq, countP_range_lt] at this
    rw [show (fun q => decide (ps[q]?.getD 0 < R.n.toNat)) =
      (fun x => decide (x < R.n.toNat)) ∘ (fun q => ps[q]?.getD 0) from rfl, ← this]; omega
  have hsumR : ((List.range k).map cRN).sum = R.n.toNat := by
    have := sum_countP_groups (Verify.groupOf Kk N.toNat) (fun q => decide (ps[q]?.getD 0 < R.n.toNat))
      (List.range N.toNat) k
    simp only at this
    rw [hcRN, this]
    exact (List.countP_congr fun q hq => by simp [hgr q (List.mem_range.1 hq)]).trans hcntR
  have hbm : ∀ G, cntN G - cRN G ≤ S.n.toNat := fun G => by
    have h1 := countP_split (fun q => Verify.groupOf Kk N.toNat q == G && true)
      (fun q => decide (ps[q]?.getD 0 < R.n.toNat)) (List.range N.toNat)
    have h2 := countP_split (fun _ => true) (fun q => decide (ps[q]?.getD 0 < R.n.toNat)) (List.range N.toNat)
    have h3 : (List.range N.toNat).countP (fun q => (Verify.groupOf Kk N.toNat q == G && true) &&
        !decide (ps[q]?.getD 0 < R.n.toNat)) ≤
        (List.range N.toNat).countP (fun q => true && !decide (ps[q]?.getD 0 < R.n.toNat)) :=
      List.countP_mono_left fun x _ hx => by simp at hx ⊢; exact hx.2
    have h4 : (List.range N.toNat).countP (fun q => (Verify.groupOf Kk N.toNat q == G && true) &&
        decide (ps[q]?.getD 0 < R.n.toNat)) = cRN G := by
      rw [hcRN]; exact List.countP_congr fun x _ => by simp
    have h5 : (List.range N.toNat).countP (fun q => true && decide (ps[q]?.getD 0 < R.n.toNat)) = R.n.toNat := by
      exact (List.countP_congr fun x _ => by simp).trans hcntR
    have h6 : (List.range N.toNat).countP (fun _ => true) = N.toNat := by simp
    have h7 : cntN G = (List.range N.toNat).countP (fun q => Verify.groupOf Kk N.toNat q == G && true) := by
      rw [hcntN]
    omega
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, F = fun G => cRN G * (cntN G - cRN G) := ⟨_, rfl⟩
  have hSk : ((List.range k).map wN).sum ≤ R.n.toNat * S.n.toNat := by
    have := sum_mul_le cRN (fun G => cntN G - cRN G) S.n.toNat hbm k
    rw [hsumR, Nat.mul_comm S.n.toNat] at this; rw [hwN]; exact this
  have hS63 : ∀ j, ((List.range j).map wN).sum ≤ ((List.range k).map wN).sum ∨ k ≤ j := fun j => by
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact Or.inl (sum_range_mono wN (by omega))
    · exact Or.inr (by omega)
  have hcSw : ∀ G < k, (raw .i64 k.toUSize cS)[G]?.getD 0 = (cntN G - cRN G).toUInt64 := fun G hG => by
    have e := (colMap_raw hcS).2.2.2 G (by omega)
    rw [hcntw G hG, hcRw G hG] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, toUInt64_sub (hle G)]
  have hww : ∀ G < k, (raw .i64 k.toUSize w)[G]?.getD 0 = (wN G).toUInt64 := fun G hG => by
    have e := (colMap_raw hw).2.2.2 G (by omega)
    rw [hcRw G hG, hcSw G hG] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, hwN]; exact (UInt64.ofNat_mul _ _).symm
  have hPw : ∀ G < k, (raw .i64 k.toUSize P)[G]?.getD 0 = ((List.range (G + 1)).map wN).sum.toUInt64 :=
    fun G hG => colPrefix_add_sum hP wN (fun G hG => hww G (by omega)) G (by omega)
  have hTn : Tn = ((List.range k).map wN).sum := hT.symm.trans (lastCount_eq _ hPf (by omega)
    (fun hk0 => by rw [hK] at hk0 ⊢; rw [hPw (k - 1) (by omega), Nat.sub_add_cancel hk0])
    (fun hk0 => by rw [hK] at hk0; subst hk0; rfl))
  have how : ∀ G < k, (raw .i64 k.toUSize o)[G]?.getD 0 = ((List.range G).map wN).sum.toUInt64 := fun G hG => by
    have e := (colMap_raw ho).2.2.2 G (by omega)
    rw [hPw G hG, hww G hG, sum_range_succ'] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, ← toUInt64_sub (by omega), Nat.add_sub_cancel]
  ------------------------------------------------------------------ each output row's group (EXPAND)
  obtain ⟨Sw, hSw⟩ : ∃ F : Nat → Nat, ∀ G, F G = ((List.range G).map wN).sum := ⟨_, fun _ => rfl⟩
  obtain ⟨bN, hbN⟩ : ∃ F : Nat → Nat, ∀ G, F G = cntN G - cRN G := ⟨_, fun _ => rfl⟩
  obtain ⟨Fs, hFs⟩ : ∃ F : Nat → Nat, ∀ G, F G = (firstsOf Kk N.toNat)[G]?.getD 0 := ⟨_, fun _ => rfl⟩
  have hn63 : R.n.toNat * S.n.toNat + R.n.toNat + S.n.toNat < 2 ^ 63 := by omega
  have hTn' : Tn = Sw k := by rw [hSw]; exact hTn
  have hTk : Sw k ≤ R.n.toNat * S.n.toNat := by rw [hSw]; exact hSk
  have hTT : Tn.toUSize.toNat = Tn := USize.toNat_ofNat_of_lt' (by omega)
  have hT1 : (Tn.toUSize + 1).toNat = Tn + 1 := by
    rw [USize.toNat_add, hTT]; simp only [USize.toNat_one]; exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; omega)
  have hSwm : ∀ G G', G < G' → Sw G + wN G ≤ Sw G' := fun G G' hG => by
    rw [hSw, hSw, ← sum_range_succ']; exact sum_range_mono wN hG
  have hSwk : ∀ G ≤ k, Sw G ≤ Sw k := fun G hG => by rw [hSw, hSw]; exact sum_range_mono wN hG
  have hGw : ∀ t G, G < k → Sw G ≤ t → t < Sw G + wN G →
      (raw .i64 Tn.toUSize Gc)[t]?.getD 0 = G.toUInt64 := by
    intro t G hG h1 h2
    have := hSwm G k hG
    obtain ⟨-, e⟩ := kgather_word hGc t (by omega)
    rw [raw_pos_word (by omega), toNat_toUInt64 (by omega)] at e
    rw [e]
    obtain ⟨-, lo, alt⟩ := expand_groups hsc hpm Sw (fun G hG => by rw [hSw]; exact how G (by omega))
      (fun G hG => by have := hSwk G (by omega); omega) (by omega) t (by omega)
    have lo' := lo G (by omega) h1
    have hx : ((raw .i64 (Tn.toUSize + 1) pm)[t]?.getD 0).toNat = G := by
      rcases alt with e0 | ⟨G', hG', h3, e3⟩
      · omega
      · rcases Nat.lt_or_ge G G' with hl | hl
        · have := hSwm G G' hl; omega
        · omega
    rw [← hx]; simp
  ------------------------------------------------------------------ each output row's input rows
  have hgath : ∀ {e o : Enc} (fN : Nat → Nat), kgather Tn.toUSize Gc k.toUSize e = .ok o →
      (∀ G < k, (raw .i64 k.toUSize e)[G]?.getD 0 = (fN G).toUInt64) →
      ∀ t G, G < k → Sw G ≤ t → t < Sw G + wN G → (raw .i64 Tn.toUSize o)[t]?.getD 0 = (fN G).toUInt64 := by
    intro e o fN hg he t G hG h1 h2
    have := hSwm G k hG
    rw [(kgather_word hg t (by omega)).2, hGw t G hG h1 h2, toNat_toUInt64 (by omega), he G hG]
  have hps : ∀ q (hq : q < N.toNat), ps[q]?.getD 0 = ps[q]'(by omega) := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  have sg : ∀ G < k, (∀ q, (q < N.toNat ∧ Verify.groupOf Kk N.toNat q = G) ↔ Fs G ≤ q ∧ q < Fs G + cntN G) ∧
      (∀ q, (q < N.toNat ∧ Verify.groupOf Kk N.toNat q = G ∧ ps[q]?.getD 0 < R.n.toNat) ↔
        Fs G ≤ q ∧ q < Fs G + cRN G) := by
    intro G hG
    have hG' : G < (firstsOf Kk N.toNat).length := by omega
    have := sorted_groups (n := R.n.toNat) hlen hsort (fun q hq => by rw [hkq q hq]; simp [seenKey, ascKeys]) hG'
    rw [hFs, List.getElem?_eq_getElem hG', Option.getD_some, hcntN, hcRN]; exact this
  have hrw : ∀ t G, G < k → Sw G ≤ t → t < Sw G + wN G →
      (raw .i64 Tn.toUSize iR)[t]?.getD 0 = (ps[Fs G + (t - Sw G) / bN G]?.getD 0).toUInt64 ∧
      (raw .i64 Tn.toUSize iS)[t]?.getD 0 =
        (ps[Fs G + cRN G + (t - Sw G) % bN G]?.getD 0 - R.n.toNat).toUInt64 ∧
      (Fs G + (t - Sw G) / bN G < N.toNat ∧ Verify.groupOf Kk N.toNat (Fs G + (t - Sw G) / bN G) = G ∧
        ps[Fs G + (t - Sw G) / bN G]?.getD 0 < R.n.toNat) ∧
      (Fs G + cRN G + (t - Sw G) % bN G < N.toNat ∧
        Verify.groupOf Kk N.toNat (Fs G + cRN G + (t - Sw G) % bN G) = G ∧
        R.n.toNat ≤ ps[Fs G + cRN G + (t - Sw G) % bN G]?.getD 0) := by
    intro t G hG h1 h2
    have hkG := hSwm G k hG
    have hw' : wN G = cRN G * bN G := by rw [hwN, hbN]
    have hb0 : 0 < bN G := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hw'; omega
    have hr : (t - Sw G) / bN G < cRN G := (Nat.div_lt_iff_lt_mul hb0).2 (by rw [← hw']; omega)
    have hs := Nat.mod_lt (t - Sw G) hb0
    have hbm' : bN G ≤ S.n.toNat := hbN G ▸ hbm G
    have hbG := hbN G
    have hle' := hle G
    obtain ⟨sgA, sgR⟩ := sg G hG
    have hcN : Fs G + cntN G ≤ N.toNat := by have := (sgA (Fs G + cntN G - 1)).2 ⟨by omega, by omega⟩; omega
    have htT : t < Tn.toUSize.toNat := by omega
    have wft := hgath Fs hft (fun G hG => by rw [hFs]; exact hfw G hG) t G hG h1 h2
    have wog := hgath Sw hog (fun G hG => by rw [hSw]; exact how G hG) t G hG h1 h2
    have wct := hgath bN hct (fun G hG => by rw [hbN]; exact hcSw G hG) t G hG h1 h2
    have wcr := hgath cRN hcr hcRw t G hG h1 h2
    have wu : (raw .i64 Tn.toUSize u)[t]?.getD 0 = (t - Sw G).toUInt64 := by
      have e := (colMap_raw hu).2.2.2 t htT
      rw [raw_pos_word htT, wog] at e; simp only [Op.eval, Except.ok.injEq] at e
      rw [← e, toUInt64_sub h1]
    have wdv : (raw .i64 Tn.toUSize dv)[t]?.getD 0 = ((t - Sw G) / bN G).toUInt64 := by
      have e := (colMap_raw hdv).2.2.2 t htT
      rw [wu, wct, eval_div_nat (by omega) (by omega) hb0, Except.ok.injEq] at e; exact e.symm
    have wmd : (raw .i64 Tn.toUSize md)[t]?.getD 0 = ((t - Sw G) % bN G).toUInt64 := by
      have e := (colMap_raw hmd).2.2.2 t htT
      rw [wu, wct, eval_mod_nat (by omega) (by omega) hb0, Except.ok.injEq] at e; exact e.symm
    have wir : (raw .i64 Tn.toUSize ir)[t]?.getD 0 = (Fs G + (t - Sw G) / bN G).toUInt64 := by
      have e := (colMap_raw hir).2.2.2 t htT
      rw [wft, wdv] at e; simp only [Op.eval, Except.ok.injEq] at e
      rw [← e]; exact (UInt64.ofNat_add _ _).symm
    have wa1 : (raw .i64 Tn.toUSize a1)[t]?.getD 0 = (Fs G + cRN G).toUInt64 := by
      have e := (colMap_raw ha1).2.2.2 t htT
      rw [wft, wcr] at e; simp only [Op.eval, Except.ok.injEq] at e
      rw [← e]; exact (UInt64.ofNat_add _ _).symm
    have wqS : (raw .i64 Tn.toUSize qS)[t]?.getD 0 = (Fs G + cRN G + (t - Sw G) % bN G).toUInt64 := by
      have e := (colMap_raw hqS).2.2.2 t htT
      rw [wa1, wmd] at e; simp only [Op.eval, Except.ok.injEq] at e
      rw [← e]; exact (UInt64.ofNat_add _ _).symm
    have wiR := (kgather_word hiR t htT).2
    rw [wir, toNat_toUInt64 (by omega), hpw _ (by omega)] at wiR
    have wpq := (kgather_word hpq t htT).2
    rw [wqS, toNat_toUInt64 (by omega), hpw _ (by omega)] at wpq
    have qRg := (sgR (Fs G + (t - Sw G) / bN G)).2 ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hr _⟩
    have qSg := (sgA (Fs G + cRN G + (t - Sw G) % bN G)).2 ⟨by omega, by omega⟩
    have hnps : R.n.toNat ≤ ps[Fs G + cRN G + (t - Sw G) % bN G]?.getD 0 :=
      Nat.le_of_not_lt fun hc => by have := (sgR _).1 ⟨qSg.1, qSg.2, hc⟩; omega
    refine ⟨wiR, ?_, qRg, qSg.1, qSg.2, hnps⟩
    have e := (colMap_raw hiS).2.2.2 t htT
    rw [wpq, colConst_raw hc3, Array.getElem?_replicate, if_pos htT, Option.getD_some, hnU] at e
    simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, toUInt64_sub hnps]
  ------------------------------------------------------------------ the rows of `U` are the pairs of `R ≫ S`
  have fs := firsts_spec Kk N.toNat
  have zR : ∀ i (hi : i < R.n.toNat), z.row ⟨i, by omega⟩ = R.val.row ⟨i, hi⟩ := fun i hi => by
    rw [Vals.concat_row hNn hoff R.val S.key hz, dif_pos hi]
  have zS : ∀ j (hj : j < S.n.toNat), z.row ⟨R.n.toNat + j, by omega⟩ = S.key.row ⟨j, hj⟩ := fun j hj => by
    rw [Vals.concat_row hNn hoff R.val S.key hz, dif_neg (by simp)]; simp only [Nat.add_sub_cancel_left]
  unfold Tab.Holds
  constructor
  · rintro ⟨t, ha, hc⟩
    have htT : t.1 < Tn := Nat.lt_of_lt_of_eq t.2 hTT
    obtain ⟨G, hG, h1, h2⟩ := exists_group wN k t.1 (by rw [← hTn]; exact htT)
    rw [← hSw] at h1 h2
    obtain ⟨wR, wS, qR, qS⟩ := hrw t.1 G hG h1 h2
    generalize Fs G + (t.1 - Sw G) / bN G = a1 at wR qR
    generalize Fs G + cRN G + (t.1 - Sw G) % bN G = a2 at wS qS
    obtain ⟨i, hi, hXi⟩ := Vals.gather_row R.key hX t
    obtain ⟨j, hj, hYj⟩ := Vals.gather_row S.val hY t
    rw [wR, toNat_toUInt64 (by have := hpsN a1 qR.1; omega)] at hi
    rw [wS, toNat_toUInt64 (by have := hpsN a2 qS.1; omega)] at hj
    have eK : Kk a1 = Kk a2 := (fs.2.2.1 a1 qR.1 a2 qS.1).1 (qR.2.1.trans qS.2.1.symm)
    rw [hkq a1 (by omega), hkq a2 (by omega), ← hps a1 qR.1, ← hps a2 qS.1] at eK
    have ez := Vals.row_of_codes z hes hcs ⟨_, hpsN a1 qR.1⟩ ⟨_, hpsN a2 qS.1⟩ eK
    obtain ⟨i, hi'⟩ := i; obtain ⟨j, hj'⟩ := j
    simp only at hi hj; subst hi hj
    have e2 := zS _ hj'; simp only [Nat.add_sub_cancel' qS.2.2] at e2
    refine ⟨R.val.row ⟨_, hi'⟩, ⟨⟨_, hi'⟩, hXi.symm.trans ha, rfl⟩, ⟨⟨_, hj'⟩, ?_, hYj.symm.trans hc⟩⟩
    rw [← e2, ← zR _ hi']; exact ez.symm
  · rintro ⟨b, ⟨i, hia, hib⟩, ⟨j, hjb, hjc⟩⟩
    have ecode := Vals.codes_of_row z hes hcs ⟨i.1, by omega⟩ ⟨R.n.toNat + j.1, by omega⟩
      (by rw [zR i.1 i.2, zS j.1 j.2]; exact hib.trans hjb.symm)
    obtain ⟨qi, hqi, ei⟩ := List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 (show i.1 < N.toNat by omega)))
    obtain ⟨qj, hqj, ej⟩ :=
      List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 (show R.n.toNat + j.1 < N.toNat by omega)))
    have eK : Kk qi = Kk qj := by rw [hkq qi hqi, hkq qj hqj, ei, ej]; exact ecode
    have hG := hgr qi (by omega)
    have gj : Verify.groupOf Kk N.toNat qj = Verify.groupOf Kk N.toNat qi :=
      (fs.2.2.1 qj (by omega) qi (by omega)).2 eK.symm
    generalize hGq : Verify.groupOf Kk N.toNat qi = G at hG gj
    obtain ⟨sgA, sgR⟩ := sg G hG
    have hRi := (sgR qi).1 ⟨by omega, hGq, by rw [hps qi (by omega), ei]; exact i.2⟩
    have hAj := (sgA qj).1 ⟨by omega, gj⟩
    have hSj : Fs G + cRN G ≤ qj := Nat.le_of_not_lt fun hc => by
      have := ((sgR qj).2 ⟨hAj.1, hc⟩).2.2; rw [hps qj (by omega), ej] at this; omega
    have hw' : wN G = cRN G * bN G := by rw [hwN, hbN]
    have hbG := hbN G
    have hb0 : 0 < bN G := by omega
    have hs : qj - Fs G - cRN G < bN G := by omega
    have hmul := Nat.mul_le_mul_left (bN G) (show qi - Fs G + 1 ≤ cRN G by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (bN G) (cRN G), ← hw'] at hmul
    obtain ⟨t, ht⟩ : ∃ t, t = Sw G + (qj - Fs G - cRN G + bN G * (qi - Fs G)) := ⟨_, rfl⟩
    have hd : t - Sw G = qj - Fs G - cRN G + bN G * (qi - Fs G) := by omega
    have hdiv : (t - Sw G) / bN G = qi - Fs G := by
      rw [hd, Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt hs, Nat.zero_add]
    have hmod : (t - Sw G) % bN G = qj - Fs G - cRN G := by
      rw [hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    have h1 : Sw G ≤ t := by omega
    have h2 : t < Sw G + wN G := by omega
    have hkG := hSwm G k hG
    obtain ⟨wR, wS, -, -⟩ := hrw t G hG h1 h2
    rw [hdiv, show Fs G + (qi - Fs G) = qi by omega, hps qi (by omega), ei] at wR
    rw [hmod, show Fs G + cRN G + (qj - Fs G - cRN G) = qj by omega, hps qj (by omega), ej,
      Nat.add_sub_cancel_left] at wS
    have htT : t < Tn.toUSize.toNat := by omega
    obtain ⟨i', hi', hXi⟩ := Vals.gather_row R.key hX ⟨t, htT⟩
    obtain ⟨j', hj', hYj⟩ := Vals.gather_row S.val hY ⟨t, htT⟩
    rw [wR, toNat_toUInt64 (by omega)] at hi'
    rw [wS, toNat_toUInt64 (by omega)] at hj'
    refine ⟨⟨t, htT⟩, ?_, ?_⟩
    · rw [hXi, ← hia]; exact congrArg _ (Fin.ext hi'.symm)
    · rw [hYj, ← hjc]; exact congrArg _ (Fin.ext hj'.symm)

namespace Tab
variable {A B C : Obj}

/-- **`R.comp S` denotes `R ≫ S`** (`Rep.rep_comp`'s statement, pointwise). -/
theorem comp_holds {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : R.comp S = .ok T) (a : A.El) (c : C.El) :
    T.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  obtain ⟨U, hU, hH⟩ := comp_canon h; rw [canon_holds hU]; exact hH a c

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
    ((tab ps).comp (tab qs)).toOption.map Tab.toList == Option.map Tab.toList (CRel.comp (some (tab ps)) (some (tab qs)))) &&
    (tab ps).conv.toOption.isSome && ((tab ps).conv.toOption.map Tab.toList) ==
      (let c := Alg.canonC (⟨(tab ps).n, (tab ps).val, (tab ps).key⟩ : Tab .long .long)
       if c.2 then some c.1.toList else none)

/-- Whether `comp` answers `R ≫ S`: the old `CRel.comp`'s list, and as a set the pairs `(a, c)` with `a {R} b {S} c`. -/
private def compOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab B C) : Bool :=
  let sp := R.toList.flatMap fun (a, b) => S.toList.filterMap fun (b', c) => if b == b' then some (a, c) else none
  match R.comp S with
  | .ok T => some T.toList == Option.map Tab.toList (CRel.comp (some R) (some S)) && T.toList.all sp.contains &&
      sp.all T.toList.contains
  | .error _ => false

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]
/-- The same eight values as `f32` bits. -/
private def f32s : List UInt64 := [0x80000000, 0, 0x7fc00001, 0x7fc00002, 0x7f800000, 0xff800000, 0x3fc00000, 0x80000000]
/-- `-1`, `-128`, `127`, `0`, `1`, `-2`, `-128`, `-1` as `i8` bits. -/
private def i8s : List UInt64 := [0xff, 0x80, 0x7f, 0, 1, 0xfe, 0x80, 0xff]

-- a float middle column, a `foR` column of its stored bits (`Arr.ofFn`) as every fixed-width column is
#guard compOk (⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 9], Arr.ofFn .f64 8 (f64s.getD · 0)⟩ : Tab .long (.atom .f64))
  (⟨5, Arr.ofFn .f64 5 (f64s.reverse.getD · 0), Alg.col [7, 8, 9, 7, 6]⟩ : Tab (.atom .f64) .long)
#guard compOk (⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 9], Arr.ofFn .f32 8 (f32s.getD · 0)⟩ : Tab .long (.atom .f32))
  (⟨5, Arr.ofFn .f32 5 (f32s.reverse.getD · 0), Alg.col [7, 8, 9, 7, 6]⟩ : Tab (.atom .f32) .long)

/-- Two lists hold the same elements, each once: the old layer orders a float NaN first, `kasc` by `ordCode`. -/
private def sameSet {α : Type} [BEq α] : Option (List α) → Option (List α) → Bool
  | some a, some b => a.length == b.length && a.all b.contains && b.all a.contains
  | _, _ => false

/-- The old layer's table in canonical form, as a list. -/
private def oldList {A B : Obj} (c : CRel A B) : Option (List (A.El × B.El)) :=
  c.bind fun t => let c := Alg.canonC t; if c.2 then some c.1.toList else none

/-- The five-kernel `canon`, `∪`, `∩`, `−`, `⊑`, `conv` and `comp` against the old operators on the same tables, whose
key, value or middle column holds the words `ws` at `t` (`Arr.ofFn`). -/
private def typeOk (t : QAtomicType) [BEq (Obj.atom t).El] (ws : List UInt64) (hu : t ≠ .u1 ∧ t.width.isSome) : Bool :=
  let x := Arr.ofFn t 8 (ws.getD · 0) hu
  let ls : List Int64 := [5, 6, 5, 7, 5, 6, 8, 5]
  let K : Tab (.atom t) .long := ⟨8, x, Alg.col ls⟩
  let V : Tab .long (.atom t) := ⟨8, Alg.col ls, x⟩
  let K₂ : Tab (.atom t) .long := ⟨8, x, Alg.col ls.reverse⟩
  let S : Tab (.atom t) .long := ⟨3, Arr.ofFn t 3 (ws.getD · 0) hu, Alg.col [5, 6, 3]⟩
  let le (R S : Tab (.atom t) .long) := (R.le S).toOption == (let c := Alg.leC R S; if c.2 then some c.1 else none)
  sameSet (K.canon.toOption.map Tab.toList) (oldList (some K)) &&
  sameSet (V.canon.toOption.map Tab.toList) (oldList (some V)) &&
  sameSet ((K.union K₂).toOption.map Tab.toList) (oldList (CRel.union (some K) (some K₂))) &&
  sameSet ((K.inter K₂).toOption.map Tab.toList) (oldList (CRel.inter (some K) (some K₂))) &&
  sameSet ((K.diff S).toOption.map Tab.toList) (oldList (CRel.diff (some K) (some S))) &&
  sameSet ((S.diff K).toOption.map Tab.toList) (oldList (CRel.diff (some S) (some K))) &&
  le K K && le K S && le S K &&
  sameSet (K.conv.toOption.map Tab.toList) (oldList (some (⟨8, K.val, K.key⟩ : Tab .long (.atom t)))) &&
  sameSet ((V.comp K).toOption.map Tab.toList) (Option.map Tab.toList (CRel.comp (some V) (some K))) &&
  sameSet ((K.comp V).toOption.map Tab.toList) (Option.map Tab.toList (CRel.comp (some K) (some V)))

-- floats (`-0.0` apart from `+0.0`, two NaN payloads apart, `±inf`), a narrow signed integer and `datetime` as key,
-- value and middle column
#guard typeOk .f64 f64s ⟨by decide, by decide⟩ && typeOk .f32 f32s ⟨by decide, by decide⟩ &&
  typeOk .i8 i8s ⟨by decide, by decide⟩ && typeOk .datetime f64s ⟨by decide, by decide⟩
-- `-0.0` and `+0.0`, and the two NaNs, are distinct rows: stored-bit equality
#guard ((⟨8, Arr.ofFn .f64 8 (f64s.getD · 0), Alg.col [1, 1, 1, 1, 1, 1, 1, 1]⟩ : Tab (.atom .f64) .long).canon.toOption.map
  Tab.n) == some 7

-- a `u1` middle column (`Arr.bools`) and a tuple middle column
#guard compOk (⟨4, Alg.col [3, 1, 2, 1], Arr.bools 4 fun i => i % 2 == 0⟩ : Tab .long (.atom .u1))
  (⟨3, Arr.bools 3 fun i => i == 1, Alg.col [7, 8, 9]⟩ : Tab (.atom .u1) .long)
#guard compOk (⟨4, Alg.col [3, 1, 2, 1], (Alg.col [1, 1, 2, 2], Alg.col [5, 6, 5, 6])⟩ : Tab .long (.prod .long .long))
  (⟨3, (Alg.col [2, 1, 1], Alg.col [5, 6, 5]), Alg.col [7, 8, 9]⟩ : Tab (.prod .long .long) .long)

end Checks

#print axioms Tab.conv_holds
#print axioms Tab.comp_holds

end Rel
