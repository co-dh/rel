import Rel.Run.Comp
import Rel.Run.SetOps
import Rel.RepCols
import Rel.RepCanon
import Rel.RepSetOps

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

/-- Splitting a count by a second predicate. -/
theorem countP_split (p q : Nat → Bool) : ∀ l : List Nat,
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x)
  | [] => rfl
  | x :: l => by
    simp only [List.countP_cons, countP_split p q l]
    cases p x <;> cases q x <;> simp <;> omega

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

/-- **`.add` folded by group over `0`/`1` words** (`scatterWords_fold`'s form, which `kscatter .add` and
`Tab.groupFold .add` answer) is each group's count of rows with `P`. -/
theorem fold_add_count {N K : USize} {g e o : Enc} (hgs : (raw .i64 N g).size = N.toNat)
    (hc : ∀ j < K.toNat, (raw .i64 K o)[j]?.getD 0 = (((List.range (raw .i64 N g).size).filter fun k =>
      ((raw .i64 N g)[k]?.getD 0).toNat = j).map ((raw .i64 N e)[·]?.getD 0)).foldl (· + ·) 0) (gr : Nat → Nat)
    (P : Nat → Bool) (hg : ∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (gr q).toUInt64)
    (hgr : ∀ q < N.toNat, gr q < 2 ^ 64) (he : ∀ q < N.toNat, (raw .i64 N e)[q]?.getD 0 = if P q then 1 else 0) :
    ∀ G < K.toNat, (raw .i64 K o)[G]?.getD 0 = ((List.range N.toNat).countP fun q => gr q == G && P q).toUInt64 := by
  intro G hG
  rw [hc G hG, hgs]
  have hf : (List.range N.toNat).filter (fun k => ((raw .i64 N g)[k]?.getD 0).toNat = G) =
      (List.range N.toNat).filter (fun q => gr q == G) := List.filter_congr fun q hq => by
    rw [hg q (List.mem_range.1 hq), toNat_toUInt64 (hgr q (List.mem_range.1 hq))]; by_cases e : gr q = G <;> simp [e]
  rw [hf, List.map_congr_left (g := fun q => if P q then (1 : UInt64) else 0)
    (fun q hq => he q (List.mem_range.1 (List.mem_filter.1 hq).1)), foldl_add_count, List.countP_filter]
  simp [Bool.and_comm]

/-- **`kscatter (.add)` of `0`/`1` words by group** is each group's count of rows with `P` (`fold_add_count`). -/
theorem scatter_add_count {N K : USize} {g e o : Enc} (h : kscatter .add N g e K 0 = .ok o) (gr : Nat → Nat)
    (P : Nat → Bool) (hg : ∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (gr q).toUInt64)
    (hgr : ∀ q < N.toNat, gr q < 2 ^ 64) (he : ∀ q < N.toNat, (raw .i64 N e)[q]?.getD 0 = if P q then 1 else 0) :
    ∀ G < K.toNat, (raw .i64 K o)[G]?.getD 0 = ((List.range N.toNat).countP fun q => gr q == G && P q).toUInt64 :=
  fold_add_count (kscatter_words h).1 (scatterWords_fold (f := (· + ·)) (fun _ _ => rfl) (kscatter_words h).2.2).2
    gr P hg hgr he

/-- Word `t` of the index column `.pos` is `t`. -/
theorem raw_pos_word {n : USize} {t : Nat} (ht : t < n.toNat) : (raw .i64 n (.pos : Enc))[t]?.getD 0 = t.toUInt64 := by
  simp only [raw, Array.getElem?_map, Array.getElem?_range, ht, if_true, Option.map_some, Option.getD_some]


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

/-- **`kscatter (.last)` at distinct indices** writes word `q` of `e` at index `π q`: no later row writes there. -/
theorem scatter_last_at {N K : USize} {ix e o : Enc} (h : kscatter .last N ix e K 0 = .ok o) (π : Nat → Nat)
    (hix : ∀ q < N.toNat, (raw .i64 N ix)[q]?.getD 0 = (π q).toUInt64) (hπ : ∀ q < N.toNat, π q < K.toNat)
    (hinj : ∀ q < N.toNat, ∀ q' < N.toNat, π q = π q' → q = q') :
    ∀ q < N.toNat, (raw .i64 K o)[π q]?.getD 0 = (raw .i64 N e)[q]?.getD 0 := by
  obtain ⟨hs, -, hw⟩ := kscatter_words h
  have hK := K.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hat : ∀ q < N.toNat, ((raw .i64 N ix)[q]?.getD 0).toNat = π q := fun q hq => by
    rw [hix q hq, toNat_toUInt64 (by have := hπ q hq; omega)]
  intro q hq
  have := ((scatterWords_spec _ _ _ _).2 _ hw).2.2 q (by omega) fun q' h1 h2 e => by
    have e' : ((raw .i64 N ix)[q']?.getD 0).toNat = ((raw .i64 N ix)[q]?.getD 0).toNat := e
    rw [hat q' (by omega), hat q hq] at e'; have := hinj _ (by omega) _ hq e'; omega
  have h' : (raw .i64 K o)[π q]? = some ((raw .i64 N e)[q]?.getD 0) := by rw [← hat q hq]; exact this
  rw [h']; rfl

/-- **GROUP over the rows of `x`** (`Vals.cols`, `kasc`, `kseen` over the sorted columns): sorted row `q` is input
row `π q`, `π` a permutation of the rows; sorted row `q` is in group `gr q`, whose first sorted row is `fs G`; two
sorted rows share a group exactly when their input rows are equal. -/
theorem group_rows {A : Obj} {N : USize} {x : Vals A N} {es : List (AscKey × Enc)} {vs : List Enc} {p g f : Enc}
    {k : Nat} (hes : Vals.cols x = .ok es) (hasc : kasc N es = .ok (vs, p))
    (hseen : kseen N ((es.map (·.1)).zip vs) = .ok (k, g, f)) :
    ∃ π gr fs : Nat → Nat, k ≤ N.toNat ∧
      (∀ q < N.toNat, (raw .i64 N p)[q]?.getD 0 = (π q).toUInt64 ∧ π q < N.toNat) ∧
      (∀ q < N.toNat, ∀ q' < N.toNat, π q = π q' → q = q') ∧
      (∀ i < N.toNat, ∃ q < N.toNat, π q = i) ∧
      (∀ P : Nat → Bool, (List.range N.toNat).countP (fun q => P (π q)) = (List.range N.toNat).countP P) ∧
      (∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < k) ∧
      (∀ G < k, (raw .i64 k.toUSize f)[G]?.getD 0 = (fs G).toUInt64 ∧ fs G < N.toNat ∧ gr (fs G) = G) ∧
      ∀ q < N.toNat, ∀ q' < N.toNat, gr q = gr q' ↔
        ∀ (h : π q < N.toNat) (h' : π q' < N.toNat), x.row ⟨π q, h⟩ = x.row ⟨π q', h'⟩ := by
  obtain ⟨cs, hcs, hp, hkq⟩ := kasc_grade hasc
  obtain ⟨hperm, -⟩ := ascGrade_spec N.toNat (ascKeys N es)
  obtain ⟨hk, hg, hf⟩ := kseen_ok hseen
  generalize ascGrade N.toNat (ascKeys N es) = ps at hp hkq hperm
  generalize seenKey N ((es.map (·.1)).zip vs) = Kk at hk hg hf hkq
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  have hpsN : ∀ q < N.toNat, ps[q]?.getD 0 < N.toNat := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hkN : k ≤ N.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hpsN' : ∀ q (hq : q < ps.length), ps[q] < N.toNat := fun q _ => List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hnd := hperm.nodup_iff.2 List.nodup_range
  obtain ⟨-, -, hgg, hfg, -⟩ := firsts_spec Kk N.toNat
  refine ⟨fun q => ps[q]?.getD 0, Verify.groupOf Kk N.toNat, fun G => (firstsOf Kk N.toNat)[G]?.getD 0, hkN,
    fun q hq => ⟨by rw [hp]; simp [List.getElem?_eq_getElem (show q < ps.length by omega)], hpsN q hq⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq q' hq' e
    simp only [List.getElem?_eq_getElem (show q < ps.length by omega),
      List.getElem?_eq_getElem (show q' < ps.length by omega), Option.getD_some] at e
    rcases Nat.lt_trichotomy q q' with hl | hl | hl
    · exact absurd e (List.pairwise_iff_getElem.1 hnd _ _ _ _ hl)
    · exact hl
    · exact absurd e.symm (List.pairwise_iff_getElem.1 hnd _ _ _ _ hl)
  · intro i hi
    obtain ⟨q, hq, e⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 hi))
    exact ⟨q, by omega, by simp [List.getElem?_eq_getElem hq, e]⟩
  · intro P
    have hmap : (List.range N.toNat).map (fun q => ps[q]?.getD 0) = ps :=
      List.ext_getElem (by simp [hlen]) fun i h1 h2 => by simp [List.getElem?_eq_getElem h2]
    rw [show (fun q => P (ps[q]?.getD 0)) = P ∘ (fun q => ps[q]?.getD 0) from rfl, ← List.countP_map, hmap,
      hperm.countP_eq]
  · intro q hq
    exact ⟨by rw [hg, (wordsFoR_closed _ (by simp)).2.1]; simp [hq],
      by have := groupOf_lt (g := Kk) (m := N.toNat) hq; omega⟩
  · intro G hG
    have hG' : G < (firstsOf Kk N.toNat).length := by omega
    refine ⟨by rw [hf, (wordsFoR_closed _ (by rw [hK, hk]; simp)).2.1]; simp [List.getElem?_eq_getElem hG'], ?_, ?_⟩
    · simp only [List.getElem?_eq_getElem hG', Option.getD_some]; exact firsts_lt Kk N.toNat (List.getElem_mem _)
    · simp only [List.getElem?_eq_getElem hG', Option.getD_some]; exact hfg G hG'
  · intro q hq q' hq'
    simp only [List.getElem?_eq_getElem (show q < ps.length by omega),
      List.getElem?_eq_getElem (show q' < ps.length by omega), Option.getD_some]
    rw [hgg q hq q' hq', hkq q (by omega), hkq q' (by omega)]
    exact ⟨fun e h h' => Vals.row_of_codes x hes hcs ⟨ps[q], h⟩ ⟨ps[q'], h'⟩ e,
      fun e => Vals.codes_of_row x hes hcs ⟨_, hpsN' q (by omega)⟩ ⟨_, hpsN' q' (by omega)⟩
        (e (hpsN' q (by omega)) (hpsN' q' (by omega)))⟩

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
    simp only at e
    exact step 0 ht 0 (by decide) (fun _ _ h => absurd h (Nat.not_lt_zero _)) (Or.inl rfl) e
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    have e := hpre (t + 1) ht
    rw [if_neg (by omega), Nat.add_sub_cancel] at e
    refine step (t + 1) ht _ i1 (fun G hG h => i2 G hG (by omega)) ?_ e
    rcases i3 with e3 | ⟨G, hG, hGx, e3⟩
    · exact Or.inl e3
    · exact Or.inr ⟨G, hG, by omega, e3⟩


/-- **EXPAND places each group's run**: where word `g` of the `K` widths is `wN g`, below
`2^63` in total, there are `T = Σ wN` rows, and row `t` of group `g`'s run `[Σ_{<g} wN, Σ_{≤g} wN)` has group `g`
and offset `t - Σ_{<g} wN`. -/
theorem expand_spec {K T : USize} {w G u : Enc} (h : expand K w = .ok (T, G, u)) (wN : Nat → Nat)
    (hw : ∀ g < K.toNat, (raw .i64 K w)[g]?.getD 0 = (wN g).toUInt64)
    (hs : ((List.range K.toNat).map wN).sum < 2 ^ 63) (hK : K.toNat < 2 ^ 63) :
    T.toNat = ((List.range K.toNat).map wN).sum ∧ ∀ g < K.toNat, ∀ t, ((List.range g).map wN).sum ≤ t →
      t < ((List.range g).map wN).sum + wN g → (raw .i64 T G)[t]?.getD 0 = g.toUInt64 ∧
        (raw .i64 T u)[t]?.getD 0 = (t - ((List.range g).map wN).sum).toUInt64 := by
  unfold expand at h
  split at h; · cases h
  rename_i P hP
  dsimp only at h
  split at h; · cases h
  rename_i hTU
  have hPf : ∃ md pk, P = .foR md pk := by
    unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
    split at hP; · cases hP
    rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at hP; subst hP
    exact kscan_foR hr
  generalize hT : lastCount _ P _ = Tn at h hTU
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, ho, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pm, hpm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Gc, hGc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨og, hog, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨u', hu, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hPw := colPrefix_add_sum hP wN hw
  have hSwm : ∀ g g', g < g' → ((List.range g).map wN).sum + wN g ≤ ((List.range g').map wN).sum :=
    fun g g' hg => by rw [← sum_range_succ']; exact sum_range_mono wN hg
  have hSwk : ∀ g ≤ K.toNat, ((List.range g).map wN).sum ≤ ((List.range K.toNat).map wN).sum :=
    fun g hg => sum_range_mono wN hg
  have hTn : Tn = ((List.range K.toNat).map wN).sum := hT.symm.trans (lastCount_eq _ hPf hs
    (fun hk0 => by rw [hPw (K.toNat - 1) (by omega), Nat.sub_add_cancel hk0])
    (fun hk0 => by rw [hk0]; rfl))
  have how : ∀ g < K.toNat, (raw .i64 K o)[g]?.getD 0 = ((List.range g).map wN).sum.toUInt64 := fun g hg => by
    have e := (colMap_raw ho).2.2.2 g hg
    rw [hPw g hg, hw g hg, sum_range_succ'] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, ← toUInt64_sub (by omega), Nat.add_sub_cancel]
  have hTT : Tn.toUSize.toNat = Tn := USize.toNat_ofNat_of_lt' (by omega)
  have hT1 : (Tn.toUSize + 1).toNat = Tn + 1 := by
    rw [USize.toNat_add, hTT]; simp only [USize.toNat_one]
    exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; omega)
  refine ⟨by rw [hTT, hTn], fun g hg t h1 h2 => ?_⟩
  have := hSwm g K.toNat hg
  have htT : t < Tn.toUSize.toNat := by omega
  have hGw : (raw .i64 Tn.toUSize Gc)[t]?.getD 0 = g.toUInt64 := by
    obtain ⟨-, e⟩ := kgather_word hGc t htT
    rw [raw_pos_word htT, toNat_toUInt64 (by omega)] at e
    rw [e]
    obtain ⟨-, lo, alt⟩ := expand_groups hsc hpm (fun g => ((List.range g).map wN).sum) how
      (fun g hg => by dsimp only; have := hSwk g (by omega); omega) hK t (by omega)
    have lo' := lo g hg h1
    have hx : ((raw .i64 (Tn.toUSize + 1) pm)[t]?.getD 0).toNat = g := by
      rcases alt with e0 | ⟨G', hG', h3, e3⟩
      · omega
      · rcases Nat.lt_or_ge g G' with hl | hl
        · have := hSwm g G' hl; omega
        · omega
    rw [← hx]; simp
  refine ⟨hGw, ?_⟩
  have e := (colMap_raw hu).2.2.2 t htT
  rw [raw_pos_word htT, (kgather_word hog t htT).2, hGw, toNat_toUInt64 (by omega), how g hg] at e
  simp only [Op.eval, Except.ok.injEq] at e
  rw [← e, toUInt64_sub h1]

/-- **`R.compOne S` is `canon` of a table denoting `R ≫ S`**: so `T` holds `R ≫ S` and is sorted without duplicates
(`Tab.canon_sorted` at `U`). -/
theorem Tab.compOne_canon {A B C : Obj}
    {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : R.compOne S = .ok T) (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  rw [Tab.compOne] at h; simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  dsimp only [Tab.compGroups] at hx
  split at hx; · cases hx
  rename_i hnm
  simp only [bind] at hx; rw [Except.bind_eq_ok'] at hx; obtain ⟨_, -, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨⟨N, sh⟩, hcat, hx⟩ := hx; try dsimp only at hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨z, hz, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨es, hes, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨⟨vs, p⟩, hasc, hx⟩ := hx; try dsimp only at hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨⟨k, g, f⟩, hseen, hx⟩ := hx; try dsimp only at hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨lt, hlt, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨cR, hcR, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨c1, hc1, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨cnt, hcnt, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨cS, hcS, hx⟩ := hx
  rw [Except.bind_eq_ok'] at hx; obtain ⟨w, hw, hx⟩ := hx
  simp only [pure, Except.pure, Except.ok.injEq] at hx; subst hx
  dsimp only [Tab.compExpand] at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T', Gc, u⟩, hex, h⟩ := h; try dsimp only at h
  obtain ⟨Tn, rfl, hTT⟩ : ∃ Tn : Nat, T' = Tn.toUSize ∧ Tn.toUSize.toNat = Tn := ⟨T'.toNat, by simp, by simp⟩
  rw [Except.bind_eq_ok'] at h; obtain ⟨ft, hft, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ct, hct, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dv, hdv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ir, hir, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iR, hiR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cr, hcr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a1, ha1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨md, hmd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨qS, hqS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pq, hpq, h⟩ := h
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
    have e := (colMap_post hlt).2 q hq
    -- `gt` with the constant on its left is `lt` with it on its right, by `Op.eval`
    change Op.lt.eval ((raw .i64 N p)[q]?.getD 0) R.n.toUInt64 = _ at e
    rw [hpw q hq, hnU,
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
  obtain ⟨hTn0, hex'⟩ := expand_spec hex wN (fun G hG => hww G (by omega)) (by rw [hK]; omega) (by omega)
  rw [hK] at hTn0 hex'
  have hTn : Tn = ((List.range k).map wN).sum := hTT.symm.trans hTn0
  ------------------------------------------------------------------ each output row's group (EXPAND)
  obtain ⟨Sw, hSw⟩ : ∃ F : Nat → Nat, ∀ G, F G = ((List.range G).map wN).sum := ⟨_, fun _ => rfl⟩
  obtain ⟨bN, hbN⟩ : ∃ F : Nat → Nat, ∀ G, F G = cntN G - cRN G := ⟨_, fun _ => rfl⟩
  obtain ⟨Fs, hFs⟩ : ∃ F : Nat → Nat, ∀ G, F G = (firstsOf Kk N.toNat)[G]?.getD 0 := ⟨_, fun _ => rfl⟩
  have hn63 : R.n.toNat * S.n.toNat + R.n.toNat + S.n.toNat < 2 ^ 63 := by omega
  have hTn' : Tn = Sw k := by rw [hSw]; exact hTn
  have hTk : Sw k ≤ R.n.toNat * S.n.toNat := by rw [hSw]; exact hSk
  have hSwm : ∀ G G', G < G' → Sw G + wN G ≤ Sw G' := fun G G' hG => by
    rw [hSw, hSw, ← sum_range_succ']; exact sum_range_mono wN hG
  have hSwk : ∀ G ≤ k, Sw G ≤ Sw k := fun G hG => by rw [hSw, hSw]; exact sum_range_mono wN hG
  have hGu : ∀ t G, G < k → Sw G ≤ t → t < Sw G + wN G → (raw .i64 Tn.toUSize Gc)[t]?.getD 0 = G.toUInt64 ∧
      (raw .i64 Tn.toUSize u)[t]?.getD 0 = (t - Sw G).toUInt64 :=
    fun t G hG h1 h2 => by rw [hSw] at h1 h2 ⊢; exact hex' G hG t h1 h2
  have hGw : ∀ t G, G < k → Sw G ≤ t → t < Sw G + wN G → (raw .i64 Tn.toUSize Gc)[t]?.getD 0 = G.toUInt64 :=
    fun t G hG h1 h2 => (hGu t G hG h1 h2).1
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
    have := sorted_groups (n := R.n.toNat) hlen hsort (fun q hq => by rw [hkq q hq]; simp [seenKey]) hG'
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
    have wct := hgath bN hct (fun G hG => by rw [hbN]; exact hcSw G hG) t G hG h1 h2
    have wcr := hgath cRN hcr hcRw t G hG h1 h2
    have wu := (hGu t G hG h1 h2).2
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
    have e := (colMap_post hiS).2 t htT
    rw [wpq, hnU] at e
    simp only [Op.eval, Except.ok.injEq] at e
    have hneg : ∀ a b : UInt64, 0 - b + a = a - b := fun a b => by
      rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.zero_add, UInt64.add_comm]
    rw [← e, hneg, toUInt64_sub hnps]
  ------------------------------------------------------------------ the rows of `U` are the pairs of `R ≫ S`
  have fs := firsts_spec Kk N.toNat
  have zR : ∀ i (hi : i < R.n.toNat), z.row ⟨i, by omega⟩ = R.val.row ⟨i, hi⟩ := fun i hi => by
    rw [Vals.concat_row hNn hoff R.val S.key hz hR.2 hS.1, dif_pos hi]
  have zS : ∀ j (hj : j < S.n.toNat), z.row ⟨R.n.toNat + j, by omega⟩ = S.key.row ⟨j, hj⟩ := fun j hj => by
    rw [Vals.concat_row hNn hoff R.val S.key hz hR.2 hS.1, dif_neg (by simp)]; simp only [Nat.add_sub_cancel_left]
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

/-- A step that keeps `P` keeps it through `List.foldlM`. -/
theorem foldlM_keeps {α β : Type} {P : β → Prop} {f : β → α → Except String β}
    (hf : ∀ b a b', f b a = .ok b' → P b → P b') : ∀ (l : List α) {b b' : β}, l.foldlM f b = .ok b' → P b → P b'
  | [], _, _, h, hb => by simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | a :: l, _, _, h, hb => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc; exact foldlM_keeps hf l h (hf _ a c hc hb)

namespace Tab
variable {A B C : Obj}

/-- **`compExpand` keeps `Tab.WF`**: `R.key` and `S.val` gathered at each output row, `canon`. -/
theorem compExpand_wf {R : Tab A B} {S : Tab B C} {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc}
    {t : Tab A C} (h : compExpand R S x = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  obtain ⟨N, p, g, f, K, cR, cS, w⟩ := x
  simp only [Tab.compExpand, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hR.1, Vals.gather_wf ‹_› hS.2⟩

theorem compOne_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : compOne R S = .ok t) (hR : R.WF) (hS : S.WF) :
    t.WF := by
  simp only [Tab.compOne, bind, Except.bind] at h
  split at h; · cases h
  exact compExpand_wf h hR hS

theorem compBlock_wf {R : Tab A B} {S : Tab B C} {c : Enc} {j : Nat} {t : Tab A C} (h : compBlock R S c j = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compBlock, bind, Except.bind] at h
  okSplit
  exact compOne_wf h (keep_wf ‹_› hR) hS

/-- **`compBlocks` keeps `Tab.WF`**: each block by `compBlock_wf`, met by `∪` (`union_wf`). -/
theorem compBlocks_wf {R : Tab A B} {S : Tab B C} {nb : Nat} {bid : Arr .i64 R.n} {t : Tab A C}
    (h : compBlocks R S nb bid = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compBlocks, bind, Except.bind] at h
  okSplit
  refine foldlM_keeps (P := Tab.WF) (fun b a b' hb hw => ?_) _ h (compBlock_wf ‹_› hR hS)
  simp only [bind, Except.bind] at hb
  split at hb; · cases hb
  exact union_wf hb hw (compBlock_wf ‹_› hR hS)

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
holds, and past the first step it is a `canon`. -/
theorem foldlM_union {k v : Obj} {f : Nat → Except String (Tab k v)} (hf : ∀ j X, f j = .ok X → X.WF) :
    ∀ (L : List Nat) (acc T : Tab k v), L.foldlM (fun acc j => do acc.union (← f j)) acc = .ok T → acc.WF →
      (∀ j ∈ L, ∃ X, f j = .ok X) ∧ (L = [] → T = acc) ∧ (L ≠ [] → ∃ U : Tab k v, U.canon = .ok T) ∧
      ∀ a b, T.Holds a b ↔ acc.Holds a b ∨ ∃ j ∈ L, ∃ X, f j = .ok X ∧ X.Holds a b
  | [], acc, T, h, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | j :: L, acc, T, h, hacc => by
    rw [List.foldlM_cons] at h; simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨acc', h1, h2⟩ := h
    rw [Except.bind_eq_ok'] at h1; obtain ⟨X, hX, hu⟩ := h1
    have hXw := hf j X hX
    obtain ⟨hL, h0, hc, hH⟩ := foldlM_union hf L acc' T h2 (union_wf hu hacc hXw)
    refine ⟨fun i hi => ?_, by simp, fun _ => ?_, fun a b => ?_⟩
    · rcases List.mem_cons.1 hi with rfl | hi
      · exact ⟨X, hX⟩
      · exact hL i hi
    · by_cases hL0 : L = []
      · obtain rfl := h0 hL0; obtain ⟨C, -, hC⟩ := union_sorted hu; exact ⟨C, hC⟩
      · exact hc hL0
    · rw [hH, union_holds hu hacc hXw]; constructor
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
  rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨m, hm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Rj, hRj, h⟩ := h
  have hmi : ∀ i < R.n.toNat, (raw .i64 R.n m)[i]?.getD 0 =
      if (raw .i64 R.n c)[i]?.getD 0 = j.toUInt64 then 1 else 0 := fun i hi => by
    have e1 := (colMap_raw hm).2.2.2 i hi
    simp only [colConst_raw he, Array.getElem?_replicate, hi, if_true, Option.getD_some] at e1
    have e2 : Op.eval .eq ((raw .i64 R.n c)[i]?.getD 0) j.toUInt64 =
        .ok (if (raw .i64 R.n c)[i]?.getD 0 = j.toUInt64 then 1 else 0) := by
      show Except.ok (if ((raw .i64 R.n c)[i]?.getD 0 == j.toUInt64) = true then 1 else 0) = _; simp
    rw [e2] at e1; exact (Except.ok.inj e1).symm
  obtain ⟨U, hU, hH⟩ := compOne_canon h (keep_wf hRj hR) hS
  rw [canon_holds hU, hH]
  refine exists_congr fun b => and_congr_left fun _ => ?_
  rw [keep_holds hRj (fun i hi => by rw [hmi i hi]; split <;> decide)]
  refine exists_congr fun i => and_congr_left fun _ => ?_
  rw [hmi i.1 i.2]; split <;> simp_all

/-- **`compBlocks` denotes `R ≫ S` and is a `canon`**, whatever the block words `bid`: clamped into `[0, nb - 1]`,
every row of `R` is in one block, and every block is in the `∪`. -/
theorem compBlocks_canon {R : Tab A B} {S : Tab B C} {nb : Nat} {bid : Arr .i64 R.n} {T : Tab A C}
    (h : compBlocks R S nb bid = .ok T) (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  unfold compBlocks at h
  split at h; · cases h
  rename_i hnb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T0, h0, h⟩ := h
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
    rw [Except.bind_eq_ok'] at h0'; obtain ⟨_, -, h0'⟩ := h0'
    rw [Except.bind_eq_ok'] at h0'; obtain ⟨_, hk0, h0'⟩ := h0'
    obtain ⟨U, hU, -⟩ := compOne_canon h0' (keep_wf hk0 hR) hS
    exact ⟨U, hU, fun a d => by rw [← hT, canon_holds hU]⟩
  · obtain ⟨U, hU⟩ := hcan hL0
    exact ⟨U, hU, fun a d => by rw [← hT, canon_holds hU]⟩

/-- **`R.compWith bound S` is `canon` of a table denoting `R ≫ S`**, at every `bound`; `Tab.comp` is `bound =
blockRows`. -/
theorem compFrom_canon {bound : Nat} {R : Tab A B} {S : Tab B C}
    {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc} {T : Tab A C} (hx : compGroups R S = .ok x)
    (h : compFrom bound R S x = .ok T) (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  simp only [compFrom, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, -, h⟩ := h
  rcases o with _ | ⟨nb, bid⟩
  · exact compOne_canon (by rw [compOne, hx]; exact h) hR hS
  · exact compBlocks_canon h hR hS

theorem comp_canon {bound : Nat} {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : compWith bound R S = .ok T)
    (hR : R.WF) (hS : S.WF) :
    ∃ U : Tab A C, U.canon = .ok T ∧ ∀ a c, U.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  unfold compWith at h
  split at h
  · exact compOne_canon h hR hS
  · simp only [bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
    exact compFrom_canon hx h hR hS

/-- **`R.comp S` denotes `R ≫ S`** (`Rep.rep_comp`'s statement, pointwise). -/
theorem comp_holds {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : R.comp S = .ok T) (hR : R.WF) (hS : S.WF)
    (a : A.El) (c : C.El) :
    T.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  obtain ⟨U, hU, hH⟩ := comp_canon h hR hS; rw [canon_holds hU]; exact hH a c

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
-- the five-kernel `comp` and `conv` against `R ≫ S` and `R°` as sets of pairs, each pair once: duplicates,
-- negatives, an empty side, no common middle value, a group whose run product is past 1
#guard
  let ts : List (List (Int64 × Int64)) := [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
    [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], [(4, 8)], []]
  ts.all fun ps => (ts.all fun qs => specOk ((tab ps).comp (tab qs))
    (ps.flatMap fun (a, b) => qs.filterMap fun (b', c) => if b == b' then some (a, c) else none)) &&
    specOk (tab ps).conv (ps.map fun (a, b) => (b, a))

/-- Whether `compWith b` (blocked past `b` rows) and `compOne` (one expansion) give the same rows. -/
private def blockedOk (b : Nat) (ps qs : List (Int64 × Int64)) : Bool :=
  match Tab.compWith b (tab ps) (tab qs), (tab ps).compOne (tab qs) with
  | .ok X, .ok Y => X.toList == Y.toList
  | _, _ => false

/-- The block count `compCuts b` gives `tab ps ≫ tab qs` (`1`: one block). -/
private def blockCount (b : Nat) (ps qs : List (Int64 × Int64)) : Option Nat :=
  ((Tab.compGroups (tab ps) (tab qs)).bind (Tab.compCuts b (tab ps).n)).toOption.map fun o => (o.map (·.1)).getD 1

-- middle values `1 2 3` expand to `6 4 4` rows (duplicates `(1, 10)` …): every bound `0 … 15` cuts between groups,
-- at a group's end (`6`, `10`), inside a group larger than the bound (`1 … 5`), or not at all (`14`, `15`); an empty
-- side, no common middle value, and negative words
#guard let ps : List (Int64 × Int64) := [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (4, 3), (1, 3), (1, 1)]
  let qs : List (Int64 × Int64) := [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10), (3, 13), (9, 9)]
  let ts := [ps, qs, [], [(-1, 5), (-2, 5), (7, 7)], [(5, -3), (5, 1), (5, -3)]]
  (List.range 16).all fun b => ts.all fun xs => ts.all fun ys => blockedOk b xs ys
#guard blockCount 3 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 3
#guard blockCount 10 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 2
#guard blockCount 14 [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (1, 3)] [(1, 10), (1, 11), (2, 10), (2, 12), (3, 10),
  (3, 13)] == some 1

/-- Whether `comp` answers `R ≫ S`: as a set the pairs `(a, c)` with `a {R} b {S} c`. -/
private def compOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab B C) : Bool :=
  let sp := R.toList.flatMap fun (a, b) => S.toList.filterMap fun (b', c) => if b == b' then some (a, c) else none
  match R.comp S with
  | .ok T => T.toList.all sp.contains &&
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

/-- The five-kernel `canon`, `∪`, `∩`, `−`, `⊑`, `conv` and `comp` against their denotations as sets of pairs on the
same tables, whose key, value or middle column holds the words `ws` at `t` (`Arr.ofFn`). -/
private def typeOk (t : QAtomicType) [BEq (Obj.atom t).El] (ws : List UInt64) (hu : t ≠ .u1 ∧ t.width.isSome) : Bool :=
  let x := Arr.ofFn t 8 (ws.getD · 0) hu
  let ls : List Int64 := [5, 6, 5, 7, 5, 6, 8, 5]
  let K : Tab (.atom t) .long := ⟨8, x, Alg.col ls⟩
  let V : Tab .long (.atom t) := ⟨8, Alg.col ls, x⟩
  let K₂ : Tab (.atom t) .long := ⟨8, x, Alg.col ls.reverse⟩
  let S : Tab (.atom t) .long := ⟨3, Arr.ofFn t 3 (ws.getD · 0) hu, Alg.col [5, 6, 3]⟩
  let k := K.toList; let k₂ := K₂.toList; let s := S.toList; let v := V.toList
  let le (R S : Tab (.atom t) .long) := (R.le S).toOption == some (R.toList.all S.toList.contains)
  let comp {A B C : Obj} [BEq B.El] (r : List (A.El × B.El)) (q : List (B.El × C.El)) : List (A.El × C.El) :=
    r.flatMap fun (a, b) => q.filterMap fun (b', c) => if b == b' then some (a, c) else none
  specOk K.canon k && specOk V.canon v && specOk (K.union K₂) (k ++ k₂) &&
  specOk (K.inter K₂) (k.filter k₂.contains) && specOk (K.diff S) (k.filter (!s.contains ·)) &&
  specOk (S.diff K) (s.filter (!k.contains ·)) && le K K && le K S && le S K &&
  specOk K.conv (k.map fun (a, b) => (b, a)) && specOk (V.comp K) (comp v k) && specOk (K.comp V) (comp k v)

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
-- an `arr` middle column: cells over two payloads (equal cells from different ranges, the empty cell),
-- a side of no payload rows, a table of no rows, tuple elements and nested arrays
#guard let As := [arrTab arrCells arrPay, arrTab [(1, 2, 1), (1, 3, 7), (0, 0, 2), (2, 4, 1), (0, 2, 9)] [9, 5, 1, 5],
    arrTab [(0, 0, 1), (0, 0, 2)] [], arrTab [] arrPay]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let As := [arrOn arrCells (B := .prod .long .long) (Alg.col arrPay, Alg.col [0, 1, 0, 0, 2]),
    arrOn [(1, 3, 7), (0, 0, 2), (2, 5, 1)] (B := .prod .long .long) (Alg.col arrPay, Alg.col [1, 0, 0, 1, 0])]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let As := [arrOn arrCells (arrTab [(1, 2, 1), (0, 2, 7), (0, 0, 2), (2, 4, 1), (3, 4, 5)] [9, 5, 1, 5]).key,
    arrOn [(0, 2, 1), (1, 3, 7)] (arrTab arrCells arrPay).key]
  As.all fun R => As.all fun S => compOk (Tab.mk R.n R.val R.key) S
-- a `sum` middle column, with long and with `arr` summands
#guard let Ss := [sumTab [(false, 0, 1), (true, 1, 2), (false, 2, 1), (true, 0, 2), (false, 5, 3)] [5, 7, 5] [9, 4],
    sumTab [(true, 0, 2), (false, 1, 1), (false, 0, 9), (true, 1, 3)] [7, 5] [9, 8]]
  Ss.all fun R => Ss.all fun S => compOk (Tab.mk R.n R.val R.key) S
#guard let Ss := [sumOn [(false, 0, 1), (true, 1, 2), (false, 2, 1)] (arrTab arrCells arrPay).key (b := .long)
      (Alg.col [9, 4]),
    sumOn [(true, 0, 2), (false, 7, 1), (false, 0, 9)] (arrTab [(1, 3, 7), (0, 0, 2)] [9, 5, 1, 5]).key (b := .long)
      (Alg.col [9])]
  Ss.all fun R => Ss.all fun S => compOk (Tab.mk R.n R.val R.key) S

end Checks

#print axioms Tab.conv_holds
#print axioms Tab.comp_holds

end Rel
