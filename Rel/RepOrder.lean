module

public import Rel.RepCanon
public import Rel.ObjOrder

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! **`kasc`'s order is `Obj.lt`** (PLAN S5): on any side whose columns `kasc` reads (`ascCol` answers on each), a row
whose order codes (`seenKey`) are below another's holds an element below the other's in `Obj.lt`. An atom's key is
its order code (`Obj.key_ordCode`, floats included, decision G); a pair, a sum and an array compare their codes
column after column as `Obj.key` compares its parts. So the order law `Λ` reads holds at every object
(`Vals.lamLaw`): `kasc` refuses a general atom, the one type whose codes are not its order. -/

namespace Rel
open  Rel.Kernel Rel.Verify

/-- Code lists are equal where their `toNat` lists are. -/
theorem map_toNat_inj : ∀ {u v : List UInt64}, u.map UInt64.toNat = v.map UInt64.toNat → u = v
  | [], [], _ => rfl
  | a :: u, b :: v, h => by
    simp only [List.map_cons, List.cons.injEq] at h; rw [UInt64.toNat_inj.1 h.1, map_toNat_inj h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- **`lexLe` with distinct codes is the strict lexicographic order** of the rows' codes. -/
theorem lexLe_lt : ∀ (ks : List (Array UInt64)) {i j : Nat}, lexLe ks i j = true →
    ks.map (·[i]?.getD 0) ≠ ks.map (·[j]?.getD 0) →
    (ks.map (·[i]?.getD 0)).map UInt64.toNat < (ks.map (·[j]?.getD 0)).map UInt64.toNat
  | [], _, _, _, hne => absurd rfl hne
  | c :: cs, i, j, h, hne => by
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.cons_lt_cons_iff]
    rcases h with h | ⟨e, h⟩
    · exact .inl (UInt64.lt_iff_toNat_lt.1 h)
    · exact .inr ⟨congrArg _ e, lexLe_lt cs h fun h' => hne (by rw [List.map_cons, List.map_cons, e, h'])⟩

/-- Two lists of one length, different, each extended: ordered as the lists are. -/
theorem lt_of_append_lt : ∀ {l1 l2 r1 r2 : List Nat}, l1.length = l2.length → l1 ≠ l2 → l1 ++ r1 < l2 ++ r2 →
    l1 < l2
  | [], [], _, _, _, hne, _ => absurd rfl hne
  | a :: l1, b :: l2, r1, r2, hl, hne, h => by
    simp only [List.cons_append, List.cons_lt_cons_iff] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact .inl h
    · exact .inr ⟨rfl, lt_of_append_lt (by simpa using hl) (fun e => hne (by rw [e])) h⟩
  | [], _ :: _, _, _, hl, _, _ | _ :: _, [], _, _, hl, _, _ => by simp at hl

/-- Blocks of one length `k` over `0 … c-1`, concatenated: the first block where they differ orders them. -/
theorem flatMap_range_lt {k : Nat} {F G : Nat → List Nat} (hF : ∀ a, (F a).length = k) (hG : ∀ a, (G a).length = k) :
    ∀ c, (List.range c).flatMap F < (List.range c).flatMap G → ∃ p < c, (∀ q < p, F q = G q) ∧ F p < G p
  | 0, h => by simp only [List.range_zero, List.flatMap_nil] at h; exact absurd h (List.lt_irrefl _)
  | c + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append] at h
    by_cases e : (List.range c).flatMap F = (List.range c).flatMap G
    · rw [e, lt_append_left_iff] at h
      exact ⟨c, Nat.lt_succ_self c, fun q hq => (flatMap_eq_iff hF hG _).1 e q (List.mem_range.2 hq), by simpa using h⟩
    · obtain ⟨p, hp, hq, hlt⟩ := flatMap_range_lt hF hG c
        (lt_of_append_lt (by simp [List.length_flatMap, hF, hG]) e h)
      exact ⟨p, by omega, hq, hlt⟩

/-- **An array by its first difference**: equal up to `p`, then `xs` ends there and `ys` goes on, or both go on with
`xs`' element below `ys`'. -/
theorem Obj.lt_arr_of (b : Obj) : ∀ (p : Nat) (xs ys : List b.El), (∀ q < p, xs[q]? = ys[q]?) →
    (xs.length = p ∧ p < ys.length ∨ ∃ x y, xs[p]? = some x ∧ ys[p]? = some y ∧ b.lt x y) → (Obj.arr b).lt xs ys
  | 0, [], [], _, h => by simp at h
  | 0, [], y :: ys, _, _ => Obj.lt_nil_cons b y ys
  | 0, _ :: _, [], _, h => by simp at h
  | 0, x :: xs, y :: ys, _, h => (Obj.lt_cons b x y xs ys).2 (.inl (by simpa using h))
  | _ + 1, [], _, _, h => by simp at h
  | p + 1, x :: xs, [], he, _ => by have := he 0 (by omega); simp at this
  | p + 1, x :: xs, y :: ys, he, h => by
    obtain rfl : x = y := by have := he 0 (by omega); simpa using this
    exact (Obj.lt_cons b x x xs ys).2 (.inr ⟨rfl, Obj.lt_arr_of b p xs ys
      (fun q hq => by simpa using he (q + 1) (by omega)) (by simpa using h)⟩)

/-- **A nullable column's codes order its rows as `1+t`**: row `q`'s codes (`nulCodes`) are `[0, 0]` at a null and
`(if hasNul then [1] else []) ++ [code]` elsewhere, while `Obj.key` of `1+t` is `[0]` at the null (`inl ()`) and
`1 :: [code]` at a value (`inr`, `Obj.key_ordCode`): so code order is key order, the null least. -/
theorem Opt.lt_of_codes {t : QAtomicType} {n : USize} (x : Opt t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat)
    (h : (seenKey n [(.atom t, x.enc)] i).map UInt64.toNat < (seenKey n [(.atom t, x.enc)] i').map UInt64.toNat) :
    (Obj.opt (.atom t)).lt ((x.get i).elim (.inl ()) .inr) ((x.get i').elim (.inl ()) .inr) := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨hraw, hsz, -, hat⟩ := ascCol_ok hac
  obtain ⟨f, hof⟩ := hat t rfl
  have hv := ascCol_valid hac
  dsimp only at hv hraw
  have hs : (Enc.raw .i64 n x.enc).size = n.toNat := by rw [← hraw]; exact hsz
  obtain ⟨⟨w, fl, s⟩, hl, rfl⟩ := Option.map_eq_some_iff.1 hof
  have hg : t ≠ .general := by rintro rfl; simp [ascLayout, orderKind] at hl
  -- each row: the null, codes `[0, 0]` and key `[0]`; or a value, its codes ending in its code `c`, key `[1, c]`
  have row : ∀ q : Fin n.toNat,
      (hasNul x.enc = true ∧ (seenKey n [(.atom t, x.enc)] q).map UInt64.toNat = [0, 0] ∧
        (Obj.opt (.atom t)).key ((x.get q).elim (.inl ()) .inr) = [0]) ∨
      ∃ c, (seenKey n [(.atom t, x.enc)] q).map UInt64.toNat = (if hasNul x.enc then [1] else []) ++ [c] ∧
        (Obj.opt (.atom t)).key ((x.get q).elim (.inl ()) .inr) = [1, c] := fun q => by
    have hw := Array.getElem?_eq_getElem (show q.1 < _ by rw [hs]; exact q.2)
    rw [Opt.get_ne x q hg]
    simp only [seenKey, ascKeys, ascKey, nulCodes, nulWords, hof, Option.getD_some, List.append_nil]
    cases hn : x.isNul q
    · have h0 := (Opt.isNul_eq_false x q).1 hn
      obtain ⟨a, ha, hua, ex⟩ := Enc.get_raw_atom x.wf hg q h0
      rw [hw] at ha; cases ha
      refine .inr ⟨(ordCode w fl s (Enc.raw .i64 n x.enc)[q.1]).toNat, ?_, ?_⟩
      · cases hasNul x.enc <;> simp [Array.getElem?_mapIdx, hw, h0]
      · simp only [Bool.false_eq_true, if_false, Option.elim, ex]
        show 1 :: _ = _; rw [Obj.key_ordCode hl hg _ hua]
    · have h1 : (foRNuls n x.enc)[q.1]? = some 1 := by
        have e1 := foRNuls_bit n x.enc q.2
        have e2 : (foRNuls n x.enc)[q.1]? ≠ some 0 := fun e => absurd ((Opt.isNul_eq_false x q).2 e) (by simp [hn])
        rw [e1] at e2 ⊢; split at e2 <;> simp_all
      have hN : hasNul x.enc = true := by
        cases hN : hasNul x.enc; · rw [foRNuls_plain x.wf hN q.2] at h1; cases h1
        rfl
      refine .inl ⟨hN, ?_, rfl⟩
      simp [hN, Array.getElem?_mapIdx, hw, h1]
  show Obj.key _ _ < Obj.key _ _
  rcases row i with ⟨-, ci, ki⟩ | ⟨c, ci, ki⟩ <;> rcases row i' with ⟨hN', ci', ki'⟩ | ⟨c', ci', ki'⟩ <;>
    rw [ci, ci'] at h <;> rw [ki, ki']
  · exact absurd h (List.lt_irrefl _)
  · exact List.cons_lt_cons_iff.2 (.inl Nat.zero_lt_one)
  · rw [hN'] at h; rcases List.cons_lt_cons_iff.1 h with h | ⟨h, -⟩ <;> omega
  · refine List.cons_lt_cons_iff.2 (.inr ⟨rfl, ?_⟩)
    split at h <;> simpa using h

/-- **One column's codes order its elements**: `Opt.lt_of_codes` at a column with no null, every row `inr`. -/
theorem Arr.lt_of_codes {t : QAtomicType} {n : USize} (x : Arr t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat)
    (h : (seenKey n [(.atom t, x.enc)] i).map UInt64.toNat < (seenKey n [(.atom t, x.enc)] i').map UInt64.toNat) :
    (Obj.atom t).lt (x.get i) (x.get i') := by
  have hl := Opt.lt_of_codes (Opt.ofArr x) hc i i' h
  rw [Opt.get_ofArr, Opt.get_ofArr] at hl
  exact (Obj.lt_inr _ _ _ _).1 hl

/-- **Codes below, element below**, over any side whose columns `kasc` reads: row `i`'s codes (`seenKey`) below row
`i'`'s in the lexicographic order make `x`'s row `i` below its row `i'` in `Obj.lt`. -/
theorem ValsB.lt_of_codes : {A : Obj} → {o : Bool} → {n : USize} → (x : ValsB o A n) → (P : Fin n.toNat → Prop) →
    x.WFOn P → {es : List (AscKey × Enc)} → x.cols = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs →
    ∀ i i' : Fin n.toNat, P i → P i' → (seenKey n es i).map UInt64.toNat < (seenKey n es i').map UInt64.toNat →
      A.lt (x.row i) (x.row i')
  | .atom t, o, n, x, P, hw, es, hes, cs, hc, i, i', hPi, hPi', h => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes
    cases o
    · exact Arr.lt_of_codes x hc i i' h
    · have own : ∀ q, P q → ∃ v, Opt.get x q = some v := fun q hq =>
        Option.ne_none_iff_exists'.1 fun e => (hw q).1 hq e
      obtain ⟨v, hv⟩ := own i hPi
      obtain ⟨v', hv'⟩ := own i' hPi'
      have hl := Opt.lt_of_codes x hc i i' h
      rw [hv, hv'] at hl
      show (Obj.atom t).lt ((Opt.get x i).getD default) ((Opt.get x i').getD default)
      rw [hv, hv']
      exact (Obj.lt_inr _ _ _ _).1 hl
  | .prod a b, o, n, x, P, hw, es, hes, cs, hc, i, i', hPi, hPi', h => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys_append]
    rw [hs, hs, List.map_append, List.map_append] at h
    show (Obj.prod a b).lt (ValsB.row x.1 i, ValsB.row x.2 i) (ValsB.row x.1 i', ValsB.row x.2 i')
    rw [Obj.lt_prod]
    by_cases e : (seenKey n es1 i).map UInt64.toNat = (seenKey n es1 i').map UInt64.toNat
    · rw [e, lt_append_left_iff] at h
      exact .inr ⟨by rw [ValsB.row_of_codes x.1 P hw.1 h1 hc1 i i' hPi hPi' (map_toNat_inj e)],
        ValsB.lt_of_codes x.2 P hw.2 h2 hc2 i i' hPi hPi' h⟩
    · exact .inl (ValsB.lt_of_codes x.1 P hw.1 h1 hc1 i i' hPi hPi' (lt_of_append_lt (by simp [seenKey]) e h))
  | .arr b, o, n, ⟨c, lo, hi, f⟩, P, hw, es, hes, cs, hc, i, i', hPi, hPi', h => by
    obtain ⟨hfl, fs, hfs, ⟨cs', hcs'⟩, -⟩ := ValsB.cols_arr hw hes hc
    have ⟨_, _, hwb, hwf⟩ := hw
    obtain rfl : es = [(.cells n c lo.enc hi.enc fs, .pos)] := by
      simp only [ValsB.cols, hfs, bind, Except.bind, pure, Except.pure] at hes; exact (Except.ok.inj hes).symm
    have hr : ∀ q : Fin n.toNat, P q → (seenKey n [(AscKey.cells n c lo.enc hi.enc fs, .pos)] q).map UInt64.toNat =
        (List.range c.toNat).flatMap fun p =>
          (if p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 then 1 else 0) ::
          (ascKeys c fs).map fun z => if p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
            q.1.toUInt64 then (z[cellStart (Enc.raw .i64 n lo.enc) q.1.toUInt64 + p]?.getD 0).toNat else 0 :=
      fun q hq => by
        rw [seenKey_cells_raw q (hfl q hq).1 (hfl q hq).2]
        simp only [cellFns, List.map_flatMap, List.map_cons, List.map_map, Function.comp_def]
        congr 1; funext p
        by_cases hp : p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 <;> simp [hp]
    rw [hr i hPi, hr i' hPi'] at h
    obtain ⟨p, -, hq, hp⟩ := flatMap_range_lt (k := (ascKeys c fs).length + 1) (by simp) (by simp) _ h
    have bound : ∀ (q : Fin n.toNat), P q → ∀ k, k < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
        q.1.toUInt64 → cellStart (Enc.raw .i64 n lo.enc) q.1.toUInt64 + k < c.toNat := fun q hq k hk => by
      have := ValsB.cell_le (hfl q hq).1 (hfl q hq).2 hw hq; omega
    have get : ∀ (q : Fin n.toNat) (hq : P q) k (hk : k < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
        q.1.toUInt64), (ValsB.row (A := .arr b) ⟨c, lo, hi, f⟩ q)[k]? = some (f.row ⟨_, bound q hq k hk⟩) :=
      fun q hq k hk => by rw [ValsB.row_arr q (hfl q hq).1 (hfl q hq).2 (hwb q hq)]; simp [hk, bound q hq k hk]
    have len : ∀ q : Fin n.toNat, P q → (ValsB.row (A := .arr b) ⟨c, lo, hi, f⟩ q).length =
        cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 := fun q hq => by
      rw [ValsB.row_arr q (hfl q hq).1 (hfl q hq).2 (hwb q hq)]; simp
    -- below `p` the blocks agree: one reach flag, and where both reach, one element
    have flag : ∀ q < p, (q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 ↔
        q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64) := fun q hqp => by
      have := (List.cons.inj (hq q hqp)).1
      by_cases a1 : q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 <;>
        by_cases a2 : q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 <;>
        simp [a1, a2] at this ⊢
    have elem : ∀ q < p, ∀ (h1 : q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64)
        (h2 : q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64),
        (ValsB.row (A := .arr b) ⟨c, lo, hi, f⟩ i)[q]? = (ValsB.row (A := .arr b) ⟨c, lo, hi, f⟩ i')[q]? :=
      fun q hqp h1 h2 => by
        have e := (List.cons.inj (hq q hqp)).2
        simp only [if_pos h1, if_pos h2] at e
        rw [get i hPi q h1, get i' hPi' q h2]
        exact congrArg some (ValsB.row_of_codes f (fun _ => True) hwf hfs hcs' _ _ trivial trivial (map_toNat_inj (by
          simpa only [seenKey, List.map_map, Function.comp_def] using e)))
    apply Obj.lt_arr_of b p _ _ fun q hqp => ?_
    · simp only [List.cons_lt_cons_iff] at hp
      rcases hp with hlt | ⟨hfl, hlt⟩
      · by_cases a1 : p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 <;>
          by_cases a2 : p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 <;>
          simp [a1, a2] at hlt
        refine .inl ⟨?_, by rw [len i' hPi']; exact a2⟩
        rw [len i hPi]
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · omega
        · have := (flag (p - 1) (by omega)).2 (by omega); omega
      · by_cases a1 : p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64
        · have a2 : p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 := by
            refine Classical.byContradiction fun a2 => ?_; simp [a1, a2] at hfl
          simp only [if_pos a1, if_pos a2] at hlt
          exact .inr ⟨_, _, get i hPi p a1, get i' hPi' p a2, ValsB.lt_of_codes f (fun _ => True) hwf hfs hcs' _ _ trivial trivial (by
            simpa only [seenKey, List.map_map, Function.comp_def] using hlt)⟩
        · have a2 : ¬ p < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 := by
            intro a2; simp [a1, a2] at hfl
          simp only [if_neg a1, if_neg a2] at hlt
          exact absurd hlt (List.lt_irrefl _)
    · -- below `p` both cells reach `q`, or neither does and both rows end before `q`
      by_cases h1 : q < cellLen (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64
      · exact elem q hqp h1 ((flag q hqp).1 h1)
      · have h2 := mt (flag q hqp).2 h1
        rw [List.getElem?_eq_none (by rw [len i hPi]; omega), List.getElem?_eq_none (by rw [len i' hPi']; omega)]
  | .sum a b, o, n, s, P, hw, es, hes, cs, hc, i, i', hPi, hPi', h => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩
    · simp only [ValsB.cols, hv, Except.ok.injEq] at hes; subst hes
      obtain ⟨rfl, rfl⟩ := Obj.band_some hb
      have e : ∀ v, Obj.optEl hb v = v.elim (.inl ()) .inr := fun v => by
        unfold Obj.optEl; generalize Obj.band_some hb = p; obtain ⟨p1, p2⟩ := p; cases v <;> rfl
      simp only [ValsB.row, hv, e]
      exact Opt.lt_of_codes x hc i i' h
    simp only [ValsB.WFOn, hv] at hw
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := ValsB.cols_sum hv hes
    obtain ⟨c0, c12, hc0, hc12, -⟩ := mapM_append_ok (l1 := [(.atom .u1, tag.enc)]) (l2 := xs ++ ys) hc
    obtain ⟨c1, c2, hc1, hc2, -⟩ := mapM_append_ok hc12
    obtain ⟨hvt, heq⟩ := Arr.eq_of_codes tag hc0
    have hs : ∀ (e1 e2 : List (AscKey × Enc)) q, seenKey n (e1 ++ e2) q = seenKey n e1 q ++ seenKey n e2 q :=
      fun _ _ q => by simp [seenKey, ascKeys_append]
    rw [show (AscKey.atom .u1, tag.enc) :: (xs ++ ys) = [(AscKey.atom .u1, tag.enc)] ++ (xs ++ ys) from rfl,
      hs, hs, hs, hs, List.map_append, List.map_append, List.map_append, List.map_append] at h
    simp only [ValsB.row, hv]
    by_cases et : (seenKey n [(.atom .u1, tag.enc)] i).map UInt64.toNat =
        (seenKey n [(.atom .u1, tag.enc)] i').map UInt64.toNat
    · have ht := heq i i' (map_toNat_inj et)
      rw [et, lt_append_left_iff] at h
      rw [ht]
      cases htt : tag.get i'
      · have ky : seenKey n ys i = seenKey n ys i' :=
          ValsB.codes_of_unowned y _ hw.2.2 hys hc2 i i' (fun hh => absurd (hh.2.symm.trans (ht.trans htt)) (by decide))
            (fun hh => absurd (hh.2.symm.trans htt) (by decide))
        rw [ky] at h
        have hx : (seenKey n xs i).map UInt64.toNat < (seenKey n xs i').map UInt64.toNat := by
          by_cases e : (seenKey n xs i).map UInt64.toNat = (seenKey n xs i').map UInt64.toNat
          · rw [e] at h; exact absurd h (List.lt_irrefl _)
          · exact lt_of_append_lt (by simp [seenKey]) e h
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (Obj.lt_inl a b _ _).2 (ValsB.lt_of_codes x _ hw.2.1 hxs hc1 i i' ⟨hPi, ht.trans htt⟩ ⟨hPi', htt⟩ hx)
      · have kx : seenKey n xs i = seenKey n xs i' :=
          ValsB.codes_of_unowned x _ hw.2.1 hxs hc1 i i' (fun hh => absurd (hh.2.symm.trans (ht.trans htt)) (by decide))
            (fun hh => absurd (hh.2.symm.trans htt) (by decide))
        rw [kx, lt_append_left_iff] at h
        simp only [↓reduceIte]
        exact (Obj.lt_inr a b _ _).2 (ValsB.lt_of_codes y _ hw.2.2 hys hc2 i i' ⟨hPi, ht.trans htt⟩ ⟨hPi', htt⟩ h)
    · have hT := Arr.lt_of_codes tag hc0 i i' (lt_of_append_lt (by simp [seenKey]) et h)
      revert hT
      cases tag.get i <;> cases tag.get i' <;> intro hT
      · exact absurd hT (Obj.lt_irrefl _ _)
      · exact Obj.lt_inl_inr a b _ _
      · exact absurd hT (by decide)
      · exact absurd hT (Obj.lt_irrefl _ _)
  | .one, _, _, _, _, _, es, hes, _, _, _, _, _, _, h => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes; simp [seenKey, ascKeys] at h

/-- **`Λ`'s order law**: on a side of pairs whose columns `kasc` reads, two rows of one key whose codes
ascend strictly hold values ascending in `Obj.lt`. -/
theorem Vals.lamLaw {A B : Obj} {m : USize} (x : Vals (.prod A B) m) (hw : Vals.WF x) {es : List (AscKey × Enc)}
    (hes : ValsB.cols x = .ok es) {cs} (hc : es.mapM (ascCol m) = .ok cs) (i i' : Fin m.toNat)
    (h1 : (x.row i).1 = (x.row i').1) (hl : lexLe (ascKeys m es) i i' = true) (hne : seenKey m es i ≠ seenKey m es i') :
    B.lt (x.row i).2 (x.row i').2 := by
  have h := ValsB.lt_of_codes x (fun _ => True) hw hes hc i i' trivial trivial (lexLe_lt _ hl hne)
  change (Obj.prod A B).lt ((x.row i).1, (x.row i).2) ((x.row i').1, (x.row i').2) at h
  rw [Obj.lt_prod, h1] at h
  exact h.resolve_left (Obj.lt_irrefl _ _) |>.2

end Rel
