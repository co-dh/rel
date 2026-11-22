import Rel.RepCanon
import Rel.ObjOrder

/-! **`kasc`'s order is `Obj.lt`** (PLAN S5): on any side whose columns `kasc` reads (`ascCol` answers on each), a row
whose order codes (`seenKey`) are below another's holds an element below the other's in `Obj.lt`. An atom's key is
its order code (`Obj.key_ordCode`, floats included, decision G); a pair, a sum and an array compare their codes
column after column as `Obj.key` compares its parts. So the order law `Λ` reads holds at every object
(`Vals.lamLaw`): `kasc` refuses a general atom, the one type whose codes are not its order. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

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

/-- **One column's codes order its elements**: where `kasc` reads `x`, row `i`'s code below row `i'`'s is `x`'s
element at `i` below its element at `i'`, since an atom's key is its code (`Obj.key_ordCode`). -/
theorem Arr.lt_of_codes {t : QAtomicType} {n : USize} (x : Arr t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat)
    (h : (seenKey n [(.atom t, x.enc)] i).map UInt64.toNat < (seenKey n [(.atom t, x.enc)] i').map UInt64.toNat) :
    (Obj.atom t).lt (x.get i) (x.get i') := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨-, -, -, hat⟩ := ascCol_ok hac
  obtain ⟨f, hof⟩ := hat t rfl
  have hv := ascCol_valid hac
  obtain ⟨⟨w, fl, s⟩, hl, rfl⟩ := Option.map_eq_some_iff.1 hof
  have hg : t ≠ .general := by rintro rfl; simp [ascLayout, orderKind] at hl
  obtain ⟨a, ha, hua, ex⟩ := Arr.get_raw_atom x hv hg i
  obtain ⟨b, hb, hub, ey⟩ := Arr.get_raw_atom x hv hg i'
  simp only [seenKey, ascKeys, ascKey, List.append_nil, List.map_cons, List.map_nil, hof, Option.getD_some,
    Array.getElem?_map, ha, hb, Option.map_some] at h
  show Obj.key _ _ < Obj.key _ _
  rw [ex, ey, Obj.key_ordCode hl hg a hua, Obj.key_ordCode hl hg b hub]; exact h

/-- **Codes below, element below**, over any side whose columns `kasc` reads: row `i`'s codes (`seenKey`) below row
`i'`'s in the lexicographic order make `x`'s row `i` below its row `i'` in `Obj.lt`. -/
theorem Vals.lt_of_codes : {A : Obj} → {n : USize} → (x : Vals A n) → {es : List (AscKey × Enc)} →
    Vals.cols x = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs → ∀ i i' : Fin n.toNat,
      (seenKey n es i).map UInt64.toNat < (seenKey n es i').map UInt64.toNat → A.lt (x.row i) (x.row i')
  | .atom t, n, x, es, hes, cs, hc, i, i', h => by
    simp only [Vals.cols, Except.ok.injEq] at hes; subst hes
    exact Arr.lt_of_codes x hc i i' h
  | .prod a b, n, x, es, hes, cs, hc, i, i', h => by
    simp only [Vals.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys_append]
    rw [hs, hs, List.map_append, List.map_append] at h
    show (Obj.prod a b).lt (Vals.row x.1 i, Vals.row x.2 i) (Vals.row x.1 i', Vals.row x.2 i')
    rw [Obj.lt_prod]
    by_cases e : (seenKey n es1 i).map UInt64.toNat = (seenKey n es1 i').map UInt64.toNat
    · rw [e, lt_append_left_iff] at h
      exact .inr ⟨by rw [Vals.row_of_codes x.1 h1 hc1 i i' (map_toNat_inj e)], Vals.lt_of_codes x.2 h2 hc2 i i' h⟩
    · exact .inl (Vals.lt_of_codes x.1 h1 hc1 i i' (lt_of_append_lt (by simp [seenKey]) e h))
  | .arr b, n, ⟨c, lo, hi, f⟩, es, hes, cs, hc, i, i', h => by
    obtain ⟨fs, hfs, ⟨cs', hcs'⟩, -⟩ := Vals.cols_arr hes hc
    obtain rfl : es = [(.cells n c lo.enc hi.enc fs, .pos)] := by
      simp only [Vals.cols, hfs, bind, Except.bind, pure, Except.pure] at hes; exact (Except.ok.inj hes).symm
    have hr : ∀ q : Fin n.toNat, (seenKey n [(AscKey.cells n c lo.enc hi.enc fs, .pos)] q).map UInt64.toNat =
        (List.range c.toNat).flatMap fun p =>
          (if p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 then 1 else 0) ::
          (ascKeys c fs).map fun z => if p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
            q.1.toUInt64 then (z[cellStart c.toNat (Enc.raw .i64 n lo.enc) q.1.toUInt64 + p]?.getD 0).toNat else 0 :=
      fun q => by
        have e : seenKey n [(AscKey.cells n c lo.enc hi.enc fs, .pos)] q = (cellFns c.toNat (Enc.raw .i64 n lo.enc)
            (Enc.raw .i64 n hi.enc) (ascKeys c fs)).map (· q.1.toUInt64) := by
          simp [seenKey, ascKeys, ascKey, List.map_map, Function.comp_def, Enc.raw, q.2]
        rw [e]
        simp only [cellFns, List.map_flatMap, List.map_cons, List.map_map, Function.comp_def]
        congr 1; funext p
        by_cases hp : p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 <;> simp [hp]
    rw [hr, hr] at h
    obtain ⟨p, -, hq, hp⟩ := flatMap_range_lt (k := (ascKeys c fs).length + 1) (by simp) (by simp) _ h
    have bound : ∀ (q : Fin n.toNat) k, k < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
        q.1.toUInt64 → cellStart c.toNat (Enc.raw .i64 n lo.enc) q.1.toUInt64 + k < c.toNat := fun q k hk => by
      simp only [cellLen] at hk; omega
    have get : ∀ (q : Fin n.toNat) k (hk : k < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc)
        q.1.toUInt64), (Vals.row (A := .arr b) ⟨c, lo, hi, f⟩ q)[k]? = some (f.row ⟨_, bound q k hk⟩) :=
      fun q k hk => by rw [Vals.row_arr]; simp [hk, bound q k hk]
    have len : ∀ q : Fin n.toNat, (Vals.row (A := .arr b) ⟨c, lo, hi, f⟩ q).length =
        cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) q.1.toUInt64 := fun q => by
      rw [Vals.row_arr]; simp
    -- below `p` the blocks agree: one reach flag, and where both reach, one element
    have flag : ∀ q < p, (q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 ↔
        q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64) := fun q hqp => by
      have := (List.cons.inj (hq q hqp)).1
      by_cases a1 : q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 <;>
        by_cases a2 : q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 <;>
        simp [a1, a2] at this ⊢
    have elem : ∀ q < p, ∀ (h1 : q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64)
        (h2 : q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64),
        (Vals.row (A := .arr b) ⟨c, lo, hi, f⟩ i)[q]? = (Vals.row (A := .arr b) ⟨c, lo, hi, f⟩ i')[q]? :=
      fun q hqp h1 h2 => by
        have e := (List.cons.inj (hq q hqp)).2
        simp only [if_pos h1, if_pos h2] at e
        rw [get i q h1, get i' q h2]
        exact congrArg some (Vals.row_of_codes f hfs hcs' _ _ (map_toNat_inj (by
          simpa only [seenKey, List.map_map, Function.comp_def] using e)))
    apply Obj.lt_arr_of b p _ _ fun q hqp => ?_
    · simp only [List.cons_lt_cons_iff] at hp
      rcases hp with hlt | ⟨hfl, hlt⟩
      · by_cases a1 : p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64 <;>
          by_cases a2 : p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 <;>
          simp [a1, a2] at hlt
        refine .inl ⟨?_, by rw [len]; exact a2⟩
        rw [len]
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · omega
        · have := (flag (p - 1) (by omega)).2 (by omega); omega
      · by_cases a1 : p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64
        · have a2 : p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 := by
            refine Classical.byContradiction fun a2 => ?_; simp [a1, a2] at hfl
          simp only [if_pos a1, if_pos a2] at hlt
          exact .inr ⟨_, _, get i p a1, get i' p a2, Vals.lt_of_codes f hfs hcs' _ _ (by
            simpa only [seenKey, List.map_map, Function.comp_def] using hlt)⟩
        · have a2 : ¬ p < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i'.1.toUInt64 := by
            intro a2; simp [a1, a2] at hfl
          simp only [if_neg a1, if_neg a2] at hlt
          exact absurd hlt (List.lt_irrefl _)
    · -- below `p` both cells reach `q`, or neither does and both rows end before `q`
      by_cases h1 : q < cellLen c.toNat (Enc.raw .i64 n lo.enc) (Enc.raw .i64 n hi.enc) i.1.toUInt64
      · exact elem q hqp h1 ((flag q hqp).1 h1)
      · have h2 := mt (flag q hqp).2 h1
        rw [List.getElem?_eq_none (by rw [len]; omega), List.getElem?_eq_none (by rw [len]; omega)]
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩, es, hes, cs, hc, i, i', h => by
    obtain ⟨xs, ys, rfl, hrest⟩ := Vals.cols_sum hes
    obtain ⟨c0, c12, hc0, hc12, -⟩ := mapM_append_ok (l1 := [(.atom .u1, tag.enc)]) (l2 := xs ++ ys) hc
    obtain ⟨c1, c2, hc1, hc2, -⟩ := mapM_append_ok hc12
    obtain ⟨hv, heq⟩ := Arr.eq_of_codes tag hc0
    obtain ⟨xl0, xg, yl0, yg⟩ := hrest hv
    have hs : ∀ (e1 e2 : List (AscKey × Enc)) q, seenKey n (e1 ++ e2) q = seenKey n e1 q ++ seenKey n e2 q :=
      fun _ _ q => by simp [seenKey, ascKeys_append]
    rw [show (AscKey.atom .u1, tag.enc) :: (xs ++ ys) = [(AscKey.atom .u1, tag.enc)] ++ (xs ++ ys) from rfl,
      hs, hs, hs, hs, List.map_append, List.map_append, List.map_append, List.map_append] at h
    show (Obj.sum a b).lt (Vals.row (A := .sum a b) ⟨l, r, tag, idx, x, y⟩ i)
      (Vals.row (A := .sum a b) ⟨l, r, tag, idx, x, y⟩ i')
    simp only [Vals.row]
    by_cases et : (seenKey n [(.atom .u1, tag.enc)] i).map UInt64.toNat =
        (seenKey n [(.atom .u1, tag.enc)] i').map UInt64.toNat
    · have ht := heq i i' (map_toNat_inj et)
      rw [et, lt_append_left_iff] at h
      rw [ht]
      cases htt : tag.get i'
      · have ky : seenKey n ys i = seenKey n ys i' := by
          by_cases h0 : 0 < r.toNat
          · obtain ⟨g, hg, hrow⟩ := yg h0
            exact Vals.codes_of_row g hg hc2 i i' (by rw [hrow, hrow, ht, htt]; simp)
          · rw [yl0 (by omega)]; simp [seenKey, ascKeys]
        rw [ky] at h
        have hx : (seenKey n xs i).map UInt64.toNat < (seenKey n xs i').map UInt64.toNat := by
          by_cases e : (seenKey n xs i).map UInt64.toNat = (seenKey n xs i').map UInt64.toNat
          · rw [e] at h; exact absurd h (List.lt_irrefl _)
          · exact lt_of_append_lt (by simp [seenKey]) e h
        by_cases h0 : 0 < l.toNat
        · obtain ⟨g, hg, hrow⟩ := xg h0
          have := Vals.lt_of_codes g hg hc1 i i' hx
          rw [hrow, hrow, ht, htt] at this
          simp only [Bool.false_eq_true, ↓reduceIte, dif_pos h0]
          exact (Obj.lt_inl a b _ _).2 (by simpa using this)
        · rw [xl0 (by omega)] at hx; simp [seenKey, ascKeys] at hx
      · have kx : seenKey n xs i = seenKey n xs i' := by
          by_cases h0 : 0 < l.toNat
          · obtain ⟨g, hg, hrow⟩ := xg h0
            exact Vals.codes_of_row g hg hc1 i i' (by rw [hrow, hrow, ht, htt]; simp)
          · rw [xl0 (by omega)]; simp [seenKey, ascKeys]
        rw [kx, lt_append_left_iff] at h
        by_cases h0 : 0 < r.toNat
        · obtain ⟨g, hg, hrow⟩ := yg h0
          have := Vals.lt_of_codes g hg hc2 i i' h
          rw [hrow, hrow, ht, htt] at this
          simp only [↓reduceIte, dif_pos h0]
          exact (Obj.lt_inr a b _ _).2 (by simpa using this)
        · rw [yl0 (by omega)] at h; simp [seenKey, ascKeys] at h
    · have hT := Arr.lt_of_codes tag hc0 i i' (lt_of_append_lt (by simp [seenKey]) et h)
      revert hT
      cases tag.get i <;> cases tag.get i' <;> intro hT
      · exact absurd hT (Obj.lt_irrefl _ _)
      · exact Obj.lt_inl_inr a b _ _
      · exact absurd hT (by decide)
      · exact absurd hT (Obj.lt_irrefl _ _)
  | .one, _, _, es, hes, _, _, _, _, h => by
    simp only [Vals.cols, Except.ok.injEq] at hes; subst hes; simp [seenKey, ascKeys] at h

/-- **`Λ`'s order law**: on a side of pairs whose columns `kasc` reads, two rows of one key whose codes
ascend strictly hold values ascending in `Obj.lt`. -/
theorem Vals.lamLaw {A B : Obj} {m : USize} (x : Vals (.prod A B) m) {es : List (AscKey × Enc)}
    (hes : Vals.cols x = .ok es) {cs} (hc : es.mapM (ascCol m) = .ok cs) (i i' : Fin m.toNat)
    (h1 : (x.row i).1 = (x.row i').1) (hl : lexLe (ascKeys m es) i i' = true) (hne : seenKey m es i ≠ seenKey m es i') :
    B.lt (x.row i).2 (x.row i').2 := by
  have h := Vals.lt_of_codes x hes hc i i' (lexLe_lt _ hl hne)
  change (Obj.prod A B).lt ((x.row i).1, (x.row i).2) ((x.row i').1, (x.row i').2) at h
  rw [Obj.lt_prod, h1] at h
  exact h.resolve_left (Obj.lt_irrefl _ _) |>.2

end Rel
