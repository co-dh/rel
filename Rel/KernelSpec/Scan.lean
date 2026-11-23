module

public import Rel.Kernel.Scan
public import Rel.KernelSpec.Ids
public import Rel.KernelSpec.Search

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

open Rel.Ext

/-! The scan primitive's law (design §4, `raw_scan`; `raw_kscan` until 6.11 takes the name back from the driver's): an
answer `kscan` returns is the segmented prefix fold of `Op.eval` over the raw rows of its columns, cut to the answer
type's width. -/

namespace Rel.Kernel
open Column

theorem rawAll_ok {t : QAtomicType} {n : USize} {e : Enc} {a : Array UInt64} (h : rawAll t n e = .ok a) :
    a = e.raw t n ∧ a.size = n.toNat := by
  unfold rawAll at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem mapM_rawAll {s : QAtomicType} {n : USize} :
    ∀ {es : List Enc} {cs : List (Array UInt64)}, es.mapM (rawAll s n) = .ok cs →
      cs = es.map (·.raw s n) ∧ ∀ e ∈ es, (e.raw s n).size = n.toNat
  | [], cs, h => by cases h; simp
  | e :: es, cs, h => by
    rw [List.mapM_cons] at h
    cases ha : rawAll s n e with
    | error m => rw [ha] at h; cases h
    | ok a =>
      cases hb : es.mapM (rawAll s n) with
      | error m => rw [ha, hb] at h; cases h
      | ok bs =>
        rw [ha, hb] at h; cases h
        obtain ⟨rfl, hs⟩ := rawAll_ok ha
        obtain ⟨rfl, hr⟩ := mapM_rawAll hb
        exact ⟨rfl, by simpa [hs] using hr⟩

/-- `kscan`'s row fold: from no rows, it answers one word a row, row `i`'s being `op` folded over the other columns'
row `i` from the carry `kscanRow` picks. -/
theorem foldlM_kscanRow (op : Op) (g seed : Array UInt64) (xs : List (Array UInt64)) :
    ∀ (m : Nat) (out : Array UInt64), (List.range m).foldlM (kscanRow op g seed xs) #[] = .ok out →
      out.size = m ∧ ∀ i (hi : i < out.size), xs.foldlM (fun a x => op.eval a (x[i]?.getD 0))
        (if 0 < i ∧ g[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else seed[i]?.getD 0) = .ok out[i] := by
  intro m
  induction m with
  | zero => intro out h; cases h; exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | succ m ih =>
    intro out h
    rw [List.range_succ, List.foldlM_append] at h
    cases hm : (List.range m).foldlM (kscanRow op g seed xs) #[] with
    | error e => rw [hm] at h; cases h
    | ok mid =>
      obtain ⟨hs, hrow⟩ := ih mid hm
      cases ha : xs.foldlM (fun a x => op.eval a (x[m]?.getD 0))
          (if 0 < m ∧ g[m]?.getD 0 = 0 then mid[m - 1]?.getD 0 else seed[m]?.getD 0) with
      | error e => simp [hm, kscanRow, ha, bind, Except.bind, Functor.map, Except.map] at h
      | ok a =>
        simp only [hm, kscanRow, ha, bind, Except.bind, List.foldlM_cons, List.foldlM_nil, Functor.map, Except.map,
          pure, Except.pure] at h
        cases h
        refine ⟨by simp [hs], fun i hi => ?_⟩
        simp only [Array.size_push] at hi
        -- the carry at row `i ≤ m` reads row `i - 1 < m`, which the push leaves as it was
        have hc : (if 0 < i ∧ g[i]?.getD 0 = 0 then (mid.push a)[i - 1]?.getD 0 else seed[i]?.getD 0) =
            (if 0 < i ∧ g[i]?.getD 0 = 0 then mid[i - 1]?.getD 0 else seed[i]?.getD 0) := by
          by_cases h0 : 0 < i
          · simp only [Array.getElem?_push, show i - 1 ≠ mid.size by omega, if_false]
          · simp [h0]
        rw [hc]
        by_cases him : i < m
        · rw [Array.getElem_push_lt (by omega)]; exact hrow i (by omega)
        · obtain rfl : i = m := by omega
          subst hs
          rw [Array.getElem_push_eq]; exact ha

/-- `l.mapM f` answers one word per word, each `f` of the word in its place. -/
theorem mapM_get {f : UInt64 → Except String UInt64} :
    ∀ {l l' : List UInt64}, l.mapM f = .ok l' → l'.length = l.length ∧ ∀ i < l.length, f (l[i]?.getD 0) = .ok (l'[i]?.getD 0)
  | [], l', h => by cases h; simp
  | x :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error m => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hl : l.mapM f with
      | error m => simp [hx, hl, bind, Except.bind] at h
      | ok ys =>
        simp only [hx, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨hn, hr⟩ := mapM_get hl
        refine ⟨by simp [hn], fun i hi => ?_⟩
        cases i with
        | zero => simpa using hx
        | succ i => simpa using hr i (by simpa using hi)

/-- **`chainAll c` is `chain c` word by word.** -/
theorem chainAll_ok {c : List (Op × UInt64)} {a b : Array UInt64} (h : chainAll c a = .ok b) :
    b.size = a.size ∧ ∀ i < a.size, chain c (a[i]?.getD 0) = .ok (b[i]?.getD 0) := by
  unfold chainAll at h
  cases hm : a.toList.mapM (chain c) with
  | error m => simp [hm, Functor.map, Except.map] at h
  | ok l =>
    simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h; subst h
    obtain ⟨hn, hr⟩ := mapM_get hm
    exact ⟨by simpa using hn, fun i hi => by simpa using hr i (by simpa using hi)⟩

/-- **`kscan`'s columns through `chain pre`**: each column of `es` held `n` raw words, and its chained column holds `n`
words, `chain pre` of the raw word in each place. -/
theorem mapM_chain {s : QAtomicType} {n : USize} {pre : List (Op × UInt64)} :
    ∀ {es : List Enc} {cs : List (Array UInt64)}, es.mapM (fun e => rawAll s n e >>= chainAll pre) = .ok cs →
      cs.length = es.length ∧ ∀ p ∈ es.zip cs, (p.1.raw s n).size = n.toNat ∧ p.2.size = n.toNat ∧
        ∀ i < n.toNat, chain pre ((p.1.raw s n)[i]?.getD 0) = .ok (p.2[i]?.getD 0)
  | [], cs, h => by cases h; simp
  | e :: es, cs, h => by
    rw [List.mapM_cons] at h
    generalize hb : es.mapM (fun e => rawAll s n e >>= chainAll pre) = B at h
    cases ha : rawAll s n e with
    | error m => simp [ha, bind, Except.bind] at h
    | ok a =>
      obtain ⟨rfl, hs⟩ := rawAll_ok ha
      cases hc : chainAll pre (e.raw s n) with
      | error m => simp [ha, hc, bind, Except.bind] at h
      | ok c =>
        cases B with
        | error m => simp [ha, hc, bind, Except.bind] at h
        | ok bs =>
          simp only [ha, hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
          obtain ⟨hcs, hcr⟩ := chainAll_ok hc
          obtain ⟨hl, hP⟩ := mapM_chain hb
          refine ⟨by simp [hl], fun p hp => ?_⟩
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hs, hcs.trans hs, fun i hi => hcr i (by omega)⟩
          · exact hP p hp

/-- The empty chain is the identity. -/
theorem chainAll_nil : chainAll [] = pure := by
  funext a
  have : ∀ l : List UInt64, l.mapM (chain []) = .ok l := fun l => by
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.mapM_cons, ih]; rfl
  simp [chainAll, this, Functor.map, Except.map, pure, Except.pure]


/-- A lock-step source list, every source holding `n` rows, is read as its columns alone. -/
theorem mapM_pairs {s : QAtomicType} {n : USize} {pre : List (Op × UInt64)} :
    ∀ {es : List (USize × Enc)}, (∀ p ∈ es, p.1 = n) →
      es.mapM (fun p => rawAll s p.1 p.2 >>= chainAll pre) = (es.map (·.2)).mapM (fun e => rawAll s n e >>= chainAll pre)
  | [], _ => rfl
  | p :: es, h => by
    rw [List.mapM_cons, List.map_cons, List.mapM_cons, h p (by simp), mapM_pairs fun q hq => h q (by simp [hq])]

/-- **`kscanCols` of a call that is no stream**: every source held `n` rows, and the columns are the sources' own. -/
theorem kscanCols_lock {op : Op} {s : QAtomicType} {n : USize} {es : List (USize × Enc)} {pre post : List (Op × UInt64)}
    {ws : List (Array UInt64)} {ns : Array UInt64} (hs : kscanStream op es pre post = false)
    (h : kscanCols op s n es pre post = .ok (ws, ns)) :
    (∀ p ∈ es, p.1 = n) ∧ ns = #[] ∧ (es.map (·.2)).mapM (fun e => rawAll s n e >>= chainAll pre) = .ok ws := by
  unfold kscanCols at h
  simp only [hs, Bool.false_eq_true, if_false] at h
  cases hm : es.mapM (fun p => rawAll s p.1 p.2 >>= chainAll pre) with
  | error m => rw [hm] at h; simp [bind, Except.bind] at h
  | ok ws' =>
    rw [hm] at h; simp only [bind, Except.bind] at h
    by_cases hn : es.any (·.1 != n) = true
    · simp [hn] at h
    · have hl : ∀ p ∈ es, p.1 = n := fun p hp =>
        Classical.byContradiction fun hp' => hn (List.any_eq_true.mpr ⟨p, hp, by simpa using hp'⟩)
      simp only [hn, Bool.false_eq_true, if_false] at h
      cases hf : es.forM fun p => noNul "kscan" p.1 p.2 with
      | error m => simp [hf, pure, Except.pure] at h
      | ok u =>
        simp only [hf, pure, Except.pure] at h
        cases h
        exact ⟨hl, rfl, by rw [← mapM_pairs hl]; exact hm⟩

/-- **`raw_scan`** (design §4), at any segment marks and chains: an answer of `kscan` read back at its type `t` of `w`
bytes is the word sequence `out` of one word a row, each cut to `t`'s width (a boolean's to its low bit). `out` is
`chain post` of `out₀`, whose row `i` is `op` folded over the columns after the first at row `i` (each word through
`chain pre`: the columns `cs'`), from `out₀`'s previous row, or from the first column's row `i` (`c'`) where the marks
`g` (`segAll`) start a segment there (row 0 always); every column held `n` raw words. With `rev` every column, `g`
included, is reversed before the fold and `out` after it. The fold result `r.2` is `out`'s last word (the row visited
last) cut the same way, `none` where `out` is empty. -/
theorem raw_kscanChain (op : Op) (rev : Bool) (s t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize)
    (seg : Option Enc) (es : List (USize × Enc)) (pre post : List (Op × UInt64)) (r : Enc × Option UInt64)
    (hs : kscanStream op es pre post = false) (h : kscan op rev s t n seg es pre post = .ok r) :
    ∃ g, segAll n seg = .ok g ∧ (∀ p ∈ es, p.1 = n) ∧
    ∃ c' cs', (es.map (·.2)).mapM (fun e => rawAll s n e >>= chainAll pre) = .ok (c' :: cs') ∧
    ∃ out₀ out : Array UInt64, out₀.size = n.toNat ∧ chainAll post out₀ = .ok out ∧
      r.1.raw t n = (if rev then out.reverse else out).map
        (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      r.2 = out.back?.map (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      ∀ i (hi : i < out₀.size),
        (cs'.map fun a => if rev then a.reverse else a).foldlM (fun a x => op.eval a (x[i]?.getD 0))
          (if 0 < i ∧ (if rev then g.reverse else g)[i]?.getD 0 = 0
           then out₀[i - 1]?.getD 0 else (if rev then c'.reverse else c')[i]?.getD 0) = .ok out₀[i] := by
  obtain ⟨e, v⟩ := r
  dsimp only
  unfold kscan at h
  by_cases hd : kscanRefuses op n es pre post = true
  · simp only [hd, ↓reduceIte] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i g hg
  split at h; · cases h
  rename_i cs hc
  split at h; · cases h
  rename_i c cs' ns
  obtain ⟨hl, hns, hcc⟩ := kscanCols_lock hs hc
  split at h; · cases h
  rename_i out₀ hf
  split at h; · cases h
  rename_i out hp
  split at h; · cases h
  rename_i w' hw
  rw [ht] at hw; cases hw
  split at h; · cases h
  rename_i nl hnl
  obtain ⟨hos, hrow⟩ := foldlM_kscanRow _ _ _ _ _ _ hf
  have hps := (chainAll_ok hp).1
  subst hns
  cases h
  refine ⟨g, hg, hl, c, cs', hcc, out₀, out, hos, hp, ?_, rfl, hrow⟩
  replace hos : out.size = n.toNat := hps.trans hos
  -- every `foR` is read cut to `t`'s width, a boolean's being one bit
  have hraw : ∀ M P : ByteArray, (Enc.foR M P : Enc).raw t n = (Array.range n.toNat).map fun i =>
      UInt64.ofNat ((Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (if t = .u1 then 1 else 8 * w)) := by
    intro M P
    by_cases hb : t = .u1
    · subst hb; simp [Enc.raw]
    · rw [Verify.raw_foR t w ht hb]; simp [hb]
  -- the words, encoded whole at 8 bytes, read back exactly (`foRBits_encode`), then cut to `t`'s width
  have h8 : USize.ofNat32 8 (by decide) = (8 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp [h])
  generalize hO : (if rev then out.reverse else out) = O
  have hOs : O.size = n.toNat := by subst hO; split <;> simp [hos]
  generalize hW : O.map (fun v => if t = .u1 then v % 2 else v) = W
  have hWs : W.size = n.toNat := by subst hW; simp [hOs]
  generalize hX : W.foldl (init := ByteArray.empty) (fun acc w => Column.pushBits acc w 8) = X
  obtain ⟨hxs, -, hxg⟩ := Verify.foldl_pushBits (fun v => v) 8 (by decide) W.toList ByteArray.empty
  rw [Array.foldl_toList, hX] at hxs hxg
  simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
  rw [hraw]
  apply Array.ext (by simp [hOs])
  intro i h1 h2
  have hi : i < W.size := by simpa [hWs] using h1
  have hu : (Coc.keyAt 8 X i).toUInt64 = W[i] := by
    have h1 : (Coc.keyAt 8 X i).toUInt64.toNat % 2 ^ (8 * 8) = (Column.bitsAt X (i * 8) 8).toNat :=
      Verify.sext_bits 8 (by decide) (by decide) _ (Verify.bitsAt_lt _ _ _ (by decide))
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), Nat.mul_comm, hxg i (by simpa using hi),
      Verify.ofNat_toNat_mod64, Array.getElem_toList] at h1
    exact UInt64.toNat_inj.mp h1
  simp only [Array.getElem_map, Array.getElem_range, h8, Coc.encode,
    show ((#[] : Array UInt64).any fun x : UInt64 => x != 0) = false by simp, Bool.false_eq_true, if_false]
  rw [Verify.foRBits_encode Column.lgEnc (by decide) 8 (by decide) (by decide) X i (by rw [hxs]; omega), hu]
  subst hW
  by_cases hb : t = .u1 <;> simp [hb]

/-- **`raw_scan` at a column of segment marks and no chain** (`raw_kscanChain`): every column, `seg` included, held `n`
raw words, and they are the columns the fold reads. -/
theorem raw_kscan (op : Op) (rev : Bool) (s t : QAtomicType) (w : Nat) (ht : t.width = some w) (n : USize)
    (seg : Enc) (es : List (USize × Enc)) (r : Enc × Option UInt64) (hs : kscanStream op es [] [] = false)
    (h : kscan op rev s t n seg es = .ok r) :
    (seg.raw .u1 n).size = n.toNat ∧ (∀ p ∈ es, p.1 = n ∧ (p.2.raw s n).size = n.toNat) ∧
    ∃ c cs, es.map (·.2) = c :: cs ∧ ∃ out : Array UInt64, out.size = n.toNat ∧
      r.1.raw t n = (if rev then out.reverse else out).map
        (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      r.2 = out.back?.map (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      ∀ i (hi : i < out.size),
        ((cs.map (·.raw s n)).map fun a => if rev then a.reverse else a).foldlM (fun a x => op.eval a (x[i]?.getD 0))
          (if 0 < i ∧ (if rev then (seg.raw .u1 n).reverse else seg.raw .u1 n)[i]?.getD 0 = 0
           then out[i - 1]?.getD 0 else (if rev then (c.raw s n).reverse else c.raw s n)[i]?.getD 0) = .ok out[i] := by
  obtain ⟨g, hg, hl, c', cs', hc, out₀, out, hos, hp, he, hv, hrow⟩ := raw_kscanChain op rev s t w ht n seg es [] [] r hs h
  simp only [segAll] at hg
  obtain ⟨rfl, hgs⟩ := rawAll_ok hg
  rw [chainAll_nil] at hp hc; cases hp
  simp only [bind_pure] at hc
  obtain ⟨hl', hsz⟩ := mapM_rawAll hc
  cases es with
  | nil => cases hl'
  | cons p ps =>
    simp only [List.map_cons, List.cons.injEq] at hl'; obtain ⟨rfl, rfl⟩ := hl'
    exact ⟨hgs, fun q hq => ⟨hl q hq, hsz q.2 (List.mem_map_of_mem hq)⟩, p.2, ps.map (·.2), rfl, _, hos, he, hv, hrow⟩

/-- **The fold result is the answer's last-visited row**: `kscan`'s second component is word `n − 1` of its answer read
at `t` (word 0 under `rev`), and `none` exactly at `n = 0`. -/
theorem kscan_last {op : Op} {rev : Bool} {s t : QAtomicType} {w : Nat} (ht : t.width = some w) {n : USize}
    {seg : Option Enc} {es : List (USize × Enc)} {pre post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hs : kscanStream op es pre post = false) (h : kscan op rev s t n seg es pre post = .ok r) :
    r.2 = (r.1.raw t n)[if rev then 0 else n.toNat - 1]? := by
  obtain ⟨-, -, -, -, -, -, out₀, out, hos₀, hp, he, hv, -⟩ := raw_kscanChain op rev s t w ht n seg es pre post r hs h
  have hos : out.size = n.toNat := (chainAll_ok hp).1.trans hos₀
  rw [he, hv, Array.back?_eq_getElem?]
  rcases Nat.eq_zero_or_pos out.size with h0 | h0
  · cases rev <;> simp [h0]
  · cases rev <;> simp [hos, show 0 < n.toNat by omega] <;> exact ⟨_, Array.getElem?_eq_getElem (by omega), rfl⟩

end Rel.Kernel

