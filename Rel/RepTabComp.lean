import Rel.Run.Comp
import Rel.RepCanon
import Rel.Run.CRelDef
import Rel.KernelSpec.Scatter
import Rel.KernelSpec.Scan

/-! The laws of `Tab.conv` and `Tab.comp` (`Rel/Run/Comp.lean`), from the five kernels' laws and `Tab.canon_holds`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

/-- **`kscatter` under any `op`, on words**: the answer reads back as `scatterWords` of its arguments' words. -/
theorem kscatter_words {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64} (h : kscatter op m ix e n fill = .ok o) :
    (raw .i64 m ix).size = m.toNat ∧ (raw .i64 m e).size = m.toNat ∧
      scatterWords op (raw .i64 m ix) (raw .i64 m e) n.toNat fill = .ok (raw .i64 n o) := by
  unfold kscatter at h
  cases hi : foRWords "scatter: ix" m ix with
  | error s => simp [hi, bind, Except.bind] at h
  | ok is' =>
    cases he : foRWords "scatter: e" m e with
    | error s => simp [hi, he, bind, Except.bind] at h
    | ok es' =>
      obtain ⟨rfl, hisz⟩ := foRWords_raw _ _ _ _ hi
      obtain ⟨rfl, hesz⟩ := foRWords_raw _ _ _ _ he
      cases hw : scatterWords op (raw .i64 m ix) (raw .i64 m e) n.toNat fill with
      | error s => simp [hi, he, hw, bind, Except.bind] at h
      | ok ws =>
        simp only [hi, he, hw, bind, Except.bind, pure, Except.pure] at h
        have h8 : USize.ofNat32 8 (by decide) = 8 := USize.toNat_inj.mp (by simp)
        rw [h8] at h
        have hs := scatterWords_size hw
        have ho := (Except.ok.inj h).symm
        obtain ⟨hxs, -, hxg⟩ := foldl_pushBits (fun v => v) 8 (by decide) ws.toList ByteArray.empty
        rw [Array.foldl_toList] at hxs hxg
        simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
        refine ⟨hisz, hesz, congrArg Except.ok ?_⟩
        have h88 : (8 : USize) = (8 : Nat).toUSize := rfl
        rw [ho, Coc.encode, h88, raw_encodeAt .i64 8 rfl (by decide) Column.lgEnc (by decide) _ n (by rw [hxs]; omega),
          raw_bytes .i64 8 rfl (by decide)]
        refine (Array.ext (by simp [hs]) fun i h1 _ => ?_).symm
        simp only [Array.getElem_map, Array.getElem_range]
        rw [Nat.mul_comm, hxg i (by simp at h1; omega), ofNat_toNat_mod64, Array.getElem_toList]

/-- **`colConst n w` is `n` words `w`.** -/
theorem colConst_raw {n : USize} {w : UInt64} {e : Enc} (h : colConst n w = .ok e) :
    raw .i64 n e = Array.replicate n.toNat w := by
  obtain ⟨-, -, hw⟩ := kscatter_words h
  have h0 : (raw .i64 0 (.pos : Enc)).size = 0 := by simp [raw]
  unfold scatterWords at hw
  rw [h0] at hw
  exact (Except.ok.inj hw).symm

/-- **`colConst n w` read as booleans is `n` words `w % 2`** (`kscan`'s `seg`). -/
theorem colConst_u1 {n : USize} {w : UInt64} {e : Enc} (h : colConst n w = .ok e) :
    ∀ i < n.toNat, (raw .u1 n e)[i]?.getD 0 = UInt64.ofNat (w.toNat % 2) := by
  intro i hi
  obtain ⟨hfo, -⟩ := raw_scatter 0 .pos .pos n w e h
  have he := colConst_raw h
  generalize Coc.encode _ _ = q at hfo; subst hfo
  have hu : raw .u1 n (.foR q.1 q.2 : Enc) = (raw .i64 n (.foR q.1 q.2 : Enc)).map fun w => UInt64.ofNat (w.toNat % 2) := by
    simp only [raw, QAtomicType.width, Array.map_map]
    refine Array.ext (by simp) fun j _ _ => ?_
    simp
  rw [hu, Array.getElem?_map, he, Array.getElem?_replicate, if_pos hi]; rfl

/-- `kscan` at `i64` writes its words as they are: the cut to `8 * 8` bits is the identity. -/
private theorem mod_i64 (v : UInt64) : UInt64.ofNat (v.toNat % 2 ^ (if QAtomicType.i64 = .u1 then 1 else 8 * 8)) = v := by
  simp only [if_neg (by decide : QAtomicType.i64 ≠ .u1)]; exact ofNat_toNat_mod64 v

/-- **`colPrefix op n a` is the running fold of `op` from `0`**: row `i` is `op` of row `i - 1` (`0` at row `0`) and
`a[i]`. -/
theorem colPrefix_raw {op : Op} {n : USize} {a e : Enc} (h : colPrefix op n a = .ok e) :
    (raw .i64 n a).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧ ∀ i < n.toNat,
      op.eval (if i = 0 then 0 else (raw .i64 n e)[i - 1]?.getD 0) ((raw .i64 n a)[i]?.getD 0) =
        .ok ((raw .i64 n e)[i]?.getD 0) := by
  unfold colPrefix at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz
  obtain ⟨-, hxs, c, cs, hc, out, hout, he, hrow⟩ := raw_kscan op false .i64 .i64 8 rfl n z [z, a] e h
  simp only [List.cons.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte, mod_i64, Array.map_id'] at he hrow
  have hz0 := colConst_raw hz
  have hzs := colConst_u1 hz
  refine ⟨hxs a (by simp), by rw [he, hout], fun i hi => ?_⟩
  have := hrow i (by rw [hout]; exact hi)
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, hzs i hi, hz0,
    Array.getElem?_replicate, if_pos hi, Option.getD_some] at this
  rw [he]
  simp only [Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some]
  rw [← this]
  by_cases h0 : i = 0
  · subst h0; simp only [Nat.lt_irrefl, false_and, ↓reduceIte]
    cases op.eval 0 ((raw .i64 n a)[0]?.getD 0) <;> rfl
  · simp only [if_neg h0, show 0 < i by omega, true_and, show UInt64.ofNat (UInt64.toNat 0 % 2) = 0 from rfl,
      ↓reduceIte]
    cases op.eval (out[i - 1]?.getD 0) ((raw .i64 n a)[i]?.getD 0) <;> rfl

/-- **`colMap op n a b` is `op` row by row**: both arguments hold `n` words, and row `i` of the answer is
`op.eval a[i] b[i]`. -/
theorem colMap_raw {op : Op} {n : USize} {a b e : Enc} (h : colMap op n a b = .ok e) :
    (raw .i64 n a).size = n.toNat ∧ (raw .i64 n b).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧
      ∀ i < n.toNat, op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) = .ok ((raw .i64 n e)[i]?.getD 0) := by
  unfold colMap at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i one hone
  obtain ⟨hg, hxs, c, cs, hc, out, hout, he, hrow⟩ := raw_kscan op false .i64 .i64 8 rfl n one [a, b] e h
  simp only [List.cons.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte, mod_i64, Array.map_id'] at he hrow
  -- `one` read as booleans: each word `1`, so every row starts a segment
  have hseg : ∀ i < n.toNat, (raw .u1 n one)[i]?.getD 0 ≠ 0 := fun i hi => by rw [colConst_u1 hone i hi]; decide
  refine ⟨hxs a (by simp), hxs b (by simp), by rw [he, hout], fun i hi => ?_⟩
  have := hrow i (by rw [hout]; exact hi)
  have hc : ¬(0 < i ∧ (raw .u1 n one)[i]?.getD 0 = 0) := fun h => hseg i hi h.2
  simp only [hc, ↓reduceIte, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil] at this
  rw [he]
  simp only [Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some]
  rw [← this]; cases op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) <;> rfl

/-- The fold `scatterWords .add` runs, over any rows `l` from any start `o` of `n` cells, every index below `n`: cell
`j` ends as `o[j]` plus the sum of `es[k]` over the rows `k` of `l` that name `j`. -/
private theorem scatterAddFold (is es : Array UInt64) (n : Nat) :
    ∀ (l : List Nat) (o : Array UInt64), o.size = n → (∀ k ∈ l, (is[k]?.getD 0).toNat < n) →
      ∃ o', l.foldlM (fun (o : Array UInt64) (k : Nat) =>
          let i : UInt64 := is[k]?.getD 0
          if i.toNat < n then
            match Op.add.eval (o[i.toNat]?.getD 0) (es[k]?.getD 0) with
            | .ok v => Except.ok (o.setIfInBounds i.toNat v)
            | .error s => Except.error s!"scatter: {s} at row {k}"
          else Except.error (ε := String) s!"scatter: index {i} at row {k} is not below n = {n}") o = Except.ok o' ∧ o'.size = n ∧
        ∀ j < n, o'[j]?.getD 0 = o[j]?.getD 0 +
          ((l.filter fun k => (is[k]?.getD 0).toNat = j).map (es[·]?.getD 0)).sum
  | [], o, hs, _ => ⟨o, rfl, hs, fun j _ => by simp⟩
  | k :: l, o, hs, hix => by
    have hk := hix k (by simp)
    obtain ⟨o', ho', hs', hj⟩ := scatterAddFold is es n l (o.setIfInBounds (is[k]?.getD 0).toNat
      ((o[(is[k]?.getD 0).toNat]?.getD 0) + (es[k]?.getD 0))) (by simp [hs]) fun k' hk' => hix k' (by simp [hk'])
    refine ⟨o', by simp only [List.foldlM_cons, if_pos hk, Op.eval, bind, Except.bind]; exact ho', hs', fun j hjn => ?_⟩
    rw [hj j hjn]
    by_cases e : (is[k]?.getD 0).toNat = j
    · subst e
      simp only [Array.getElem?_setIfInBounds_self_of_lt (show (is[k]?.getD 0).toNat < o.size by omega),
        Option.getD_some, UInt64.add_assoc]
      simp
    · simp only [Array.getElem?_setIfInBounds_ne e]
      simp [e]

/-- **`scatterWords .add` sums**: where every index is below `n`, cell `j` is `fill` plus the sum of `es[k]` over the
rows `k` naming `j`. -/
theorem scatterWords_add (is es : Array UInt64) (n : Nat) (fill : UInt64)
    (hix : ∀ k < is.size, (is[k]?.getD 0).toNat < n) :
    ∃ ws, scatterWords .add is es n fill = .ok ws ∧ ws.size = n ∧ ∀ j < n, ws[j]?.getD 0 = fill +
      (((List.range is.size).filter fun k => (is[k]?.getD 0).toNat = j).map (es[·]?.getD 0)).sum := by
  obtain ⟨o', ho, hs, hj⟩ := scatterAddFold is es n (List.range is.size) (Array.replicate n fill) (by simp)
    fun k hk => hix k (List.mem_range.1 hk)
  exact ⟨o', ho, hs, fun j hjn => by rw [hj j hjn]; simp [hjn]⟩

namespace Tab
variable {A B C : Obj}

/-- **`R.conv` denotes `R°`** (`Rep.rep_conv`'s statement, pointwise). -/
theorem conv_holds {R : Tab A B} {S : Tab B A} (h : R.conv = .ok S) (b : B.El) (a : A.El) :
    S.Holds b a ↔ R.Holds a b := by
  rw [canon_holds h]; exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
private def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

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
