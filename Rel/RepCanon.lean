import Rel.Run.Canon
import Rel.Run.CRelRelDef
import Rel.KernelSpec.KSeen

/-! The laws of `Vals.nub`, `Tab.canon`, `Tab.ran` and `Tab.dom` (`Rel/Run/Canon.lean`), from the five kernels' laws:
`asc_perm` (the sorted columns are the input's through a permutation), `kseen_ok` with `firsts_spec` (the first row of
each group, and every row's group), `raw_kgather` (a gathered word is the source's word at the index) and the closure
law `wordsFoR_closed` (a kernel's answer reads back as the words it wrote). `Arr.get_eq_of_raw` carries a word law to
the elements, and `Vals.gather_row` to the rows. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **An element is the atom of its word**: in a column every kernel reads (`foR`, or `pos` at `i64`), element `i` is
`Carrier.of?` of the atom its raw word `a` reads as (`atomOfBits`), and at `u1` that word is below `2`. A `sym` column
has no word reading (`Enc.get` declines it), so `sym` is excluded. -/
theorem Arr.get_raw_atom {t : QAtomicType} {n : USize} (x : Arr t n) (hx : Kernel.Enc.Valid n x.enc)
    (hg : t ≠ .general) (hs : t ≠ .sym) (i : Fin n.toNat) : ∃ a, (Enc.raw .i64 n x.enc)[i.1]? = some a ∧ (t = .u1 → a < 2) ∧
      x.get i = (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default := by
  have hw := x.wf
  rw [Arr.get_ne x i hg]
  cases hc : x.enc with
  | foR md pk =>
    rw [hc] at hw
    refine ⟨Column.foRBits md pk (Column.blockStarts md) i, by simp only [raw_foR .i64 8 rfl
      (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map, Array.getElem?_range, i.2, if_true, Option.map_some,
      Nat.reduceMul, ofNat_toNat_mod64], fun hu => by
        subst hu; simp only [Enc.WF] at hw; exact UInt64.lt_iff_toNat_lt.2 (hw.2.1 trivial i i.2), ?_⟩
    cases t <;> first | exact absurd rfl hg | exact absurd rfl hs |
      simp only [Enc.get, if_pos i.2, QAtomicType.width, foRBits_starts, Option.bind_some]
  | pos =>
    rw [hc] at hw
    cases t <;> simp only [Enc.WF] at hw
    exact ⟨UInt64.ofNat i.1, by simp [Enc.raw, i.2], fun h => absurd h (by decide),
      by simp [Enc.get, i.2, Column.atomOfBits]⟩
  | _ => all_goals (rw [hc] at hx; simp only [Kernel.Enc.Valid] at hx)

/-- **Equal atoms of the words, equal elements**: two `Arr`s of one type in a column every kernel reads (`foR`, or `pos`
at `i64`) whose raw words `a` at `i` and `b` at `j` read as one atom (`atomOfBits`, given the `u1` bound every `Arr`
keeps) hold one element there. What lifts a kernel's word law to `Arr.get`, at every type, equal words being the
special case and `Arr.get_raw_foR` the `i64` reading. -/
theorem Arr.get_eq_of_raw {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m) (hx : Kernel.Enc.Valid n x.enc)
    (hy : Kernel.Enc.Valid m y.enc) (i : Fin n.toNat) (j : Fin m.toNat)
    (h : ∀ (hg : t ≠ .general) a b, (Enc.raw .i64 n x.enc)[i.1]? = some a → (Enc.raw .i64 m y.enc)[j.1]? = some b →
      (t = .u1 → a < 2 ∧ b < 2) → Column.atomOfBits t a hg = Column.atomOfBits t b hg) : x.get i = y.get j := by
  have hg : t ≠ .general := by
    rintro rfl; have hw := x.wf
    cases hc : x.enc <;> (rw [hc] at hw hx; simp only [Enc.WF, Kernel.Enc.Valid] at hw hx) <;> exact absurd hw.1 (by decide)
  by_cases hs : t = .sym
  · -- `Enc.get` declines a `sym` word column, so both elements are the default
    subst hs
    have dflt : ∀ {n} (z : Arr .sym n), Kernel.Enc.Valid n z.enc → ∀ k : Fin n.toNat, z.get k = default := by
      intro n z hz k; rw [Arr.get_ne z k hg]
      cases hc : z.enc <;> rw [hc] at hz <;> simp_all [Enc.get, QAtomicType.width, Kernel.Enc.Valid]
    rw [dflt x hx i, dflt y hy j]
  obtain ⟨a, ha, hua, ex⟩ := Arr.get_raw_atom x hx hg hs i
  obtain ⟨b, hb, hub, ey⟩ := Arr.get_raw_atom y hy hg hs j
  rw [ex, ey, h hg a b ha hb fun hu => ⟨hua hu, hub hu⟩]

section
open Ext.Enc

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
/-- **`colMap op n a b t` at any answer type `t`**: word `i` is `op` of `a`'s and `b`'s words `i`, a boolean answer's
cut to its bit (`colMap_raw` is the `i64` case with the argument sizes). -/
theorem colMap_get {op : Op} {t : QAtomicType} {n : USize} {a b o : Enc} (h : colMap op n a b t = .ok o) :
    (raw .i64 n o).size = n.toNat ∧ ∀ i < n.toNat, ∃ v,
      op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) = .ok v ∧
      (raw .i64 n o)[i]? = some (if t = .u1 then v % 2 else v) := by
  unfold colMap at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i one1 h1
  have hone : ∀ i < n.toNat, (raw .u1 n one1)[i]?.getD 0 ≠ 0 := fun i hi => by rw [colConst_u1 h1 i hi]; decide
  unfold kscan at h
  cases hg : rawAll .u1 n one1 with
  | error m => simp [hg, bind, Except.bind] at h
  | ok g =>
    obtain ⟨rfl, hgs⟩ := rawAll_ok hg
    cases hc : [a, b].mapM (rawAll .i64 n) with
    | error m => simp [hg, hc, bind, Except.bind] at h
    | ok cs =>
      obtain ⟨rfl, hsz⟩ := mapM_rawAll hc
      cases hf : (List.range n.toNat).foldlM (kscanRow op (raw .u1 n one1) (raw .i64 n a) [raw .i64 n b]) #[] with
      | error m => simp [hg, hc, hf, bind, Except.bind] at h
      | ok out =>
        obtain ⟨hos, hrow⟩ := foldlM_kscanRow _ _ _ _ _ _ hf
        cases ht : t.width with
        | none => simp [hg, hc, hf, ht, bind, Except.bind] at h
        | some w =>
          simp only [hg, hc, hf, ht, bind, Except.bind, List.map_cons, List.map_nil, pure, Except.pure,
            Bool.false_eq_true, if_false, Except.ok.injEq] at h
          change wordsFoR _ = o at h
          cases h
          have hW : (out.map fun v => if t = .u1 then v % 2 else v).size = n.toNat := by simp [hos]
          rw [(wordsFoR_closed _ hW.symm).2.1]
          refine ⟨hW, fun i hi => ?_⟩
          have hr := hrow i (by omega)
          rw [if_neg (fun hh => hone i hi hh.2)] at hr
          simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind] at hr
          cases he : op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) with
          | error s => rw [he] at hr; cases hr
          | ok v =>
            rw [he] at hr; simp only [pure, Except.pure, Except.ok.injEq] at hr
            refine ⟨v, rfl, ?_⟩
            rw [Array.getElem?_map, Array.getElem?_eq_getElem (by omega), ← hr]; rfl


/-- An `i64` element is its raw word read as an `Int64`, at every encoding `Enc.WF` admits. -/
theorem Arr.get_i64 {n : USize} (x : Arr .i64 n) (i : Fin n.toNat) :
    x.get i = ((Enc.raw .i64 n x.enc)[i.1]?.getD 0).toInt64 := by
  have hw := x.wf
  rw [Arr.get_ne x i (by decide)]
  cases hc : x.enc <;> rw [hc] at hw <;>
    simp_all [Enc.WF, Enc.get, Enc.raw, QAtomicType.width, Column.atomOfBits, Dep.Carrier.of?, foRBits_starts,
      ofNat_toNat_mod64]

/-- A word below `2^63` and below `m` clamps to itself. -/
theorem clampFin_word {w : UInt64} {m : Nat} (h : 0 < m) (hw : w.toNat < m) (hm : m ≤ 2 ^ 63) :
    clampFin w.toInt64 m h = ⟨w.toNat, hw⟩ := by
  have e : w.toInt64.toInt = (w.toNat : Int) := by
    rw [Int64.toInt, UInt64.toInt64, Int64.toBitVec]
    simp only [BitVec.toInt]
    have : w.toBitVec.toNat = w.toNat := rfl
    omega
  apply Fin.ext; simp only [clampFin, e]; omega

/-- A boolean element is `true` exactly where its word is `1`. -/
theorem Arr.get_u1 {n : USize} (x : Arr .u1 n) (hx : Kernel.Enc.Valid n x.enc) (i : Fin n.toNat) :
    ∃ a, (Enc.raw .i64 n x.enc)[i.1]? = some a ∧ a = (if x.get i then 1 else 0) := by
  obtain ⟨a, ha, hu, e⟩ := Arr.get_raw_atom x hx (by decide) (by decide) i
  refine ⟨a, ha, ?_⟩
  have h2 : a.toNat < 2 := UInt64.lt_iff_toNat_lt.1 (hu rfl)
  rw [e]
  rcases (by omega : a.toNat = 0 ∨ a.toNat = 1) with h | h
  · obtain rfl : a = 0 := UInt64.toNat_inj.mp (by simpa using h)
    rfl
  · obtain rfl : a = 1 := UInt64.toNat_inj.mp (by simpa using h)
    rfl

/-- **The column form of the bridge**: element `j` of `Arr.gather m ix x` is element `ix[j]` of `x`, the index being
below `n`. -/
theorem Arr.gather_row {t : QAtomicType} {m n : USize} {ix : Enc} (x : Arr t n) {y : Arr t m}
    (h : Arr.gather m ix x = .ok y) (j : Fin m.toNat) : ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ y.get j = x.get i := by
  simp only [Arr.gather] at h
  split at h
  · rename_i o ho
    cases h
    have hv := kgather_valid ho
    obtain ⟨his, hes, hlt, ho'⟩ := raw_kgather m ix n _ o ho
    have hc := wordsFoR_closed ((Enc.raw .i64 m ix).map fun i => (Enc.raw .i64 n x.enc)[i.toNat]?.getD 0)
      (n := m) (by rw [Array.size_map, his])
    have hj : j.1 < (Enc.raw .i64 m ix).size := by rw [his]; exact j.2
    have hi := hlt j j.2
    refine ⟨⟨_, hi⟩, rfl, (Arr.get_eq_of_raw (t := t) x _ hv (by show Kernel.Enc.Valid m o; rw [ho']; exact hc.1)
      _ j fun _ a b ha hb _ => ?_).symm⟩
    suffices hr : (Enc.raw .i64 n x.enc)[(⟨_, hi⟩ : Fin n.toNat).1]? = (Enc.raw .i64 m o)[j.1]? by
      obtain rfl := Option.some.inj (ha.symm.trans (hr.trans hb)); rfl
    dsimp only
    rw [ho', hc.2.1, Array.getElem?_map]
    cases hw : (Enc.raw .i64 m ix)[j.1]? with
    | none => simp [Array.getElem?_eq_getElem hj] at hw
    | some w =>
      rw [hw] at hi
      simp only [Option.getD_some, Option.map_some] at hi ⊢
      simp only [Array.getElem?_eq_getElem (show w.toNat < _ by rw [hes]; exact hi), Option.getD_some]
  · cases h

end


/-- **The row form of the bridge**: row `j` of `Vals.gather m ix x` is row `ix[j]` of `x`, the index being below `n`. -/
theorem Vals.gather_row {m : USize} {ix : Enc} : {A : Obj} → {n : USize} → (x : Vals A n) → {y : Vals A m} →
    Vals.gather m ix x = .ok y → ∀ j : Fin m.toNat, ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ Vals.row y j = Vals.row x i
  | .atom _, _, x, _, h, j => Arr.gather_row x h j
  | .prod a b, n, x, y, h, j => by
    simp only [Vals.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    obtain ⟨i1, e1, r1⟩ := Vals.gather_row x.1 h1 j
    obtain ⟨i2, e2, r2⟩ := Vals.gather_row x.2 h2 j
    obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
    exact ⟨i1, e1, by simp only [Vals.row, r1, r2]⟩
  | .arr _, _, _, _, h, _ => by simp [Vals.gather] at h
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩, _, h, j => by
    simp only [Vals.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i tag' h1
    split at h; · cases h
    rename_i idx' h2
    cases h
    obtain ⟨i1, e1, r1⟩ := Arr.gather_row tag h1 j
    obtain ⟨i2, e2, r2⟩ := Arr.gather_row idx h2 j
    obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
    exact ⟨i1, e1, by simp only [Vals.row, r1, r2]⟩

/-- **A summand gathered at a sum side's positions**: where word `i` of `p` is `idx`'s, `y` (of `m ≤ 2^63` rows)
gathered at `p` holds at row `i` the row of `y` that `Vals.row` reads at `idx`'s clamped position. -/
theorem Vals.gather_clamp {B : Obj} {n m : USize} {p : Enc} (idx : Arr .i64 n) (y : Vals B m) {gy : Vals B n}
    (hg : Vals.gather n p y = .ok gy) (hm : m.toNat ≤ 2 ^ 63) (h0 : 0 < m.toNat) (i : Fin n.toNat)
    (hp : (Enc.raw .i64 n p)[i.1]?.getD 0 = (Enc.raw .i64 n idx.enc)[i.1]?.getD 0) :
    Vals.row y (clampFin (idx.get i) m.toNat h0) = Vals.row gy i := by
  obtain ⟨k, e, r⟩ := Vals.gather_row y hg i
  rw [r, Arr.get_i64, ← hp, clampFin_word h0 (by rw [e]; exact k.2) hm]
  exact congrArg _ (Fin.ext e)

/-- What `Vals.nub` answers, unfolded: each kernel's answer named, in the order of the composition. -/
theorem Vals.nub_ok {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∃ es vs p k g f ix y, Vals.cols x = .ok es ∧ kasc n es = .ok (vs, p) ∧
      kseen n ((es.map (·.1)).zip vs) = .ok (k, g, f) ∧ kgather k.toUSize f n p = .ok ix ∧
      Vals.gather k.toUSize ix x = .ok y ∧ r = ⟨k.toUSize, y⟩ := by
  simp only [Vals.nub, bind, Except.bind] at h
  repeat (split at h; · cases h)
  rename_i _ es hes _ vp hvp _ kgf hkgf _ ix hix
  cases hg : Vals.gather kgf.1.toUSize ix x with
  | error s => simp [hg, Functor.map, Except.map] at h
  | ok y =>
    simp only [hg, Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨es, vp.1, vp.2, kgf.1, kgf.2.1, kgf.2.2, ix, y, hes, hvp, hkgf, hix, hg, h.symm⟩

/-- **Every row of `Vals.nub x` is a row of `x`.** -/
theorem Vals.nub_sub {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∀ j : Fin r.1.toNat, ∃ i : Fin n.toNat, Vals.row r.2 j = Vals.row x i := by
  obtain ⟨_, _, _, _, _, _, _, y, _, _, _, _, hy, rfl⟩ := Vals.nub_ok h
  exact fun j => (Vals.gather_row x hy j).imp fun _ h => h.2

/-- **Every row of `x` has a row of `Vals.nub x` equal to it in the kernels' order codes** (`seenKey` over the side's
columns `es`): the first input row of its run among the sorted rows. Where equal codes mean equal rows, the two sides
hold the same rows (`Vals.nub_rows`). -/
theorem Vals.nub_cover {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (QAtomicType × Enc)} (hes : Vals.cols x = .ok es) (i : Fin n.toNat) :
    ∃ j : Fin r.1.toNat, ∃ i' : Fin n.toNat, Vals.row r.2 j = Vals.row x i' ∧ seenKey n es i' = seenKey n es i := by
  obtain ⟨es', vs, p, k, g, f, ix, y, hes', ha, hs, hix, hy, rfl⟩ := Vals.nub_ok h
  have hee : es = es' := Except.ok.inj (hes.symm.trans hes'); subst hee
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm n es vs p ha
  obtain ⟨hk, -, hf⟩ := kseen_ok hs
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  -- the sorted rows' key at `q` is the input's at `ps[q]`
  have hkey : ∀ q (hq : q < ps.length), seenKey n ((es.map (·.1)).zip vs) q = seenKey n es ps[q] := by
    intro q hq
    simp only [seenKey, ascKeys, List.map_map]
    apply List.ext_getElem (by simp [hvl])
    intro c h1 h2
    have hc2 : c < es.length := by simpa using h2
    obtain ⟨ws, hv, hws, hwq⟩ := hcol c es[c] (vs[c]'(by omega)) (List.getElem?_eq_getElem hc2)
      (List.getElem?_eq_getElem _)
    simp only [List.getElem_map, List.getElem_zip, Function.comp_apply, hv, (wordsFoR_closed ws hws.symm).2.1,
      Array.getElem?_map, hwq q hq]
  generalize seenKey n ((es.map (·.1)).zip vs) = K at hk hf hkey
  obtain ⟨q, hq, hqi⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 i.2))
  obtain ⟨hgl, -, hgk, -⟩ := (firsts_spec K n.toNat).2.2.2.2.2 q (by omega)
  have hq' : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < n.toNat := firsts_lt K n.toNat (List.getElem_mem hgl)
  have hkn : k ≤ n.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  obtain ⟨i', e1, r1⟩ := Vals.gather_row x hy ⟨Verify.groupOf K n.toNat q, by rw [hkU, hk]; exact hgl⟩
  refine ⟨_, i', r1, ?_⟩
  -- `ix[G]` is `ps[firsts[G]]`
  obtain ⟨his, hps, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 k.toUSize f = ((firstsOf K n.toNat).map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hkU, hk]; simp)).2.1
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hri : Enc.raw .i64 k.toUSize ix = (((firstsOf K n.toNat).map Nat.toUInt64).toArray.map fun w =>
      ((ps.map Nat.toUInt64).toArray)[w.toNat]?.getD 0) := by
    rw [hix', (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, hrf, hrp]
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hfG : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < ps.length := by omega
  have hi' : i'.1 = ps[(firstsOf K n.toNat)[Verify.groupOf K n.toNat q]] := by
    rw [← e1, hri]
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hgl,
      Option.map_some, Option.getD_some, hc64 _ hq', List.getElem?_eq_getElem hfG]
    exact hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hfG)))
  rw [hi', ← hkey _ hfG, hgk, hkey q hq, hqi]

/-- A column `kasc` reads is one every kernel reads: `ascCol` answers only on `foRWords`' columns. -/
theorem Verify.ascCol_valid {m : USize} {c : QAtomicType × Enc} {xk : Array UInt64 × Array UInt64}
    (h : ascCol m c = .ok xk) : Kernel.Enc.Valid m c.2 := by
  unfold ascCol at h
  split at h; · cases h
  cases hw : ascWords m c with
  | error s => simp [hw, Functor.map, Except.map] at h
  | ok x => exact (foRWords_valid _ _ _).2 _ (ascWords_foR hw)

/-- **Equal order codes of one column, equal elements**: where `kasc` reads `x` (`ascCol` answers), `x` is a column
every kernel reads, and rows with equal codes (`seenKey`) hold one atom (`ascOrd_atom`), so one element. -/
theorem Arr.eq_of_codes {t : QAtomicType} {n : USize} (x : Arr t n) {cs}
    (hc : [(t, x.enc)].mapM (ascCol n) = .ok cs) : Kernel.Enc.Valid n x.enc ∧ ∀ i i' : Fin n.toNat,
      seenKey n [(t, x.enc)] i = seenKey n [(t, x.enc)] i' → x.get i = x.get i' := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨-, -, f, hof, -⟩ := ascCol_ok hac
  have hv := ascCol_valid hac
  refine ⟨hv, fun i i' hk => ?_⟩
  simp only [seenKey, ascKeys, List.map_cons, List.map_nil, hof, Option.getD_some, List.cons.injEq, and_true,
    Array.getElem?_map] at hk
  exact Arr.get_eq_of_raw x x hv hv i i' fun hg a b ha hb hu =>
    (ascOrd_atom hof hg hu).1 (by simpa only [ha, hb, Option.map_some, Option.getD_some] using hk)

/-- **Equal order codes, equal rows**, over any side whose columns `kasc` reads (`ascCol` answers on each): the codes
of row `i` and row `i'` agree in every column (`seenKey`), so their atoms do (`ascOrd_atom`), so their elements do
(`Arr.get_eq_of_raw`). -/
theorem Vals.row_of_codes : {A : Obj} → {n : USize} → (x : Vals A n) → {es : List (QAtomicType × Enc)} →
    Vals.cols x = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs → ∀ i i' : Fin n.toNat,
      seenKey n es i = seenKey n es i' → x.row i = x.row i'
  | .atom t, n, x, es, hes, cs, hc, i, i', hk => by
    simp only [Vals.cols, Except.ok.injEq] at hes; subst hes
    exact (Arr.eq_of_codes x hc).2 i i' hk
  | .prod _ _, n, x, es, hes, cs, hc, i, i', hk => by
    simp only [Vals.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys]
    rw [hs, hs] at hk
    obtain ⟨k1, k2⟩ := List.append_inj hk (by simp [seenKey, ascKeys])
    show (Vals.row x.1 i, Vals.row x.2 i) = (Vals.row x.1 i', Vals.row x.2 i')
    rw [Vals.row_of_codes x.1 h1 hc1 i i' k1, Vals.row_of_codes x.2 h2 hc2 i i' k2]
  | .arr _, _, _, _, hes, _, _, _, _, _ => by simp [Vals.cols] at hes
  | .sum _ _, _, _, _, hes, _, _, _, _, _ => by simp [Vals.cols] at hes

/-- **Rows of `x` with equal order codes are equal** where `Vals.nub x` answers: `kasc` read every column. -/
theorem Vals.row_of_seenKey {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m}
    (h : Vals.nub x = .ok r) {es} (hes : Vals.cols x = .ok es) (i i' : Fin n.toNat)
    (hk : seenKey n es i = seenKey n es i') : x.row i = x.row i' := by
  obtain ⟨es', _, _, _, _, _, _, _, hes', ha, -⟩ := Vals.nub_ok h
  obtain rfl : es = es' := Except.ok.inj (hes.symm.trans hes')
  obtain ⟨cs, hc, -⟩ := kasc_ok ha
  exact Vals.row_of_codes x hes hc i i' hk

/-- **`Vals.nub x` holds exactly `x`'s rows**: `Vals.nub_sub` one way, `Vals.nub_cover` with `Vals.row_of_seenKey`
the other. -/
theorem Vals.nub_rows {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    (a : A.El) : (∃ j, Vals.row r.2 j = a) ↔ ∃ i, Vals.row x i = a := by
  obtain ⟨es, _, _, _, _, _, _, _, hes, _⟩ := Vals.nub_ok h
  constructor
  · rintro ⟨j, rfl⟩; obtain ⟨i, hi⟩ := Vals.nub_sub h j; exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩; obtain ⟨j, i', h1, h2⟩ := Vals.nub_cover h hes i
    exact ⟨j, h1.trans (Vals.row_of_seenKey h hes i' i h2)⟩

/-- **Which input row each row of `Vals.nub x` is**: `kasc`'s permutation `ps` (its grade by the codes `ascKeys`),
`K` the sorted rows' keys (`K q` the key of input row `ps[q]`), and row `j` of the answer input row `ps[F[j]]`, `F` the
first rows of `K` (`firstsOf`, `k` of them). -/
theorem Vals.nub_sel {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (QAtomicType × Enc)} (hes : Vals.cols x = .ok es) :
    ∃ (ps : List Nat) (K : Nat → List UInt64), ps = ascGrade n.toNat (ascKeys n es) ∧
      (∀ q (hq : q < ps.length), K q = seenKey n es ps[q]) ∧ r.1.toNat = (firstsOf K n.toNat).length ∧
      ∀ j : Fin r.1.toNat, ∃ i : Fin n.toNat, Vals.row r.2 j = Vals.row x i ∧
        ((firstsOf K n.toNat)[j.1]?.bind (ps[·]?)) = some i.1 := by
  obtain ⟨es', vs, p, k, g, f, ix, y, hes', ha, hs, hix, hy, rfl⟩ := Vals.nub_ok h
  have hee : es = es' := Except.ok.inj (hes.symm.trans hes'); subst hee
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm n es vs p ha
  obtain ⟨cs, hc, -, -, -, -, -, hpk⟩ := kasc_ok ha
  rw [ascCol_keys hc] at hpk
  obtain ⟨hk, -, hf⟩ := kseen_ok hs
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hperm' := (ascGrade_spec n.toNat (ascKeys n es)).1
  have hlen' : (ascGrade n.toNat (ascKeys n es)).length = n.toNat := by simpa using hperm'.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  -- `asc_perm`'s permutation is the grade: both are what `p` reads back as
  have hpsg : ps = ascGrade n.toNat (ascKeys n es) := by
    have e : ((ascGrade n.toNat (ascKeys n es)).map Nat.toUInt64).toArray = (ps.map Nat.toUInt64).toArray := by
      rw [← hrp, hpk]; exact ((wordsFoR_closed _ (by simp [hlen'])).2.1).symm
    refine List.ext_getElem (by rw [hlen, hlen']) fun q h1 h2 => ?_
    have e2 := congrArg (fun a : Array UInt64 => a[q]?) e
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at e2
    rw [← hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem h1))),
      ← hc64 _ (List.mem_range.1 (hperm'.mem_iff.1 (List.getElem_mem h2))), e2]
  -- the sorted rows' key at `q` is the input's at `ps[q]`
  have hkey : ∀ q (hq : q < ps.length), seenKey n ((es.map (·.1)).zip vs) q = seenKey n es ps[q] := by
    intro q hq
    simp only [seenKey, ascKeys, List.map_map]
    apply List.ext_getElem (by simp [hvl])
    intro c h1 h2
    have hc2 : c < es.length := by simpa using h2
    obtain ⟨ws, hv, hws, hwq⟩ := hcol c es[c] (vs[c]'(by omega)) (List.getElem?_eq_getElem hc2)
      (List.getElem?_eq_getElem _)
    simp only [List.getElem_map, List.getElem_zip, Function.comp_apply, hv, (wordsFoR_closed ws hws.symm).2.1,
      Array.getElem?_map, hwq q hq]
  generalize seenKey n ((es.map (·.1)).zip vs) = K at hk hf hkey
  have hkn : k ≤ n.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  refine ⟨ps, K, hpsg, hkey, by rw [hkU, hk], fun j => ?_⟩
  have hgl : j.1 < (firstsOf K n.toNat).length := by have h2 : j.1 < k.toUSize.toNat := j.2; omega
  obtain ⟨i', e1, r1⟩ := Vals.gather_row x hy j
  refine ⟨i', r1, ?_⟩
  -- `ix[j]` is `ps[firsts[j]]`
  obtain ⟨his, hps, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 k.toUSize f = ((firstsOf K n.toNat).map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hkU, hk]; simp)).2.1
  have hri : Enc.raw .i64 k.toUSize ix = (((firstsOf K n.toNat).map Nat.toUInt64).toArray.map fun w =>
      ((ps.map Nat.toUInt64).toArray)[w.toNat]?.getD 0) := by
    rw [hix', (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, hrf, hrp]
  have hq' : (firstsOf K n.toNat)[j.1] < n.toNat := firsts_lt K n.toNat (List.getElem_mem hgl)
  have hfG : (firstsOf K n.toNat)[j.1] < ps.length := by omega
  rw [List.getElem?_eq_getElem hgl, Option.bind_some, List.getElem?_eq_getElem hfG, ← e1, hri]
  simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hgl,
    Option.map_some, Option.getD_some, hc64 _ hq', List.getElem?_eq_getElem hfG]
  exact congrArg some (hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hfG)))).symm

/-- **`Vals.nub x` is sorted and has no two rows with one key**: its rows are input rows `sel j`, ascending in `kasc`'s
order of their codes (`lexLe` over `ascKeys`), no two with equal codes (`seenKey`). -/
theorem Vals.nub_sorted {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (QAtomicType × Enc)} (hes : Vals.cols x = .ok es) :
    ∃ sel : Fin r.1.toNat → Fin n.toNat, (∀ j, Vals.row r.2 j = Vals.row x (sel j)) ∧
      ∀ j j' : Fin r.1.toNat, j.1 < j'.1 → lexLe (ascKeys n es) (sel j) (sel j') = true ∧
        seenKey n es (sel j) ≠ seenKey n es (sel j') := by
  obtain ⟨ps, K, hps, hkey, hr, hsel⟩ := Vals.nub_sel h hes
  obtain ⟨sel, hs⟩ := Classical.axiomOfChoice hsel
  refine ⟨sel, fun j => (hs j).1, fun j j' hjj => ?_⟩
  obtain ⟨hperm, hsort⟩ := ascGrade_spec n.toNat (ascKeys n es); rw [← hps] at hperm hsort
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have fs := firsts_spec K n.toNat
  have hj : j.1 < (firstsOf K n.toNat).length := hr ▸ j.2
  have hj' : j'.1 < (firstsOf K n.toNat).length := hr ▸ j'.2
  have hf : (firstsOf K n.toNat)[j.1] < ps.length := by have := firsts_lt K n.toNat (List.getElem_mem hj); omega
  have hf' : (firstsOf K n.toNat)[j'.1] < ps.length := by have := firsts_lt K n.toNat (List.getElem_mem hj'); omega
  have e := (hs j).2; have e' := (hs j').2
  simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.bind_some, List.getElem?_eq_getElem hf,
    List.getElem?_eq_getElem hf', Option.some.injEq] at e e'
  have hlt : (firstsOf K n.toNat)[j.1] < (firstsOf K n.toNat)[j'.1] := List.pairwise_iff_getElem.1 fs.1 _ _ hj hj' hjj
  refine ⟨?_, fun hk => ?_⟩
  · have l := (List.pairwise_iff_getElem.1 hsort _ _ hf hf' hlt).1; rw [e, e'] at l; exact l
  · replace hk : K (firstsOf K n.toNat)[j.1] = K (firstsOf K n.toNat)[j'.1] := by
      rw [hkey _ hf, hkey _ hf', e, e']; exact hk
    have g := (fs.2.2.1 _ (by omega) _ (by omega)).2 hk
    rw [fs.2.2.2.1 _ hj, fs.2.2.2.1 _ hj'] at g; omega

namespace Tab
variable {k v : Obj}

/-- **`R.canon` denotes `R`**. -/
theorem canon_holds {R S : Tab k v} (h : R.canon = .ok S) (a : k.El) (b : v.El) : S.Holds a b ↔ R.Holds a b := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn (a, b)
    simp only [Tab.Holds, Vals.row, Prod.mk.injEq] at this ⊢
    exact this

/-- **`R.ran` denotes `𝟙 ∩ R° ≫ R°°`** (`CRel.rep_ran`'s statement, pointwise). -/
theorem ran_holds {R : Tab k v} {S : Tab v v} (h : R.ran = .ok S) (a b : v.El) : S.Holds a b ↔ a = b ∧ ∃ x, R.Holds x a := by
  unfold Tab.ran at h
  cases hn : Vals.nub R.val with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, Vals.row R.key i, i, rfl, hi⟩
    · rintro ⟨rfl, x, i, -, hi⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

/-- **`R.dom` denotes `𝟙 ∩ R ≫ R°`** (`CRel.rep_dom`'s statement, pointwise). -/
theorem dom_holds {R : Tab k v} {S : Tab k k} (h : R.dom = .ok S) (a b : k.El) : S.Holds a b ↔ a = b ∧ ∃ y, R.Holds a y := by
  unfold Tab.dom at h
  cases hn : Vals.nub R.key with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, Vals.row R.val i, i, hi, rfl⟩
    · rintro ⟨rfl, y, i, hi, -⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)]).canon.toOption.map Tab.toList) ==
  some [(-1, 2), (1, 2), (2, 7), (3, 1)]
#guard ((tab [(3, 1), (1, 2), (3, 5), (0, -4)]).ran.toOption.map Tab.toList) == some [(-4, -4), (1, 1), (2, 2), (5, 5)]
#guard ((tab [(3, 1), (1, 2), (3, 5)]).dom.toOption.map Tab.toList) == some [(1, 1), (3, 3)]
#guard ((tab []).canon.toOption.map Tab.toList) == some []
-- `Alg.ofPairs`' columns are `canonC`'s rows, read through `Alg.pick` → `gatherColumn`, an old kernel that still writes
-- `.bytes` (`Rel/Run/Code.lean`, `pick`): the error, never a conversion, until that exit is `foR`
#guard (Alg.ofPairs [(1, 2)]).canon matches .error _
-- the five-kernel `canon`, `ran`, `dom` against the old `canonC`, `CRel.ran`, `CRel.dom` on the same tables
#guard [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], []].all
  fun (ps : List (Int64 × Int64)) =>
    let c := Alg.canonC (tab ps)
    ((tab ps).canon.toOption.map Tab.toList) == (if c.2 then some c.1.toList else none) &&
    ((tab ps).ran.toOption.map Tab.toList) == ((CRel.ran (some (tab ps))).map Tab.toList) &&
    ((tab ps).dom.toOption.map Tab.toList) == ((CRel.dom (some (tab ps))).map Tab.toList)

end Checks

#print axioms Tab.canon_holds
#print axioms Tab.ran_holds

end Rel
