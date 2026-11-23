module

public import Rel.Run.Cols
public import Rel.RepCanon
public import Rel.KernelSpec.Closure

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of the column helpers of `Rel/Run/Cols.lean` (`colConst`, `colMap`, `colPrefix`, `shiftCol`, CONCAT), on
the words `Enc.raw` reads, from the five kernels' laws. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

/-- `kscan` at `i64` writes its words as they are: the cut to `8 * 8` bits is the identity. -/
private theorem mod_i64 (v : UInt64) : UInt64.ofNat (v.toNat % 2 ^ (if QAtomicType.i64 = .u1 then 1 else 8 * 8)) = v := by
  simp only [if_neg (by decide : QAtomicType.i64 ≠ .u1)]; exact ofNat_toNat_mod64 v

/-- **`colPrefix op n a` is the running fold of `op` from `0`**: row `i` is `op` of row `i - 1` (`0` at row `0`) and
`a[i]`. -/
theorem colPrefix_raw {op : Op} {n : USize} {a e : Enc} (h : colPrefix op n a = .ok e) (ho : op ≠ .first := by decide) :
    (raw .i64 n a).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧ ∀ i < n.toNat,
      op.eval (if i = 0 then 0 else (raw .i64 n e)[i - 1]?.getD 0) ((raw .i64 n a)[i]?.getD 0) =
        .ok ((raw .i64 n e)[i]?.getD 0) := by
  unfold colPrefix at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz
  split at h; · cases h
  rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  obtain ⟨-, hxs, c, cs, hc, out, hout, he, -, hrow⟩ :=
    raw_kscan op false .i64 .i64 8 rfl n z [(n, z), (n, a)] r (kscanStream_ne ho _ _ _) hr
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte, mod_i64, Array.map_id'] at he hrow
  have hz0 := colConst_raw hz
  have hzs := colConst_u1 hz
  refine ⟨(hxs (n, a) (by simp)).2, by rw [he, hout], fun i hi => ?_⟩
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
theorem colMap_raw {op : Op} {n : USize} {a b e : Enc} {s : QAtomicType}
    (h : colMap op n a b .i64 s = .ok e) (hk : kscanStream op [(n, a), (n, b)] [] [] = false := by lockstep) :
    (raw s n a).size = n.toNat ∧ (raw s n b).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧
      ∀ i < n.toNat, op.eval ((raw s n a)[i]?.getD 0) ((raw s n b)[i]?.getD 0) = .ok ((raw .i64 n e)[i]?.getD 0) := by
  obtain ⟨ha, hb, hs, hr⟩ := colMap_chain h hk
  refine ⟨ha, hb, hs, fun i hi => ?_⟩
  obtain ⟨x, y, v, w, hx, hy, hv, hw, ho⟩ := hr i hi
  cases hx; cases hy; cases hw
  simp only [ho, Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1)]; exact hv

/-- **A map of one column through a post chain** at any answer type `t`: word `i` of the answer is `chain post` of
word `i` of `a`, a boolean answer's cut to its bit (`colMap_chain` at `.first` and no `pre`). -/
theorem colMap_first_chain {t s : QAtomicType} {n : USize} {a o : Enc} {post : List (Op × UInt64)}
    (h : colMap .first n a a t s [] post = .ok o) (i : Nat) (hi : i < n.toNat)
    (hs : kscanStream .first [(n, a), (n, a)] [] post = false := by lockstep) : ∃ w,
      chain post ((raw s n a)[i]?.getD 0) = .ok w ∧ (raw .i64 n o)[i]? = some (if t = .u1 then w % 2 else w) := by
  obtain ⟨x, y, v, w, hx, -, hv, hw, ho⟩ := (colMap_chain h hs).2.2.2 i hi
  cases hx; cases hv
  exact ⟨w, hw, ho⟩

/-- **`colMap .first n a a` with the post chain `[(op, c)]` is `op` of the constant `c` and each word of `a`**: a map
with a constant operand is one `kscan` (`colMap_const_eq`); `colMap_first_chain` at `i64` and a one-step chain. -/
theorem colMap_post {op : Op} {n : USize} {a e : Enc} {c : UInt64}
    (h : colMap .first n a a .i64 .i64 [] [(op, c)] = .ok e) : (raw .i64 n e).size = n.toNat ∧
      ∀ i < n.toNat, op.eval c ((raw .i64 n a)[i]?.getD 0) = .ok ((raw .i64 n e)[i]?.getD 0) := by
  have hs : kscanStream .first [(n, a), (n, a)] [] [(op, c)] = false := by simp [kscanStream]
  refine ⟨(colMap_chain h hs).2.2.1, fun i hi => ?_⟩
  obtain ⟨w, hw, ho⟩ := colMap_first_chain h i hi hs
  simp only [ho, Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1)]
  simpa [chain] using hw

/-- `x - b` as a post step:`(.add, 0 - b)`, since `kscan` has no step subtracting its constant from the word. -/
theorem neg_add_word (a b : UInt64) : 0 - b + a = a - b := by
  rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.zero_add, UInt64.add_comm]

/-- **A constant operand is a post step** (perf11): `colMap op' n a (colConst n c)` and the one `kscan`
`colMap .first n a a` with the post chain `[(op, c)]` write the same words wherever `op' x c = op c x`, so the
`kscatter` that builds the constant column is not run. -/
theorem colMap_const_eq {op op' : Op} {n : USize} {a k e e' : Enc} {c : UInt64}
    (hop : ∀ x, op'.eval x c = op.eval c x) (hk : colConst n c = .ok k)
    (h : colMap op' n a k = .ok e) (h' : colMap .first n a a .i64 .i64 [] [(op, c)] = .ok e')
    (hl : kscanStream op' [(n, a), (n, k)] [] [] = false := by lockstep) : raw .i64 n e = raw .i64 n e' := by
  obtain ⟨-, -, hs, hr⟩ := colMap_raw h hl
  obtain ⟨hs', hr'⟩ := colMap_post h'
  refine Array.ext (hs.trans hs'.symm) fun i hi hi' => ?_
  have h1 := hr i (hs ▸ hi)
  simp only [colConst_raw hk, Array.getElem?_replicate, if_pos (hs ▸ hi), Option.getD_some, hop,
    hr' i (hs ▸ hi), Except.ok.injEq, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] at h1
  exact h1.symm

/-- **An ordered element is its word read at its type**: element `i` of a column of an ordered atom `t` (`ordNum`: the
number atoms, `char`, `date`, `datetime`) is `ofBits t` of word `i` of `Enc.raw t`, at every encoding `Enc.WF` admits
(`Arr.get_i64` reads `i64`'s). -/
theorem Arr.get_word {t : QAtomicType} {n : USize} (x : Arr t n) (ht : t.ordNum.isSome) (i : Fin n.toNat) :
    x.get i = QAtomicType.ofBits t ((raw t n x.enc)[i.1]?.getD 0) := by
  have hw := x.wf
  obtain ⟨w, hwd⟩ : ∃ w, t.width = some w := by cases t <;> first | exact absurd ht (by decide) | exact ⟨_, rfl⟩
  have hg := QAtomicType.ne_general_of_width hwd
  have hu : t ≠ .u1 := by rintro rfl; exact absurd ht (by decide)
  have ofA : ∀ a, (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default = QAtomicType.ofBits t a := by
    intro a; cases t <;> first | rfl | exact absurd ht (by decide)
  rw [Arr.get_ne x i hg, ← ofA]
  suffices e : Enc.get t n x.enc i.1 = some (Column.atomOfBits t ((raw t n x.enc)[i.1]?.getD 0) hg) by rw [e]; rfl
  cases t <;> first | exact absurd ht (by decide) | skip
  all_goals
    cases hc : x.enc <;> rw [hc] at hw <;> simp only [Enc.WF, QAtomicType.width] at hw <;>
      simp only [Enc.get, raw, QAtomicType.width, Array.getElem?_map, Array.getElem?_range, i.2,
        if_true, Option.map_some, Option.getD_some, foRBits_starts, Option.some.injEq] <;>
      first | rfl | exact (atomOfBits_mod rfl (by decide) _).symm | simp_all

/-- **`shiftCol n s` is the words `k + s`**. -/
theorem shiftCol_raw {n : USize} {s : UInt64} {o : Enc} (h : shiftCol n s = .ok o) :
    ∀ k < n.toNat, (raw .i64 n o)[k]?.getD 0 = k.toUInt64 + s := by
  intro k hk
  have hr := (colMap_post h).2 k hk
  have hp : (raw .i64 n (.pos : Enc))[k]?.getD 0 = k.toUInt64 := by
    simp only [raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
  rw [hp] at hr
  simp only [Op.eval, Except.ok.injEq] at hr
  rw [← hr, UInt64.add_comm]

/-- The source column of a successful `kscatter` is one every kernel reads. -/
theorem kscatter_valid {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64} (h : kscatter op m ix e n fill = .ok o) :
    Kernel.Enc.Valid m e := by
  unfold kscatter at h
  split at h; · cases h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i ws hws
  exact (foRWords_valid _ _ _).2 _ hws

/-- Two words that read alike: equal, or a boolean's word cut to its bit where both are below `2`. -/
theorem atom_of_cut {t : QAtomicType} (hg : t ≠ .general) {p q : UInt64} (hp : p = if t = .u1 then q % 2 else q)
    (hu : t = .u1 → p < 2 ∧ q < 2) : Column.atomOfBits t p hg = Column.atomOfBits t q hg := by
  congr 1
  by_cases tu : t = .u1
  · rw [hp, if_pos tu]
    have : q.toNat < 2 := UInt64.lt_iff_toNat_lt.1 (hu tu).2
    exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod]; exact Nat.mod_eq_of_lt this)
  · rw [hp, if_neg tu]

/-- **A source's word read at `t` is its `i64` word cut to `t`'s width** (a boolean's to its bit), in every column every
kernel reads: `raw_foR` at `t` and at `i64`, or `pos`, an `i64` column, read at `i64` both times. -/
theorem raw_cut {t : QAtomicType} {w : Nat} (ht : t.width = some w) {m : USize} {e : Enc} (hw : Enc.WF t m e)
    (hV : Kernel.Enc.Valid m e) {k : Nat} (hk : k < m.toNat) :
    (raw t m e)[k]? = some (UInt64.ofNat (((raw .i64 m e)[k]?.getD 0).toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) := by
  cases e with
  | foR md pk =>
    have hr : (raw .i64 m (.foR md pk : Enc))[k]?.getD 0 = Column.foRBits md pk (Column.blockStarts md) k := by
      simp only [raw_foR .i64 8 rfl (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map, Array.getElem?_range, hk,
        if_true, Option.map_some, Option.getD_some, Nat.reduceMul, ofNat_toNat_mod64]
    rw [hr]
    by_cases hb : t = .u1
    · subst hb; simp [Enc.raw, hk]
    · rw [raw_foR t w ht hb]; simp [hb, hk]
  | pos =>
    cases t <;> simp only [Enc.WF] at hw
    obtain rfl : w = 8 := (Option.some.inj (ht : some 8 = some w)).symm
    simp only [Enc.raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some,
      Option.some.injEq]
    exact (mod_i64 _).symm
  | _ => all_goals simp only [Kernel.Enc.Valid] at hV

/-- **A stream's answer reads each source's rows, null included**, as `Opt.get_eq_of_raw` asks: row `S + k` of the answer
`z` (`streamEnc`), `S` the rows of the sources before source `j`, is row `k` of that source `src`. The flags are
`kscan_stream_get`'s (`foRNuls_wordsFoR`, `bitAt_stream`, `joined_get`), the words `raw_cut` and `atomOfBits_mod`
(`atom_of_cut` at a boolean). -/
theorem Opt.stream_get {t : QAtomicType} {n : USize} {es : List (USize × Enc)} (hwid : t.width.isSome)
    (hW : ∀ p ∈ es, Enc.WF t p.1 p.2) (hn : (es.map (·.1.toNat)).sum = n.toNat) {j k : Nat} (hj : j < es.length)
    (hk : k < es[j].1.toNat) (z : Opt t n) (hz : z.enc = streamEnc t t es) (hV : Kernel.Enc.Valid n z.enc)
    (src : Opt t es[j].1) (hs : src.enc = es[j].2) (hVs : Kernel.Enc.Valid es[j].1 src.enc) (i : Fin n.toNat)
    (hi : i.1 = ((es.take j).map (·.1.toNat)).sum + k) : z.get i = src.get ⟨k, hk⟩ := by
  obtain ⟨w, ht⟩ := Option.isSome_iff_exists.1 hwid
  obtain ⟨i, hlt⟩ := i
  dsimp only at hi; subst hi
  have hsz : n.toNat = ((streamRaw t es).map (cutBit t)).size := by
    rw [Array.size_map, streamRaw_size hwid hW, hn]
  have hnn : ((es.take j).map (·.1.toNat)).sum + k < (streamNul es).size := by rw [streamNul_size, hn]; exact hlt
  have e1 : (streamNul es)[((es.take j).map (·.1.toNat)).sum + k]? = (foRNuls es[j].1 es[j].2)[k]? := by
    rw [streamNul_eq]; exact joined_get (fun p => foRNuls p.1 p.2) (fun p _ => foRNuls_size _ _) hj hk
  have hf : (foRNuls n z.enc)[((es.take j).map (·.1.toNat)).sum + k]? = (foRNuls es[j].1 src.enc)[k]? := by
    rw [hz, hs]; unfold streamEnc
    rw [foRNuls_wordsFoR _ _ hsz _ (by rw [Array.size_map, streamRaw_size hwid hW, hn]; exact hlt), bitAt_stream hnn, e1]
    exact (foRNuls_bit _ _ hk).symm
  refine Opt.get_eq_of_raw z src hV hVs ⟨_, hlt⟩ ⟨k, hk⟩ hf fun h0 hg a b ha hb hu => ?_
  have h0' : (foRNuls es[j].1 es[j].2)[k]? = some 0 := by rw [← hs, ← hf]; exact h0
  obtain ⟨md, pk, hE⟩ : ∃ md pk, z.enc = .foR md pk := ⟨_, _, by rw [hz]; rfl⟩
  have hg' := kscan_stream_get (s := t) (t := t) hwid hW hn hj hk (md := md) (pk := pk) (hz.symm.trans hE)
  simp only [h0', Option.getD_some, bne_self_eq_false, Bool.false_eq_true, if_false] at hg'
  rw [hs] at hb
  have hb' := raw_cut ht (hW _ (List.getElem_mem hj)) (hs ▸ hVs) hk
  rw [hb, Option.getD_some] at hb'
  rw [hb', Option.getD_some] at hg'
  rw [hE, raw_foR .i64 8 rfl (by decide : QAtomicType.i64 ≠ .u1)] at ha
  simp only [Array.getElem?_map, Array.getElem?_range, hlt, if_true, Option.map_some, Nat.reduceMul,
    ofNat_toNat_mod64, Option.some.injEq] at ha
  unfold Column.foROpt at hg'
  split at hg'; · cases hg'
  have hae : a = cutBit t (UInt64.ofNat (b.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) := by
    rw [← ha]; exact Option.some.inj hg'
  by_cases tu : t = .u1
  · subst tu
    have hb3 : b.toNat < 2 := by simpa using UInt64.lt_iff_toNat_lt.1 (hu rfl).2
    have : a = b := by
      rw [hae]; simp only [cutBit, if_true]
      apply UInt64.toNat_inj.mp
      simp [UInt64.toNat_mod, UInt64.toNat_ofNat]; omega
    rw [this]
  · rw [hae]; simp only [cutBit, tu, if_false]; exact atomOfBits_mod ht tu b

/-- **What a successful `Opt.concat` is**: its answer is the stream `streamEnc` of the two sources, a column every kernel
reads, and the sources are `foROk` and sum to `n` rows at a type with a width. -/
theorem Opt.concat_enc {t : QAtomicType} {n₁ n₂ n : USize} {x : Opt t n₁} {y : Opt t n₂} {z : Opt t n}
    (h : Opt.concat n x y = .ok z) : z.enc = streamEnc t t [(n₁, x.enc), (n₂, y.enc)] ∧ Kernel.Enc.Valid n z.enc ∧
      n₁.toNat + n₂.toNat = n.toNat ∧ foROk n₁ x.enc = true ∧ foROk n₂ y.enc = true ∧ t.width.isSome := by
  unfold Opt.concat at h
  split at h
  · rename_i hn
    split at h
    · rename_i hv
      split at h
      · rename_i w hw
        split at h
        · rename_i r hr
          cases h
          obtain ⟨h1, h2, -⟩ := kscan_stream_closed (s := t) hw (by rw [hw]; rfl) (n := n)
            (es := [(n₁, x.enc), (n₂, y.enc)]) (by simp; exact ⟨x.wf, y.wf⟩) (by simp) (by simpa using hn)
          rw [hr] at h1
          have e : r.1 = streamEnc t t [(n₁, x.enc), (n₂, y.enc)] := congrArg Prod.fst (Except.ok.inj h1)
          exact ⟨e, by show Kernel.Enc.Valid n r.1; rw [e]; exact h2, hn, hv.1, hv.2, by rw [hw]; rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Element `c` of `Opt.concat`** is element `c` of `x` below `n₁`, element `c - n₁` of `y` from there, a null
included: the one `kscan` stream reads each source's rows back (`Opt.stream_get`). -/
theorem Opt.concat_get {t : QAtomicType} {n₁ n₂ n : USize} {x : Opt t n₁} {y : Opt t n₂} {z : Opt t n}
    (hn : n.toNat = n₁.toNat + n₂.toNat) (h : Opt.concat n x y = .ok z) (c : Fin n.toNat) :
    z.get c = if hc : c.1 < n₁.toNat then x.get ⟨c.1, hc⟩ else y.get ⟨c.1 - n₁.toNat, by omega⟩ := by
  obtain ⟨hz, hV, -, hx, hy, hwid⟩ := Opt.concat_enc h
  have hW : ∀ p ∈ [(n₁, x.enc), (n₂, y.enc)], Enc.WF t p.1 p.2 := by simp; exact ⟨x.wf, y.wf⟩
  have hs : (([(n₁, x.enc), (n₂, y.enc)] : List (USize × Enc)).map (·.1.toNat)).sum = n.toNat := by simp; omega
  split
  · rename_i hc
    exact Opt.stream_get hwid hW hs (j := 0) (k := c.1) (by simp) (by simpa using hc) z hz hV x rfl
      (foROk_valid hx) c (by simp)
  · rename_i hc
    exact Opt.stream_get hwid hW hs (j := 1) (k := c.1 - n₁.toNat) (by simp) (by simp; omega) z hz hV y rfl
      (foROk_valid hy) c (by simp; omega)

/-- **Element `c` of `Arr.concat`**: `Opt.concat_get` read through `Opt.ofArr` (`Opt.get_ofArr`). -/
theorem Arr.concat_get {t : QAtomicType} {n₁ n₂ n : USize} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (hn : n.toNat = n₁.toNat + n₂.toNat) (h : Arr.concat n x y = .ok z) (c : Fin n.toNat) :
    z.get c = if hc : c.1 < n₁.toNat then x.get ⟨c.1, hc⟩ else y.get ⟨c.1 - n₁.toNat, by omega⟩ := by
  unfold Arr.concat at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i zo hzo
  split at h
  · rename_i hz
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have e0 : zo.get c = some ((Arr.mk zo.enc zo.wf hz).get c) := Opt.get_ofArr (Arr.mk zo.enc zo.wf hz) c
    rw [Opt.concat_get hn hzo c] at e0
    by_cases hc : c.1 < n₁.toNat
    · rw [dif_pos hc, Opt.get_ofArr] at e0
      rw [dif_pos hc]; exact (Option.some.inj e0).symm
    · rw [dif_neg hc, Opt.get_ofArr] at e0
      rw [dif_neg hc]; exact (Option.some.inj e0).symm
  · cases h

/-- What `catRows` answers: the summed count. -/
theorem catRows_ok {n₁ n₂ n : USize} (h : catRows n₁ n₂ = .ok n) : n.toNat = n₁.toNat + n₂.toNat := by
  unfold catRows at h
  split at h
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact USize.toNat_ofNat_of_lt' hlt
  · cases h

/-- **`Arr.clampShift c s x`** reads each long of `x` clamped into `[0, c]`, plus `s`, where `c + s` is below `2^63`. -/
theorem Arr.clampShift_get {n : USize} {c s : UInt64} {x y : Arr .i64 n} (hcs : c.toNat + s.toNat < 2 ^ 63)
    (h : x.clampShift c s = .ok y) (i : Fin n.toNat) :
    (y.get i).toInt = min (max (x.get i).toInt 0) c.toNat + s.toNat := by
  unfold Arr.clampShift colArr at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨-, -, -, hr⟩ := colMap_chain ho
    obtain ⟨x', y', v, W, hx, hy, hv, hw, ho'⟩ := hr i.1 i.2
    cases hx; cases hy; cases hv
    rw [Arr.get_i64, Arr.get_i64]
    show ((raw .i64 n o)[i.1]?.getD 0).toInt64.toInt = _
    rw [ho', Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1)]
    generalize (raw .i64 n x.enc)[i.1]?.getD 0 = w at hw ⊢
    have e : s + (if (if (0 : UInt64).toInt64 < w.toInt64 then w else 0).toInt64 < c.toInt64 then
        (if (0 : UInt64).toInt64 < w.toInt64 then w else 0) else c) = W := Except.ok.inj hw
    subst e
    have hc : c.toInt64.toInt = c.toNat := by rw [Verify.toInt_toInt64, if_pos (by omega)]
    have h0 : (0 : UInt64).toInt64.toInt = 0 := rfl
    have hz0 : (0 : UInt64).toNat = 0 := rfl
    have hW := Verify.toInt_toInt64 w
    have hw := UInt64.toNat_lt w
    -- each branch adds `s` to a word `X ≤ c`, which stays below `2^63`
    have key : ∀ X : UInt64, X.toNat ≤ c.toNat → (s + X).toInt64.toInt = X.toNat + s.toNat := fun X hX => by
      rw [Verify.toInt_toInt64, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]; omega
    simp only [Int64.lt_iff_toInt_lt, hc, h0]
    by_cases h1 : 0 < w.toInt64.toInt
    · simp only [h1, ↓reduceIte]
      by_cases h2 : w.toInt64.toInt < (c.toNat : Int)
      · simp only [h2, ↓reduceIte]; rw [key w (by split at hW <;> omega)]; split at hW <;> omega
      · simp only [h2, ↓reduceIte]; rw [key c (Nat.le_refl _)]; split at hW <;> omega
    · simp only [h1, ↓reduceIte, h0]
      by_cases h2 : (0 : Int) < c.toNat
      · simp only [h2, ↓reduceIte]; rw [key 0 (by rw [hz0]; omega)]; split at hW <;> omega
      · simp only [h2, ↓reduceIte]; rw [key c (Nat.le_refl _)]; split at hW <;> omega
  · cases h

/-- **`Arr.shift s x`** reads each long of `x` plus `s`, where that long is in `[0, 2^63 - s)`. -/
theorem Arr.shift_get {n : USize} {s : UInt64} {x y : Arr .i64 n} (h : x.shift s = .ok y) (i : Fin n.toNat)
    (h0 : 0 ≤ (x.get i).toInt) (hs : (x.get i).toInt + s.toNat < 2 ^ 63) :
    (y.get i).toInt = (x.get i).toInt + s.toNat := by
  unfold Arr.shift colArr at h
  split at h
  · rename_i o ho
    cases h
    have r3 := (colMap_post ho).2 i.1 i.2
    simp only [Op.eval] at r3; rw [UInt64.add_comm] at r3
    rw [Arr.get_i64] at h0 hs
    rw [Arr.get_i64, Arr.get_i64]
    show ((raw .i64 n o)[i.1]?.getD 0).toInt64.toInt = _
    generalize (raw .i64 n x.enc)[i.1]?.getD 0 = w at r3 h0 hs ⊢
    generalize (raw .i64 n o)[i.1]?.getD 0 = O at r3 ⊢
    have e3 : w + s = O := Except.ok.inj r3
    subst e3
    have hw := UInt64.toNat_lt w
    have hsl := UInt64.toNat_lt s
    have hW := Verify.toInt_toInt64 w
    split at hW
    · rw [hW] at h0 hs ⊢
      rw [Verify.toInt_toInt64, UInt64.toNat_add, if_pos (by omega)]; omega
    · omega
  · cases h

/-- The pairs of `List.finRange (a + b)` that `G` keeps: those of the first `a` positions, then of the last `b`. -/
theorem filterMap_finRange_add {α : Type} {M a b : Nat} (h : M = a + b) (G : Fin M → Option α) :
    (List.finRange M).filterMap G = (List.finRange a).filterMap (fun j => G ⟨j.1, by omega⟩) ++
      (List.finRange b).filterMap (fun j => G ⟨a + j.1, by omega⟩) := by
  subst h
  simp only [List.finRange, List.ofFn_add, List.filterMap_append]
  congr 1
  · rw [show (List.ofFn fun i : Fin a => Fin.castLE (Nat.le_add_right a b) i) =
      (List.ofFn fun i : Fin a => i).map (fun j => ⟨j.1, by omega⟩) from
      List.ext_getElem (by simp) (fun _ _ _ => by simp), List.filterMap_map]; rfl
  · rw [show (List.ofFn fun i : Fin b => Fin.natAdd a i) =
      (List.ofFn fun i : Fin b => i).map (fun j => ⟨a + j.1, by omega⟩) from
      List.ext_getElem (by simp) (fun _ _ _ => by simp [Fin.natAdd]), List.filterMap_map]; rfl

theorem sum_append_nat : ∀ l1 l2 : List Nat, (l1 ++ l2).sum = l1.sum + l2.sum
  | [], _ => by simp
  | x :: l, l2 => by simp [sum_append_nat l l2, Nat.add_assoc]

/-- A word below `2^63` read signed is its `Nat`. -/
theorem toInt64_toInt {x : UInt64} (h : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat := by
  rw [show x.toInt64.toInt = x.toBitVec.toInt from rfl, BitVec.toInt]; simp only [UInt64.toNat_toBitVec]
  omega

/-- The signed reading of a word: itself below `2^63`, itself less `2^64` from there. -/
theorem toInt64_toInt_cond (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64 := by
  split
  · exact toInt64_toInt (by assumption)
  · rename_i hx
    have := x.toNat_lt
    simp only [UInt64.toInt64, Int64.toInt, Int64.toBitVec, BitVec.toInt_eq_toNat_cond, UInt64.toNat] at *
    rw [if_neg (by omega)]; simp

/-- A word whose signed reading is not negative is below `2^63` and reads as itself. -/
theorem toInt64_nonneg {x : UInt64} (h : 0 ≤ x.toInt64.toInt) : x.toNat < 2 ^ 63 ∧ x.toInt64.toInt = x.toNat := by
  rw [toInt64_toInt_cond] at h ⊢
  have := x.toNat_lt
  split at h <;> rename_i hx
  · rw [if_pos hx]; exact ⟨hx, rfl⟩
  · omega

/-- A `Nat` below `2^64` is its word's `Nat`. -/
theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by simp; omega

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
    simp only [Op.eval, hw 0 hG, Except.ok.injEq] at this
    rw [← this]; simp
  | succ G ih =>
    have := hr (G + 1) hG
    rw [if_neg (by omega), Nat.add_sub_cancel, ih (by omega), hw _ hG] at this
    simp only [Op.eval, Except.ok.injEq] at this
    rw [← this]; simp only [List.range_succ, List.map_append, sum_append_nat, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]; exact (UInt64.ofNat_add _ _).symm

/-- `kscan`'s answer is a `foR` column. -/
theorem kscan_foR {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc} {es : List (USize × Enc)}
    {pre post : List (Op × UInt64)} {r : Enc × Option UInt64} (h : kscan op rev s t n seg es pre post = .ok r) :
    ∃ md pk, r.1 = .foR md pk := by
  unfold kscan at h
  by_cases hd : kscanRefuses op n es pre post = true
  · simp only [hd, ↓reduceIte] at h; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  simp only [Except.ok.injEq] at h
  subst h; exact ⟨_, _, rfl⟩

/-- **A one-source `kscan .first` at no `seg` writes `chain post` of each word** (`colMap_chain` with one source): word `i`
of the answer is `chain post` of word `i` of `a`, a boolean answer's cut to its bit. -/
theorem kscan_first_chain {s t : QAtomicType} {n : USize} {a : Enc} {post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hs : kscanStream .first [(n, a)] [] post = false) (h : kscan .first false s t n none [(n, a)] [] post = .ok r) :
    (raw s n a).size = n.toNat ∧ (raw .i64 n r.1).size = n.toNat ∧ ∀ i < n.toNat, ∃ w,
      chain post ((raw s n a)[i]?.getD 0) = .ok w ∧ (raw .i64 n r.1)[i]? = some (if t = .u1 then w % 2 else w) := by
  have hr := h
  unfold kscan at hr
  by_cases hd : kscanRefuses .first n [(n, a)] [] post = true
  · simp only [hd, ↓reduceIte] at hr; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure, segAll] at hr
  split at hr; · cases hr
  rename_i cs hc
  split at hr; · cases hr
  rename_i ca cs' ns
  obtain ⟨-, hns, hcc⟩ := kscanCols_lock hs hc
  obtain ⟨hl, hP⟩ := mapM_chain hcc
  rcases cs' with _ | ⟨_, _⟩ <;> try simp at hl
  obtain ⟨ha, -, hra⟩ := hP (a, ca) (by simp)
  split at hr; · cases hr
  rename_i out₀ hf
  split at hr; · cases hr
  rename_i out hp
  split at hr; · cases hr
  rename_i w' ht
  split at hr; · cases hr
  rename_i nl hnl
  simp only [Except.ok.injEq] at hr
  subst hns
  have ho : r.1 = wordsFoR (out.map fun v => if t = .u1 then v % 2 else v) := by
    rw [← hr]; first | rfl | simp [wordsFoR]
  rw [ho]; clear ho hr
  obtain ⟨hos, hrow⟩ := foldlM_kscanRow _ _ _ _ _ _ hf
  obtain ⟨hps, hpr⟩ := chainAll_ok hp
  have hW : (out.map fun v => if t = .u1 then v % 2 else v).size = n.toNat := by simp [hps, hos]
  refine ⟨ha, ?_, fun i hi => ?_⟩
  · rw [(wordsFoR_closed _ hW.symm).2.1]; exact hW
  rw [(wordsFoR_closed _ hW.symm).2.1]
  have hr := hrow i (by omega)
  rw [if_neg (fun hh => by simp [hi] at hh)] at hr
  simp only [List.map_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hr
  have hq := hpr i (by omega)
  have e : (raw s n a)[i]?.getD 0 = ca[i]?.getD 0 :=
    Except.ok.inj (by have := hra i hi; simpa only [chain, List.foldlM_nil] using this)
  refine ⟨out[i]?.getD 0, ?_, ?_⟩
  · rw [e, hr]; simpa [Array.getElem?_eq_getElem (show i < out₀.size by omega)] using hq
  · simp [Array.getElem?_eq_getElem (show i < out.size by omega)]

/-- **`lastCount` reads the last word**: `x` where the last of the `K` words is `x < 2^63`, `0` at `K = 0`. -/
theorem lastCount_eq {K : USize} {P : Enc} (hw : Enc.WF .i64 K P) (hN : hasNul P = false)
    (hf : ∃ md pk, P = .foR md pk) {x : Nat} (hx : x < 2 ^ 63) (hl : 0 < K.toNat → (raw .i64 K P)[K.toNat - 1]?.getD 0 = x.toUInt64)
    (h0 : K.toNat = 0 → x = 0) : lastCount K P hw hN = x := by
  unfold lastCount
  split
  · rename_i hk
    obtain ⟨md, pk, rfl⟩ := hf
    rw [Arr.get_raw_foR (Arr.mk _ hw hN) rfl]; change ((raw .i64 K (Enc.foR md pk))[K.toNat - 1]?.getD 0).toInt64.toNatClampNeg = x
    rw [hl hk, ← Int64.toNat_toInt,
      toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega)]
    simp
  · exact (h0 (by omega)).symm

/-- **`summandPos n s tag idx`** is `idx` on the rows `tag` gives to the summand `s`, `0` on the others. -/
theorem summandPos_raw {n : USize} {s : Bool} {tag : Arr .u1 n} {idx : Enc} {p : Enc}
    (h : summandPos n s tag idx = .ok p) (hv : Kernel.Enc.Valid n tag.enc) (q : Fin n.toNat) :
    (raw .i64 n p)[q.1]?.getD 0 = if tag.get q = s then (raw .i64 n idx)[q.1]?.getD 0 else 0 := by
  obtain ⟨t, ht, et⟩ := Arr.get_u1 tag hv q
  have hi64 : ¬ (QAtomicType.i64 = .u1) := by decide
  unfold summandPos at h
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
    split at h; · cases h
    rename_i nt hnt
    obtain ⟨v1, e1, h1⟩ := (colMap_get hnt).2 q q.2
    obtain ⟨v2, e2, h2⟩ := (colMap_get h).2 q q.2
    simp only [ht, Option.getD_some, Op.eval, Except.ok.injEq] at e1; subst e1
    simp only [h1, if_neg hi64, Option.getD_some, Op.eval, Except.ok.injEq] at e2; subst e2
    simp only [h2, if_neg hi64, Option.getD_some]
    rw [et]; cases tag.get q <;> simp
  · simp only [↓reduceIte] at h
    obtain ⟨v2, e2, h2⟩ := (colMap_get h).2 q q.2
    simp only [ht, Option.getD_some, Op.eval, Except.ok.injEq] at e2; subst e2
    simp only [h2, if_neg hi64, Option.getD_some]
    rw [et]; cases tag.get q <;> simp

/-- Both columns of a successful `Arr.concat` are ones every kernel reads (the `foROk` guard of its stream). -/
theorem Arr.concat_valid {t : QAtomicType} {n₁ n₂ n : USize} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (h : Arr.concat n x y = .ok z) : Kernel.Enc.Valid n₁ x.enc ∧ Kernel.Enc.Valid n₂ y.enc := by
  unfold Arr.concat at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i zo hzo
  obtain ⟨-, -, -, hx, hy, -⟩ := Opt.concat_enc hzo
  exact ⟨foROk_valid hx, foROk_valid hy⟩

/-- **`Arr.pos n` holds the positions**: row `c` is `c`. -/
theorem Arr.pos_get {n : USize} {P : Arr .i64 n} (h : Arr.pos n = .ok P) (c : Fin n.toNat) :
    P.get c = c.1.toUInt64.toInt64 := by
  unfold Arr.pos at h
  split at h
  · rename_i o ho
    cases h
    rw [Arr.get_i64]
    show ((raw .i64 n o)[c.1]?.getD 0).toInt64 = _
    rw [shiftCol_raw ho c.1 c.2, UInt64.add_zero]
  · cases h

/-- **`Arr.pos n` read as positions**: row `c` clamped into `n` rows is `c`, `n` at most `2^63`. -/
theorem Arr.pos_clamp {n : USize} {P : Arr .i64 n} (h : Arr.pos n = .ok P) (hn : n.toNat ≤ 2 ^ 63) (c : Fin n.toNat)
    (h0 : 0 < n.toNat) : clampFin (P.get c) n.toNat h0 = c := by
  have hc : (c.1.toUInt64).toNat = c.1 := by
    have := c.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [Arr.pos_get h c]
  exact (clampFin_word h0 (by rw [hc]; exact c.2) hn).trans (Fin.ext hc)

/-- **A `tagCount` of `0`**: no row is tagged into the summand `s`. -/
theorem tagCount_zero {n : USize} {s : Bool} {tag : Arr .u1 n} (h : tagCount n s tag = .ok 0)
    (hv : Kernel.Enc.Valid n tag.enc) (q : Fin n.toNat) : tag.get q ≠ s := by
  unfold tagCount at h
  split at h; · cases h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i p hp
  split at h
  · rename_i P hP
    simp only [Except.ok.injEq] at h
    have hf : ∃ md pk, P = .foR md pk := by
      unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
      split at hP; · cases hP
      rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at hP; subst hP
      exact kscan_foR hr
    -- `wN G`: row `G` is tagged into `s`
    obtain ⟨wN, hwN⟩ : ∃ f : Nat → Nat, f = fun G => if hG : G < n.toNat then (if tag.get ⟨G, hG⟩ = s then 1 else 0) else 0 := ⟨_, rfl⟩
    have hw : ∀ G < n.toNat, (raw .i64 n p.1)[G]?.getD 0 = (wN G).toUInt64 := fun G hG => by
      -- word `G` of `p` is `tag`'s bit, or its `.not` at `s = false` (`kscan_first_chain`)
      obtain ⟨t, ht, et⟩ := Arr.get_u1 tag hv ⟨G, hG⟩
      obtain ⟨w, hc, ho⟩ := (kscan_first_chain (by cases s <;> simp [kscanStream]) hp).2.2 G hG
      rw [ho, hwN]; simp only [dif_pos hG, if_neg (by decide : ¬ (QAtomicType.i64 = .u1)), Option.getD_some]
      simp only [ht, Option.getD_some] at hc
      rw [et] at hc
      generalize tag.get ⟨G, hG⟩ = b at hc ⊢
      cases s <;> cases b <;> simp [chain, Op.eval, List.foldlM, pure, Except.pure, bind, Except.bind] at hc <;>
        subst hc <;> decide
    have key : ∀ k, ((List.range k).map wN).sum ≤ k ∧ (q.1 < k → wN q.1 ≤ ((List.range k).map wN).sum) := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, sum_append_nat]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have h1 : wN k ≤ 1 := by rw [hwN]; dsimp only; split <;> (try split) <;> omega
        refine ⟨by omega, fun hk => ?_⟩
        by_cases e : q.1 = k
        · rw [e]; omega
        · have := ih.2 (by omega); omega
    have hc := lastCount_eq (colPrefix_closed hP).2 (colPrefix_plain hP) hf (x := ((List.range n.toNat).map wN).sum)
      (by have := (key n.toNat).1; omega)
      (fun hn => by rw [colPrefix_add_sum hP wN hw _ (by omega), Nat.sub_add_cancel hn])
      (fun hn => by rw [hn]; rfl)
    rw [h] at hc
    have h0 : wN q.1 = 0 := by have := (key n.toNat).2 q.2; omega
    rw [hwN] at h0; simp only [dif_pos q.2] at h0
    intro e; rw [if_pos e] at h0; exact absurd h0 (by decide)
  · cases h

/-- **Summand `s` of one side, `Vals.catSide`**, read at a row `q` the tags give to it: the summand is not empty, and
the row is its row at `q`'s position clamped. -/
theorem Vals.catSide_row {B : Obj} {m l l' : USize} {s : Bool} {tag : Arr .u1 m} {idx : Arr .i64 m} {x : Vals B l}
    {o : Vals B l'} {g : Vals B m} (h : Vals.catSide s tag idx x o = .ok g) (hv : Kernel.Enc.Valid m tag.enc)
    (h63 : l.toNat ≤ 2 ^ 63) (q : Fin m.toNat) (ht : tag.get q = s) :
    ∃ hl : 0 < l.toNat, Vals.row g q = Vals.row x (clampFin (idx.get q) l.toNat hl) := by
  unfold Vals.catSide at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc
    split at h
    · rename_i hc0; subst hc0; exact absurd ht (tagCount_zero hc hv q)
    · cases h
  · rename_i hl0
    have hl : 0 < l.toNat := by omega
    refine ⟨hl, ?_⟩
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i k hk
    split at h; · cases h
    rename_i p hp
    rw [Vals.summand_row tag k s x h h63 hl (summandPos_raw hp hv) q, if_pos ht]
    -- the clamped positions clamp as the stored ones (`Arr.clampShift_get`)
    have hU : (l.toUInt64 - 1).toNat = l.toNat - 1 := by
      have := l.toNat_lt_size; have := USize.size_le
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have e := Arr.clampShift_get (by rw [hU]; simp; omega) hk q
    rw [hU] at e
    congr 1; apply Fin.ext; simp only [clampFin]; simp at e; omega

/-- **`readVals` establishes `Vals.WF`**: its `arr` case refuses unless `cellBad` finds no cell, which is the cell
clause; the payload is read by the same function. -/
theorem cellBad_none {n m : USize} {lo hi : Arr .i64 n} : cellBad m lo hi = none ↔ ∀ i : Fin n.toNat,
    0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
  simp [cellBad, List.find?_eq_none]

/-- **`Vals.cellsOk` decides `Vals.WF`** in the direction a literal needs: its `arr` clause is `cellBad_none`. -/
theorem Vals.cellsOk_wf : {A : Obj} → {n : USize} → {x : Vals A n} → Vals.cellsOk x = true → Vals.WF x
  | .atom _, _, _, _ | .one, _, _, _ => trivial
  | .prod _ _, _, _, h => by
    simp only [Vals.cellsOk, Bool.and_eq_true] at h; exact ⟨Vals.cellsOk_wf h.1, Vals.cellsOk_wf h.2⟩
  | .arr _, _, ⟨_, _, _, _⟩, h => by
    simp only [Vals.cellsOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact ⟨cellBad_none.1 h.1, Vals.cellsOk_wf h.2⟩
  | .sum _ _, _, s, h => by
    simp only [Vals.cellsOk] at h; simp only [Vals.WF]
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, l, r, tag, idx, x, y⟩ <;> simp only [hv, Bool.and_eq_true] at h ⊢
    exact ⟨Vals.cellsOk_wf h.1, Vals.cellsOk_wf h.2⟩

/-- **`Vals.nub` keeps `Vals.WF`**: its rows are `Vals.gather`ed from `x`. -/
theorem Vals.nub_wf {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    (hx : Vals.WF x) : Vals.WF r.2 := by
  unfold Vals.nub at h
  simp only [bind, Except.bind, Functor.map, Except.map] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i y hg; cases h; exact Vals.gather_wf hg hx

/-- **`Tab.canon` keeps `Tab.WF`** (`Vals.nub_wf` of the pair side). -/
theorem Tab.canon_wf {k v : Obj} {R t : Tab k v} (h : R.canon = .ok t) (hR : Tab.WF R) : Tab.WF t := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error e => simp [hn, Functor.map, Except.map] at h
  | ok y => simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h; subst h; exact Vals.nub_wf hn hR

/-- **`Vals.catSide` keeps `Vals.WF`**: its rows are gathered from `x`, or from `o` where `x` is empty. -/
theorem Vals.catSide_wf {B : Obj} {m l l' : USize} {s : Bool} {tag : Arr .u1 m} {idx : Arr .i64 m} {x : Vals B l}
    {o : Vals B l'} {y : Vals B m} (h : Vals.catSide s tag idx x o = .ok y) (hx : Vals.WF x) (ho : Vals.WF o) :
    Vals.WF y := by
  unfold Vals.catSide at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    split at h
    · split at h; · cases h
      exact Vals.gather_wf h ho
    · cases h
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    split at h; · cases h
    exact Vals.gather_wf h hx

/-- **A summand of `Vals.catSummand`** read at row `c`, which the tags give to it, through positions `P` that clamp to
themselves: the summand's value of row `c` of the first side below `n₁`, of row `c - n₁` of the second from there,
given `cat` concatenates (`Vals.concat_row`). -/
theorem Vals.catSummand_row {B : Obj} {n₁ n₂ n l₁ l₂ : USize} {s : Bool} {tag₁ : Arr .u1 n₁}
    {idx₁ : Arr .i64 n₁} {x₁ : Vals B l₁} {tag₂ : Arr .u1 n₂} {idx₂ : Arr .i64 n₂} {x₂ : Vals B l₂}
    {cat : {m₁ m₂ : USize} → (m : USize) → Vals B m₁ → Vals B m₂ → Except String (Vals B m)}
    {L : (m : USize) × Vals B m} (hn : n.toNat = n₁.toNat + n₂.toNat)
    (hcat : ∀ {m₁ m₂ m : USize} {z : Vals B m} (x : Vals B m₁) (y : Vals B m₂),
      (hm : m.toNat = m₁.toNat + m₂.toNat) →
      cat m x y = .ok z → Vals.WF x → Vals.WF y → ∀ c : Fin m.toNat, Vals.row z c =
        if hc : c.1 < m₁.toNat then Vals.row x ⟨c.1, hc⟩ else Vals.row y ⟨c.1 - m₁.toNat, by omega⟩)
    (hv₁ : Kernel.Enc.Valid n₁ tag₁.enc) (hv₂ : Kernel.Enc.Valid n₂ tag₂.enc) (hx₁ : Vals.WF x₁) (hx₂ : Vals.WF x₂)
    (h : Vals.catSummand n s tag₁ idx₁ x₁ tag₂ idx₂ x₂ cat = .ok L)
    {P : Arr .i64 n} (hP : ∀ c h0, clampFin (P.get c) n.toNat h0 = c) (c : Fin n.toNat)
    (ht : (if hc : c.1 < n₁.toNat then tag₁.get ⟨c.1, hc⟩ else tag₂.get ⟨c.1 - n₁.toNat, by omega⟩) = s) :
    (if h0 : 0 < L.1.toNat then Vals.row L.2 (clampFin (P.get c) L.1.toNat h0) else B.dflt) =
      if hc : c.1 < n₁.toNat then
        (if h0 : 0 < l₁.toNat then Vals.row x₁ (clampFin (idx₁.get ⟨c.1, hc⟩) l₁.toNat h0) else B.dflt)
      else if h0 : 0 < l₂.toNat then
        Vals.row x₂ (clampFin (idx₂.get ⟨c.1 - n₁.toNat, by omega⟩) l₂.toNat h0) else B.dflt := by
  unfold Vals.catSummand at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    cases h
    have hpn := catRows_ok hp
    rw [dif_neg (by dsimp only; omega)]
    split <;> rw [dif_neg (by omega)]
  · split at h; · cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i g₁ hg₁
    split at h; · cases h
    rename_i g₂ hg₂
    split at h; · cases h
    rename_i G hG
    cases h
    have hc0 : 0 < n.toNat := by have := c.2; omega
    show (if h0 : 0 < n.toNat then Vals.row G (clampFin (P.get c) n.toNat h0) else B.dflt) = _
    rw [dif_pos hc0, hP c hc0,
      hcat g₁ g₂ hn hG (Vals.catSide_wf hg₁ hx₁ hx₂) (Vals.catSide_wf hg₂ hx₂ hx₁) c]
    split
    · rename_i hc
      rw [dif_pos hc] at ht
      obtain ⟨hl, e⟩ := Vals.catSide_row hg₁ hv₁ (by omega) ⟨c.1, hc⟩ ht
      rw [dif_pos hl, e]
    · rename_i hc
      rw [dif_neg hc] at ht
      obtain ⟨hl, e⟩ := Vals.catSide_row hg₂ hv₂ (by omega) _ ht
      rw [dif_pos hl, e]

/-- **`Vals.catSummand` keeps `Vals.WF`** where `cat` does. -/
theorem Vals.catSummand_wf {B : Obj} {n₁ n₂ n l₁ l₂ : USize} {s : Bool} {tag₁ : Arr .u1 n₁}
    {idx₁ : Arr .i64 n₁} {x₁ : Vals B l₁} {tag₂ : Arr .u1 n₂} {idx₂ : Arr .i64 n₂} {x₂ : Vals B l₂}
    {cat : {m₁ m₂ : USize} → (m : USize) → Vals B m₁ → Vals B m₂ → Except String (Vals B m)}
    (hcat : ∀ {m₁ m₂ m : USize} {a : Vals B m₁} {b : Vals B m₂} {z : Vals B m},
      m.toNat = m₁.toNat + m₂.toNat → cat m a b = .ok z → Vals.WF a → Vals.WF b → Vals.WF z)
    (hn : n.toNat = n₁.toNat + n₂.toNat)
    {z : (m : USize) × Vals B m} (h : Vals.catSummand n s tag₁ idx₁ x₁ tag₂ idx₂ x₂ cat = .ok z)
    (h₁ : Vals.WF x₁) (h₂ : Vals.WF x₂) : Vals.WF z.2 := by
  unfold Vals.catSummand at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    rename_i hc; cases h
    exact hcat (catRows_ok hp) hc h₁ h₂
  split at h; · cases h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i a ha
  split at h; · cases h
  rename_i b hb
  split at h; · cases h
  rename_i hc; cases h
  exact hcat hn hc (Vals.catSide_wf ha h₁ h₂) (Vals.catSide_wf hb h₂ h₁)

/-- **`Vals.concat` keeps `Vals.WF`**: a cell of `x` stays inside the first `m₁` payload rows, one of `y` moves
past them by `m₁`, inside the `m₁ + m₂` rows of the joined payload. -/
theorem Vals.concat_wf : {A : Obj} → {n₁ n₂ n : USize} → (hn : n.toNat = n₁.toNat + n₂.toNat) →
    {x : Vals A n₁} → {y : Vals A n₂} → {z : Vals A n} → Vals.concat n x y = .ok z →
      Vals.WF x → Vals.WF y → Vals.WF z
  | .atom _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .one, _, _, _, _, _, _, _, _, _, _ => trivial
  | .prod _ _, _, _, _, hn, x, y, z, h, hx, hy => by
    simp only [Vals.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    exact ⟨Vals.concat_wf hn h1 hx.1 hy.1, Vals.concat_wf hn h2 hx.2 hy.2⟩
  | .arr _, n₁, n₂, _, hn, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, z, h, hx, hy => by
    simp only [Vals.concat] at h
    split at h
    case isFalse => cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    rename_i L₂ hL₂
    split at h; · cases h
    rename_i lo hlo
    split at h; · cases h
    rename_i H₂ hH₂
    split at h; · cases h
    rename_i hi hhi
    split at h; · cases h
    rename_i F hF
    cases h
    have hpn := catRows_ok hp
    refine ⟨fun c => ?_, Vals.concat_wf hpn hF hx.2 hy.2⟩
    have hU : ∀ m : USize, m.toUInt64.toNat = m.toNat := fun m => by
      have := m.toNat_lt_size; have := USize.size_le; simp
    rw [Arr.concat_get hn hlo c, Arr.concat_get hn hhi c]
    split
    · rename_i hc
      have := hx.1 ⟨c.1, hc⟩
      omega
    · rename_i hc
      have hc' : c.1 - n₁.toNat < n₂.toNat := by omega
      have := hy.1 ⟨_, hc'⟩
      have l2 := Arr.shift_get hL₂ ⟨_, hc'⟩ (by omega) (by rw [hU]; omega)
      have h2 := Arr.shift_get hH₂ ⟨_, hc'⟩ (by omega) (by rw [hU]; omega)
      rw [hU] at l2 h2
      rw [l2, h2]; omega
  | .sum _ _, _, _, _, hn, s₁, s₂, z, h, hx, hy => by
    simp only [Vals.concat] at h
    rcases hv₁ : s₁.view with ⟨hb₁, x₁⟩ | ⟨hb₁, _, _, tag₁, idx₁, x₁, y₁⟩ <;>
      rcases hv₂ : s₂.view with ⟨hb₂, x₂⟩ | ⟨hb₂, _, _, tag₂, idx₂, x₂, y₂⟩ <;> simp only [hv₁, hv₂] at h
    · simp only [Functor.map, Except.map] at h
      split at h; · cases h
      cases h; simp only [Vals.WF, Vals.view_ofOpt]
    · exact absurd (hb₁.symm.trans hb₂) nofun
    · exact absurd (hb₂.symm.trans hb₁) nofun
    simp only [Vals.WF, hv₁, hv₂] at hx hy
    split at h
    case isFalse => cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i L hL
    split at h; · cases h
    rename_i R hR
    split at h; · cases h
    split at h; · cases h
    cases h
    simp only [Vals.WF, Vals.view_ofGen]
    exact ⟨Vals.catSummand_wf (fun hm hc a b => Vals.concat_wf hm hc a b) hn hL hx.1 hy.1,
      Vals.catSummand_wf (fun hm hc a b => Vals.concat_wf hm hc a b) hn hR hx.2 hy.2⟩

/-- **Row `c` of `Vals.concat`** is row `c` of `x` below `n₁`, row `c - n₁` of `y` from there. -/
theorem Vals.concat_row : {A : Obj} → {n₁ n₂ n : USize} → (hn : n.toNat = n₁.toNat + n₂.toNat) →
    (x : Vals A n₁) → (y : Vals A n₂) → {z : Vals A n} → Vals.concat n x y = .ok z → Vals.WF x → Vals.WF y →
      ∀ c : Fin n.toNat, Vals.row z c =
        if hc : c.1 < n₁.toNat then Vals.row x ⟨c.1, hc⟩ else Vals.row y ⟨c.1 - n₁.toNat, by omega⟩
  | .atom _, _, _, _, hn, x, y, z, h, _, _, c => Arr.concat_get hn h c
  | .prod _ _, _, _, _, hn, x, y, z, h, hx, hy, c => by
    simp only [Vals.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    show (Vals.row z1 c, Vals.row z2 c) = _
    rw [Vals.concat_row hn x.1 y.1 h1 hx.1 hy.1 c, Vals.concat_row hn x.2 y.2 h2 hx.2 hy.2 c]
    split <;> rfl
  | .arr _, n₁, n₂, _, hn, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, z, h, hx, hy, c => by
    simp only [Vals.concat] at h
    split at h
    case isFalse => cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    rename_i L₂ hL₂
    split at h; · cases h
    rename_i lo hlo
    split at h; · cases h
    rename_i H₂ hH₂
    split at h; · cases h
    rename_i hi hhi
    split at h; · cases h
    rename_i F hF
    cases h
    have hpn := catRows_ok hp
    have hrow := Vals.concat_row hpn f₁ f₂ hF hx.2 hy.2
    have hU : ∀ m : USize, m.toUInt64.toNat = m.toNat := fun m => by
      have := m.toNat_lt_size; have := USize.size_le; simp
    have gl := Arr.concat_get hn hlo c
    have gh := Arr.concat_get hn hhi c
    simp only [Vals.row]
    rw [filterMap_finRange_add hpn]
    split
    · rename_i hc
      have := hx.1 ⟨c.1, hc⟩
      rw [dif_pos hc] at gl gh
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₂.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gh]; dsimp only; omega, List.append_nil]
      congr 1; funext j
      rw [hrow, dif_pos j.2, gl, gh]
    · rename_i hc
      have hc' : c.1 - n₁.toNat < n₂.toNat := by omega
      have := hy.1 ⟨_, hc'⟩
      have l2 := Arr.shift_get hL₂ ⟨_, hc'⟩ (by omega) (by rw [hU]; omega)
      have h2 := Arr.shift_get hH₂ ⟨_, hc'⟩ (by omega) (by rw [hU]; omega)
      rw [dif_neg hc] at gl gh
      rw [hU] at l2 h2
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₁.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gl, l2]; have := j.2; dsimp only; omega,
        List.nil_append]
      congr 1; funext j
      rw [hrow, dif_neg (by dsimp only; omega), gl, gh, l2, h2]
      have hj : (⟨m₁.toNat + j.1 - m₁.toNat, by omega⟩ : Fin m₂.toNat) = j := Fin.ext (by simp)
      rw [hj]
      by_cases hA : (lo₂.get ⟨_, hc'⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi₂.get ⟨_, hc'⟩).toInt
      · rw [if_pos hA, if_pos (by dsimp only; omega)]
      · rw [if_neg hA, if_neg (by dsimp only; omega)]
  | .sum _ _, n₁, _, _, hn, s₁, s₂, z, h, hx, hy, c => by
    simp only [Vals.concat] at h
    rcases hs₁ : s₁.view with ⟨hb₁, x₁⟩ | ⟨hb₁, _, _, tag₁, idx₁, x₁, y₁⟩ <;>
      rcases hs₂ : s₂.view with ⟨hb₂, x₂⟩ | ⟨hb₂, _, _, tag₂, idx₂, x₂, y₂⟩ <;> simp only [hs₁, hs₂] at h
    · obtain rfl := Option.some.inj (hb₂.symm.trans hb₁)
      simp only [Functor.map, Except.map] at h
      split at h; · cases h
      rename_i w hw
      cases h
      simp only [Vals.row, hs₁, hs₂, Vals.view_ofOpt, Opt.concat_get hn hw c]
      split <;> rfl
    · exact absurd (hb₁.symm.trans hb₂) nofun
    · exact absurd (hb₂.symm.trans hb₁) nofun
    simp only [Vals.WF, hs₁, hs₂] at hx hy
    split at h
    case isFalse => cases h
    rename_i hn63
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i L hL
    split at h; · cases h
    rename_i R hR
    split at h; · cases h
    rename_i tag htag
    split at h; · cases h
    rename_i P hP
    cases h
    obtain ⟨hv₁, hv₂⟩ := Arr.concat_valid htag
    have hpos := fun c h0 => Arr.pos_clamp hP hn63 c h0
    have gt := Arr.concat_get hn htag c
    cases hb : tag.get c
    · have e := Vals.catSummand_row hn (fun x y hm hz => Vals.concat_row hm x y hz) hv₁ hv₂ hx.1 hy.1 hL hpos c
        (by rw [← gt, hb])
      simp only [Vals.row, Vals.view_ofGen, hs₁, hs₂, hb, Bool.false_eq_true, ↓reduceIte]
      rw [e]
      split
      · rename_i hc; rw [dif_pos hc] at gt; rw [← gt, hb]; rfl
      · rename_i hc; rw [dif_neg hc] at gt; rw [← gt, hb]; rfl
    · have e := Vals.catSummand_row hn (fun x y hm hz => Vals.concat_row hm x y hz) hv₁ hv₂ hx.2 hy.2 hR hpos c
        (by rw [← gt, hb])
      simp only [Vals.row, Vals.view_ofGen, hs₁, hs₂, hb, ↓reduceIte]
      rw [e]
      split
      · rename_i hc; rw [dif_pos hc] at gt; rw [← gt, hb]; rfl
      · rename_i hc; rw [dif_neg hc] at gt; rw [← gt, hb]; rfl
  | .one, _, _, _, _, _, _, _, _, _, _, c => by split <;> rfl

/-! ## Checks: CONCAT keeps every stored word -/


end Rel
