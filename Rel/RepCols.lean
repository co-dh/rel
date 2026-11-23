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
theorem colPrefix_raw {op : Op} {n : USize} {a e : Enc} (h : colPrefix op n a = .ok e) (ho : op ≠ .first := by decide)
    (hn : op ≠ .null := by decide) (hF : op.nulFold = none ∨ hasNul a = false := by nulfree) :
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
    raw_kscan op hn false .i64 .i64 8 rfl n z [(n, z), (n, a)] r (kscanStream_ne ho _ _ _) (colPrefix_hF hz hF) hr
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
    (h : colMap op n a b .i64 s = .ok e) (hk : kscanStream op [(n, a), (n, b)] [] [] = false := by lockstep)
    (hn : op ≠ .null := by decide)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by nulfree) :
    (raw s n a).size = n.toNat ∧ (raw s n b).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧
      ∀ i < n.toNat, op.eval ((raw s n a)[i]?.getD 0) ((raw s n b)[i]?.getD 0) = .ok ((raw .i64 n e)[i]?.getD 0) := by
  obtain ⟨ha, hb, hs, hr⟩ := colMap_chain h hk hn hF
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
    (hl : kscanStream op' [(n, a), (n, k)] [] [] = false := by lockstep)
    (hn : op' ≠ .null := by decide)
    (hF : op'.nulFold = none ∨ ∀ p ∈ [(n, a), (n, k)], hasNul p.2 = false := by nulfree) : raw .i64 n e = raw .i64 n e' := by
  obtain ⟨-, -, hs, hr⟩ := colMap_raw h hl hn hF
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

/-- A word `w` below `2^63 - s` as a long, shifted by `s`: the addition does not wrap. -/
theorem Int64.toInt_add_shift (w s : UInt64) (h0 : 0 ≤ w.toInt64.toInt) (hs : w.toInt64.toInt + s.toNat < 2 ^ 63) :
    (w + s).toInt64.toInt = w.toInt64.toInt + s.toNat := by
  have hw := UInt64.toNat_lt w
  have hsl := UInt64.toNat_lt s
  have hW := Verify.toInt_toInt64 w
  split at hW
  · rw [hW] at h0 hs ⊢
    rw [Verify.toInt_toInt64, UInt64.toNat_add, if_pos (by omega)]; omega
  · omega

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
    exact Int64.toInt_add_shift w s h0 hs
  · cases h

/-- **`colMap .max n a a` with the post step `add s` flags and shifts as `Opt.shift` says**: row `i` of the answer has
`a`'s own flag (`foRNuls`: `kscan_nul_row` flags `and` of the sources' flags, `a` twice) and, off a null, the word `s + a[i]`
(`max` of a word with itself is the word, `fill` read at a null being no word of the answer). -/
theorem colMap_max_self {n : USize} {a o : Enc} {s : UInt64} (hW : Enc.WF .i64 n a)
    (h : colMap .max n a a .i64 .i64 [] [(.add, s)] = .ok o) : ∀ i < n.toNat,
      (foRNuls n o)[i]? = (foRNuls n a)[i]? ∧
        ((foRNuls n a)[i]? = some 0 → (raw .i64 n o)[i]? = some (s + (raw .i64 n a)[i]?.getD 0)) := by
  have hs : kscanStream .max [(n, a), (n, a)] [] [(.add, s)] = false := by simp [kscanStream]
  have hWs : ∀ p ∈ [(n, a), (n, a)], Ext.Enc.WF .i64 p.1 p.2 := fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> exact hW
  by_cases hN : hasNul a = true
  · unfold colMap at h; simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨out, nl, hos, hnl, hr1, hV, hF, p, ps, hes, hrow⟩ := kscan_nul_row (b := .and)
      (fill := 0x8000000000000000) rfl (by decide : (QAtomicType.i64).width = some 8) (by decide) hs hWs ⟨(n, a), by simp, hN⟩ hr
    simp only [List.cons.injEq] at hes; obtain ⟨rfl, rfl, -⟩ := hes
    intro i hi
    obtain ⟨hv, hn1, hn2⟩ := hrow i hi
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, Op.eval, bind, Except.bind, pure,
      Except.pure, UInt64.and_self, Except.ok.injEq] at hn1
    have hf := foRNuls_bit n a hi
    have e1 : (foRNuls n r.1)[i]? = (foRNuls n a)[i]? := by
      rw [hn2, hf]; show (some (if nl[i]?.getD 0 != 0 then 1 else 0) : Option UInt64) = _
      rw [← hn1]; rfl
    refine ⟨e1, fun h0 => ?_⟩
    have hsz : n.toNat = (out.map (cutBit .i64)).size := by simp [hos]
    have hb : Column.bitAt (nulMap nl) i = false := by
      have h1 := foRNuls_wordsFoR (out.map (cutBit .i64)) (nulMap nl) hsz i (by simpa [hos] using hi)
      rw [← hr1, e1, h0] at h1
      cases hb : Column.bitAt (nulMap nl) i <;> simp_all
    have h2 := raw_wordsFoR_of_bit (out.map (cutBit .i64)) (nulMap nl) (m := n) (by simp [hos]) i
      (by simpa [hos] using hi) hb
    rw [← hr1] at h2
    have hr0 : rdNul n a i = 0 := by simp only [rdNul, h0]; rfl
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, Op.eval, bind, Except.bind, pure,
      Except.pure, rdFill, hr0, bne_self_eq_false, Bool.false_eq_true, if_false, chain, ite_self, Except.ok.injEq,
      Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some] at hv
    rw [h2]; simp only [Array.getElem_map, cutBit, if_neg (by decide : QAtomicType.i64 ≠ .u1), ← hv]
  · have hN' : hasNul a = false := by simpa using hN
    have hF : (Op.max).nulFold = none ∨ ∀ p ∈ [(n, a), (n, a)], hasNul p.2 = false := Or.inr fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> exact hN'
    have hC := colMap_closed hs h hF
    have hP := hC.2.2
    obtain ⟨-, -, -, hrow⟩ := colMap_chain h hs (by decide) hF
    intro i hi
    refine ⟨by rw [foRNuls_plain hC.2.1 hP hi, foRNuls_plain hW hN' hi], fun _ => ?_⟩
    obtain ⟨x', y', v, w, hx, hy, hv, hw, ho⟩ := hrow i hi
    simp only [chain, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hx hy
    subst hx hy
    simp only [Op.eval, ite_self, Except.ok.injEq] at hv
    simp only [chain, List.foldlM_cons, List.foldlM_nil, Op.eval, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hw
    subst hv hw
    rw [ho, if_neg (by decide : QAtomicType.i64 ≠ .u1)]

/-- **`Opt.shift s x` reads each long of `x` plus `s`, a null staying null**: where every owned long is in
`[0, 2^63 - s)` (so no word wraps), `y.get i` is `none` at a null of `x` and `x`'s long plus `s` else. -/
theorem Opt.shift_get {n : USize} {s : UInt64} {x y : Opt .i64 n} (h : Opt.shift s x = .ok y) (i : Fin n.toNat)
    (hv : ∀ v, x.get i = some v → 0 ≤ v.toInt ∧ v.toInt + s.toNat < 2 ^ 63) :
    (y.get i).map Int64.toInt = (x.get i).map fun v => v.toInt + (s.toNat : Int) := by
  unfold Opt.shift at h
  split at h
  · rename_i o ho
    have hy : y.enc = o := (congrArg Opt.enc (Except.ok.inj h)).symm
    obtain ⟨hf, hw⟩ := colMap_max_self x.wf ho i.1 i.2
    rw [← hy] at hf hw
    have hn : y.isNul i = x.isNul i := by
      have := (Opt.isNul_eq_false y i).trans ((by rw [hf] : _ ↔ _).trans (Opt.isNul_eq_false x i).symm)
      cases hx : x.isNul i <;> cases hy' : y.isNul i <;> simp_all
    cases hx : x.isNul i
    · have e1 := Opt.get_i64 x i hx
      have e2 := Opt.get_i64 y i (hn.trans hx)
      have hr := hw ((Opt.isNul_eq_false x i).1 hx)
      rw [e1] at hv ⊢; rw [e2, hr]
      obtain ⟨h0, hs⟩ := hv _ rfl
      simp only [Option.getD_some, Option.map_some, Option.some.injEq]
      rw [UInt64.add_comm s]; exact Int64.toInt_add_shift _ s h0 hs
    · rw [Opt.get_ne y i (by decide), Opt.get_ne x i (by decide), hn, hx]; rfl
  · cases h

/-- **Element `c` of `ColB.concat`** at either ownership: `Arr.concat_get`, or `Opt.concat_get` read through `getD`. -/
theorem ColB.concat_get {o : Bool} {t : QAtomicType} {n₁ n₂ n : USize} {x : ColB o t n₁} {y : ColB o t n₂} {z : ColB o t n}
    (hn : n.toNat = n₁.toNat + n₂.toNat) (h : ColB.concat n x y = .ok z) (c : Fin n.toNat) :
    ColB.get z c = if hc : c.1 < n₁.toNat then ColB.get x ⟨c.1, hc⟩ else ColB.get y ⟨c.1 - n₁.toNat, by omega⟩ := by
  cases o
  · exact Arr.concat_get hn h c
  · simp only [ColB.get, Opt.concat_get hn h c]; split <;> rfl

/-- **`ColB.shift s x` reads each long of `x` plus `s`** at a row of `P`, the rows `x` owns (`ColB.OwnedOn`: a null `Opt`
row reads `default`, no long), where that long is in `[0, 2^63 - s)`: `Arr.shift_get`, or `Opt.shift_get` through `getD`. -/
theorem ColB.shift_get {o : Bool} {n : USize} {s : UInt64} {x y : ColB o .i64 n} {P : Fin n.toNat → Prop}
    (h : ColB.shift s x = .ok y) (hx : ColB.OwnedOn x P) (i : Fin n.toNat) (hp : P i) (h0 : 0 ≤ (ColB.get x i).toInt)
    (hs : (ColB.get x i).toInt + s.toNat < 2 ^ 63) : (ColB.get y i).toInt = (ColB.get x i).toInt + s.toNat := by
  cases o
  · exact Arr.shift_get h i h0 hs
  · have hx' : ∀ i, (P i → Opt.get x i ≠ none) ∧ (¬P i → Opt.get x i = Opt.filler .i64) := hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 ((hx' i).1 hp)
    have := Opt.shift_get h i (fun v' hv' => by
      rw [hv] at hv'; cases hv'; simp only [ColB.get, hv, Option.getD_some] at h0 hs; exact ⟨h0, hs⟩)
    rw [hv] at this; simp only [Option.map_some] at this
    obtain ⟨w, hw⟩ := Option.map_eq_some_iff.1 this
    simp only [ColB.get, hv, hw.1, Option.getD_some] at h0 hs ⊢
    exact hw.2

/-- **`ColB.shift` keeps the owned rows**: `Opt.shift_get` maps a null to a null and a long to a long at every row,
the bound holding on `P` and a row off `P` being null. -/
theorem ColB.shift_owned {o : Bool} {n : USize} {s : UInt64} {x y : ColB o .i64 n} {P : Fin n.toNat → Prop}
    (h : ColB.shift s x = .ok y) (hx : ColB.OwnedOn x P)
    (hb : ∀ i, P i → 0 ≤ (ColB.get x i).toInt ∧ (ColB.get x i).toInt + s.toNat < 2 ^ 63) : ColB.OwnedOn y P := by
  cases o
  · trivial
  · have hx' : ∀ i, (P i → Opt.get x i ≠ none) ∧ (¬P i → Opt.get x i = none) := hx
    intro i
    have e := Opt.shift_get h i fun v hv => by
      have hp : P i := Classical.byContradiction fun hp => by rw [(hx' i).2 hp] at hv; cases hv
      have := hb i hp; simp only [ColB.get, hv, Option.getD_some] at this; exact this
    have hyx : Opt.get y i = none ↔ Opt.get x i = none := by
      cases hy : Opt.get y i <;> cases hz : Opt.get x i <;> rw [hy, hz] at e <;> simp at e ⊢
    exact ⟨fun hp hn => (hx' i).1 hp (hyx.1 hn), fun hp => hyx.2 ((hx' i).2 hp)⟩

/-- **`ColB.concat` owns the rows each side owns**, at their positions in the joined column (`Opt.concat_get`). -/
theorem ColB.concat_wf {o : Bool} {t : QAtomicType} {n₁ n₂ n : USize} {x : ColB o t n₁} {y : ColB o t n₂}
    {z : ColB o t n} (hn : n.toNat = n₁.toNat + n₂.toNat) (h : ColB.concat n x y = .ok z) {P₁ : Fin n₁.toNat → Prop}
    {P₂ : Fin n₂.toNat → Prop} (hx : ColB.OwnedOn x P₁) (hy : ColB.OwnedOn y P₂) :
    ColB.OwnedOn z fun c => if hc : c.1 < n₁.toNat then P₁ ⟨c.1, hc⟩ else P₂ ⟨c.1 - n₁.toNat, by omega⟩ := by
  cases o
  · trivial
  · have hx' : ∀ i, (P₁ i → Opt.get x i ≠ none) ∧ (¬P₁ i → Opt.get x i = Opt.filler t) := hx
    have hy' : ∀ i, (P₂ i → Opt.get y i ≠ none) ∧ (¬P₂ i → Opt.get y i = Opt.filler t) := hy
    intro c
    rw [Opt.concat_get hn h c]
    by_cases hc : c.1 < n₁.toNat
    · simp only [dif_pos hc]; exact hx' _
    · simp only [dif_neg hc]; exact hy' _

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
  obtain ⟨-, hns, ws', hcc, hcs⟩ := kscanCols_lock hs (Or.inl rfl) hc
  simp only [if_neg (by decide : Op.first ≠ Op.null), List.take_zero, List.map_nil, List.length_nil, List.drop_zero,
    List.nil_append] at hcs
  cases hcs
  obtain ⟨hl, hP⟩ := mapM_chain (es := [a]) hcc
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

/-- **A one-source `kscan .null` at no `seg` writes `chain post` of each null flag** (`kscan_first_chain` with `null`'s
first column the source's flags `foRNuls`): word `i` of the answer is `chain post` of row `i`'s flag. -/
theorem kscan_null_chain {s t : QAtomicType} {n : USize} {a : Enc} {post : List (Op × UInt64)} {r : Enc × Option UInt64}
    (hs : kscanStream .null [(n, a)] [] post = false) (h : kscan .null false s t n none [(n, a)] [] post = .ok r) :
    (raw .i64 n r.1).size = n.toNat ∧ ∀ i < n.toNat, ∃ w,
      chain post ((foRNuls n a)[i]?.getD 0) = .ok w ∧ (raw .i64 n r.1)[i]? = some (if t = .u1 then w % 2 else w) := by
  have hr := h
  unfold kscan at hr
  by_cases hd : kscanRefuses .null n [(n, a)] [] post = true
  · simp only [hd, ↓reduceIte] at hr; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure, segAll] at hr
  split at hr; · cases hr
  rename_i cs hc
  split at hr; · cases hr
  rename_i ca cs' ns
  obtain ⟨-, hns, ws', hcc, hcs⟩ := kscanCols_lock hs (Or.inl rfl) hc
  obtain ⟨hl, -⟩ := mapM_chain (es := [a]) hcc
  rcases ws' with _ | ⟨w0, _ | ⟨_, _⟩⟩ <;> try simp at hl
  simp only [if_pos rfl, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, List.drop_succ_cons, List.drop_zero, List.singleton_append, List.cons.injEq] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
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
  refine ⟨?_, fun i hi => ?_⟩
  · rw [(wordsFoR_closed _ hW.symm).2.1]; exact hW
  rw [(wordsFoR_closed _ hW.symm).2.1]
  have hr := hrow i (by omega)
  rw [if_neg (fun hh => by simp [hi] at hh)] at hr
  simp only [↓reduceIte, List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.nil_append, List.append_eq, List.map_id', List.map_id,
    List.map_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hr
  have hq := hpr i (by omega)
  refine ⟨out[i]?.getD 0, ?_, ?_⟩
  · rw [hr]; simpa [Array.getElem?_eq_getElem (show i < out₀.size by omega)] using hq
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

/-- **`readVals` establishes `Vals.WF`**: its `arr` case refuses unless `cellBad` finds no cell, which is the cell
clause; the payload is read by the same function. -/
theorem cellBad_none {n m : USize} {lo hi : Arr .i64 n} : cellBad m lo hi = none ↔ ∀ i : Fin n.toNat,
    0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
  simp [cellBad, List.find?_eq_none]

/-- `QValue.isDefault` tests for `default`. -/
theorem QValue.isDefault_eq {v : QValue} (h : QValue.isDefault v = true) : v = default := by
  unfold QValue.isDefault at h; split at h
  · rfl
  · cases h

/-- `Opt.fillerOk` tests for `Opt.filler`. -/
theorem Opt.fillerOk_eq {t : QAtomicType} {v : Option (El t)} (h : Opt.fillerOk t v = true) : v = Opt.filler t := by
  cases t
  case general =>
    cases v with
    | none => simp [Opt.fillerOk] at h
    | some w => exact congrArg some (QValue.isDefault_eq h)
  all_goals (cases v <;> simp_all [Opt.fillerOk, Opt.filler])

/-- **`ColB.ownedOk` decides `ColB.OwnedOn`** over the rows `Q` that `P` holds. -/
theorem ColB.ownedOk_on {o : Bool} {t : QAtomicType} {n : USize} (x : ColB o t n) {P : Fin n.toNat → Bool}
    {Q : Fin n.toNat → Prop} (hQ : ∀ i, Q i ↔ P i = true) (h : ColB.ownedOk x P = true) : ColB.OwnedOn x Q := by
  cases o
  · trivial
  · simp only [ColB.ownedOk, List.all_eq_true, List.mem_finRange, true_implies] at h
    intro i
    have hi := h i
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · rw [(hQ i).1 hq] at hi; simpa [Option.isSome_iff_ne_none] using hi
    · have hp : P i = false := by
        cases hp : P i
        · rfl
        · exact absurd ((hQ i).2 hp) hq
      rw [hp] at hi; simp only [Bool.false_eq_true, ↓reduceIte] at hi
      exact Opt.fillerOk_eq hi

/-- **`ValsB.cellsOkOn` decides `ValsB.WFOn`** over the rows `Q` that `P` holds, in the direction a literal needs. -/
theorem ValsB.cellsOkOn_wf : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → {P : Fin n.toNat → Bool} →
    {Q : Fin n.toNat → Prop} → (∀ i, Q i ↔ P i = true) → ValsB.cellsOkOn x P = true → ValsB.WFOn x Q
  | _, .atom _, _, x, _, _, hQ, h => ColB.ownedOk_on x hQ h
  | _, .one, _, _, _, _, _, _ => trivial
  | _, .prod _ _, _, x, _, _, hQ, h => by
    simp only [ValsB.cellsOkOn, Bool.and_eq_true] at h
    exact ⟨ValsB.cellsOkOn_wf x.1 hQ h.1, ValsB.cellsOkOn_wf x.2 hQ h.2⟩
  | _, .arr _, _, ⟨m, lo, hi, f⟩, P, Q, hQ, h => by
    simp only [ValsB.cellsOkOn, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨hl, hh⟩, hc⟩, hf⟩ := h
    exact ⟨ColB.ownedOk_on lo hQ hl, ColB.ownedOk_on hi hQ hh,
      fun i hq => (hc i).resolve_left (by simp [(hQ i).1 hq]),
      ValsB.cellsOkOn_wf f (fun _ => iff_of_true trivial rfl) hf⟩
  | _, .sum _ _, _, s, P, Q, hQ, h => by
    simp only [ValsB.cellsOkOn] at h; simp only [ValsB.WFOn]
    cases hv : s.view with
    | opt hb x =>
      simp only [hv, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        Option.isNone_iff_eq_none] at h
      exact fun i hq => (h i).resolve_left (by rwa [hQ i] at hq)
    | gen hb tag x y =>
      simp only [hv, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        Bool.not_eq_true'] at h
      obtain ⟨⟨ht, hx⟩, hy⟩ := h
      exact ⟨fun i hq => (ht i).resolve_left (by rwa [hQ i] at hq),
        ValsB.cellsOkOn_wf x (fun i => by rw [hQ i]; simp) hx, ValsB.cellsOkOn_wf y (fun i => by rw [hQ i]; simp) hy⟩

/-- **`ValsB.cellsOk` decides `Vals.WF`** in the direction a literal needs. -/
theorem Vals.cellsOk_wf {A : Obj} {n : USize} {x : Vals A n} (h : ValsB.cellsOk x = true) : Vals.WF x :=
  ValsB.cellsOkOn_wf x (fun _ => iff_of_true trivial rfl) h

/-- **`Vals.nub` keeps `Vals.WF`**: its rows are `ValsB.gather`ed from `x`. -/
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

/-- **Row `c` of `ValsB.concat`** is row `c` of `x` below `n₁`, row `c - n₁` of `y` from there, at a row the side it
comes from owns (`P₁` of `x`, `P₂` of `y`): an `arr` row reads `lo`, `hi` through the shift, which holds on owned rows. -/
theorem ValsB.concat_row : {o : Bool} → {A : Obj} → {n₁ n₂ n : USize} → (hn : n.toNat = n₁.toNat + n₂.toNat) →
    (x : ValsB o A n₁) → (y : ValsB o A n₂) → {z : ValsB o A n} → ValsB.concat n x y = .ok z →
    {P₁ : Fin n₁.toNat → Prop} → {P₂ : Fin n₂.toNat → Prop} → ValsB.WFOn x P₁ → ValsB.WFOn y P₂ →
      ∀ c : Fin n.toNat, (if hc : c.1 < n₁.toNat then P₁ ⟨c.1, hc⟩ else P₂ ⟨c.1 - n₁.toNat, by omega⟩) →
        ValsB.row z c =
          if hc : c.1 < n₁.toNat then ValsB.row x ⟨c.1, hc⟩ else ValsB.row y ⟨c.1 - n₁.toNat, by omega⟩
  | _, .atom _, _, _, _, hn, _, _, _, h, _, _, _, _, c, _ => ColB.concat_get hn h c
  | _, .prod _ _, _, _, _, hn, x, y, _, h, _, _, hx, hy, c, hP => by
    simp only [ValsB.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    show (ValsB.row z1 c, ValsB.row z2 c) = _
    rw [ValsB.concat_row hn x.1 y.1 h1 hx.1 hy.1 c hP, ValsB.concat_row hn x.2 y.2 h2 hx.2 hy.2 c hP]
    split <;> rfl
  | _, .arr _, n₁, n₂, _, hn, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, _, h, _, P₂, hx, hy, c, hP => by
    simp only [ValsB.concat] at h
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
    obtain ⟨hl₁, hh₁, hb₁, hf₁⟩ := hx
    obtain ⟨hl₂, hh₂, hb₂, hf₂⟩ := hy
    have hpn := catRows_ok hp
    have hrow := fun j => ValsB.concat_row hpn f₁ f₂ hF hf₁ hf₂ j (by split <;> trivial)
    have hU : ∀ m : USize, m.toUInt64.toNat = m.toNat := fun m => by
      have := m.toNat_lt_size; have := USize.size_le; simp
    have gl := ColB.concat_get hn hlo c
    have gh := ColB.concat_get hn hhi c
    simp only [ValsB.row]
    rw [filterMap_finRange_add hpn]
    split
    · rename_i hc
      have := hb₁ ⟨c.1, hc⟩ (by simpa only [dif_pos hc] using hP)
      rw [dif_pos hc] at gl gh
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₂.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gh]; dsimp only; omega, List.append_nil]
      congr 1; funext j
      rw [hrow, dif_pos j.2, gl, gh]
    · rename_i hc
      have hc' : c.1 - n₁.toNat < n₂.toNat := by omega
      have hp₂ : P₂ ⟨_, hc'⟩ := by simpa only [dif_neg hc] using hP
      have := hb₂ _ hp₂
      have l2 := ColB.shift_get hL₂ hl₂ ⟨_, hc'⟩ hp₂ (by omega) (by rw [hU]; omega)
      have h2 := ColB.shift_get hH₂ hh₂ ⟨_, hc'⟩ hp₂ (by omega) (by rw [hU]; omega)
      rw [dif_neg hc] at gl gh
      rw [hU] at l2 h2
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₁.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gl, l2]; have := j.2; dsimp only; omega,
        List.nil_append]
      congr 1; funext j
      rw [hrow, dif_neg (by dsimp only; omega), gl, gh, l2, h2]
      have hj : (⟨m₁.toNat + j.1 - m₁.toNat, by omega⟩ : Fin m₂.toNat) = j := Fin.ext (by simp)
      rw [hj]
      by_cases hA : (ColB.get lo₂ ⟨_, hc'⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (ColB.get hi₂ ⟨_, hc'⟩).toInt
      · rw [if_pos hA, if_pos (by dsimp only; omega)]
      · rw [if_neg hA, if_neg (by dsimp only; omega)]
  | _, .sum _ _, n₁, _, _, hn, s₁, s₂, _, h, _, _, hx, hy, c, hP => by
    simp only [ValsB.concat] at h
    rcases hs₁ : s₁.view with ⟨hb₁, x₁⟩ | ⟨hb₁, tag₁, x₁, y₁⟩ <;>
      rcases hs₂ : s₂.view with ⟨hb₂, x₂⟩ | ⟨hb₂, tag₂, x₂, y₂⟩ <;> simp only [hs₁, hs₂] at h
    · obtain rfl := Option.some.inj (hb₂.symm.trans hb₁)
      simp only [Functor.map, Except.map] at h
      split at h; · cases h
      rename_i w hw
      cases h
      simp only [ValsB.row, hs₁, hs₂, ValsB.view_ofOpt, Opt.concat_get hn hw c]
      split <;> rfl
    · exact absurd (hb₁.symm.trans hb₂) nofun
    · exact absurd (hb₂.symm.trans hb₁) nofun
    simp only [ValsB.WFOn, hs₁, hs₂] at hx hy
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i tag htag
    split at h; · cases h
    rename_i X hX
    split at h; · cases h
    rename_i Y hY
    cases h
    obtain ⟨-, hx₁, hy₁⟩ := hx
    obtain ⟨-, hx₂, hy₂⟩ := hy
    have gt := Arr.concat_get hn htag c
    have ex := ValsB.concat_row hn x₁ x₂ hX hx₁ hx₂ c
    have ey := ValsB.concat_row hn y₁ y₂ hY hy₁ hy₂ c
    by_cases hc : c.1 < n₁.toNat
    · simp only [dif_pos hc] at gt ex ey hP
      cases ht : tag₁.get ⟨c.1, hc⟩
      · simp only [ValsB.row, ValsB.view_ofGen, hs₁, dif_pos hc, gt, ht, ex ⟨hP, ht⟩, Bool.false_eq_true, if_false]
      · simp only [ValsB.row, ValsB.view_ofGen, hs₁, dif_pos hc, gt, ht, ey ⟨hP, ht⟩, if_true]
    · simp only [dif_neg hc] at gt ex ey hP
      cases ht : tag₂.get ⟨c.1 - n₁.toNat, by omega⟩
      · simp only [ValsB.row, ValsB.view_ofGen, hs₂, dif_neg hc, gt, ht, ex ⟨hP, ht⟩, Bool.false_eq_true, if_false]
      · simp only [ValsB.row, ValsB.view_ofGen, hs₂, dif_neg hc, gt, ht, ey ⟨hP, ht⟩, if_true]
  | _, .one, _, _, _, _, _, _, _, _, _, _, _, _, c, _ => by split <;> rfl

/-- **`ValsB.concat` owns the rows each side owns**, at their positions in the joined side: a cell of `x` stays inside
the first `m₁` payload rows, one of `y` moves past them by `m₁`, inside the `m₁ + m₂` rows of the joined payload. -/
theorem ValsB.concat_wf : {o : Bool} → {A : Obj} → {n₁ n₂ n : USize} → (hn : n.toNat = n₁.toNat + n₂.toNat) →
    {x : ValsB o A n₁} → {y : ValsB o A n₂} → {z : ValsB o A n} → ValsB.concat n x y = .ok z →
    {P₁ : Fin n₁.toNat → Prop} → {P₂ : Fin n₂.toNat → Prop} → ValsB.WFOn x P₁ → ValsB.WFOn y P₂ →
      ValsB.WFOn z fun c => if hc : c.1 < n₁.toNat then P₁ ⟨c.1, hc⟩ else P₂ ⟨c.1 - n₁.toNat, by omega⟩
  | _, .atom _, _, _, _, hn, _, _, _, h, _, _, hx, hy => ColB.concat_wf hn h hx hy
  | _, .one, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .prod _ _, _, _, _, hn, _, _, _, h, _, _, hx, hy => by
    simp only [ValsB.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    exact ⟨ValsB.concat_wf hn h1 hx.1 hy.1, ValsB.concat_wf hn h2 hx.2 hy.2⟩
  | _, .arr _, n₁, n₂, _, hn, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, _, h, _, P₂, hx, hy => by
    simp only [ValsB.concat] at h
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
    obtain ⟨hl₁, hh₁, hb₁, hf₁⟩ := hx
    obtain ⟨hl₂, hh₂, hb₂, hf₂⟩ := hy
    have hpn := catRows_ok hp
    have hU : ∀ m : USize, m.toUInt64.toNat = m.toNat := fun m => by
      have := m.toNat_lt_size; have := USize.size_le; simp
    refine ⟨ColB.concat_wf hn hlo hl₁ (ColB.shift_owned hL₂ hl₂ fun i hp => ?_),
      ColB.concat_wf hn hhi hh₁ (ColB.shift_owned hH₂ hh₂ fun i hp => ?_), fun c hP => ?_,
      (ValsB.WFOn_congr _ fun _ => ⟨fun _ => trivial, fun _ => by split <;> trivial⟩).1
        (ValsB.concat_wf hpn hF hf₁ hf₂)⟩
    · have := hb₂ i hp; exact ⟨by omega, by rw [hU]; omega⟩
    · have := hb₂ i hp; exact ⟨by omega, by rw [hU]; omega⟩
    rw [ColB.concat_get hn hlo c, ColB.concat_get hn hhi c]
    split
    · rename_i hc
      have := hb₁ ⟨c.1, hc⟩ (by simpa only [dif_pos hc] using hP)
      omega
    · rename_i hc
      have hc' : c.1 - n₁.toNat < n₂.toNat := by omega
      have hp₂ : P₂ ⟨_, hc'⟩ := by simpa only [dif_neg hc] using hP
      have := hb₂ _ hp₂
      have l2 := ColB.shift_get hL₂ hl₂ ⟨_, hc'⟩ hp₂ (by omega) (by rw [hU]; omega)
      have h2 := ColB.shift_get hH₂ hh₂ ⟨_, hc'⟩ hp₂ (by omega) (by rw [hU]; omega)
      rw [hU] at l2 h2
      rw [l2, h2]; omega
  | _, .sum _ _, n₁, n₂, n, hn, s₁, s₂, _, h, P₁, P₂, hx, hy => by
    simp only [ValsB.concat] at h
    rcases hv₁ : s₁.view with ⟨hb₁, x₁⟩ | ⟨hb₁, tag₁, x₁, y₁⟩ <;>
      rcases hv₂ : s₂.view with ⟨hb₂, x₂⟩ | ⟨hb₂, tag₂, x₂, y₂⟩ <;> simp only [hv₁, hv₂] at h
    · obtain rfl := Option.some.inj (hb₂.symm.trans hb₁)
      simp only [ValsB.WFOn, hv₁, hv₂] at hx hy
      simp only [Functor.map, Except.map] at h
      split at h; · cases h
      rename_i w hw
      cases h; simp only [ValsB.WFOn, ValsB.view_ofOpt]
      intro c hc
      rw [Opt.concat_get hn hw c]
      by_cases h1 : c.1 < n₁.toNat
      · simp only [dif_pos h1] at hc ⊢; exact hx _ hc
      · simp only [dif_neg h1] at hc ⊢; exact hy _ hc
    · exact absurd (hb₁.symm.trans hb₂) nofun
    · exact absurd (hb₂.symm.trans hb₁) nofun
    simp only [ValsB.WFOn, hv₁, hv₂] at hx hy
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i tag htag
    split at h; · cases h
    rename_i X hX
    split at h; · cases h
    rename_i Y hY
    cases h
    simp only [ValsB.WFOn, ValsB.view_ofGen]
    obtain ⟨ht₁, hx₁, hy₁⟩ := hx
    obtain ⟨ht₂, hx₂, hy₂⟩ := hy
    -- a summand of the join owns a row where its side does and the joined tag names it (`Arr.concat_get`)
    have key : ∀ (k : Bool) (i : Fin n.toNat), ((if hc : i.1 < n₁.toNat then P₁ ⟨i.1, hc⟩ ∧ tag₁.get ⟨i.1, hc⟩ = k
        else P₂ ⟨i.1 - n₁.toNat, by omega⟩ ∧ tag₂.get ⟨i.1 - n₁.toNat, by omega⟩ = k) ↔
        (if hc : i.1 < n₁.toNat then P₁ ⟨i.1, hc⟩ else P₂ ⟨i.1 - n₁.toNat, by omega⟩) ∧ tag.get i = k) :=
      fun k i => by
        rw [Arr.concat_get hn htag i]
        by_cases hc : i.1 < n₁.toNat
        · simp only [dif_pos hc]
        · simp only [dif_neg hc]
    refine ⟨fun i hi => ?_, (ValsB.WFOn_congr X (key false)).1 (ValsB.concat_wf hn hX hx₁ hx₂),
      (ValsB.WFOn_congr Y (key true)).1 (ValsB.concat_wf hn hY hy₁ hy₂)⟩
    rw [Arr.concat_get hn htag i]
    by_cases hc : i.1 < n₁.toNat
    · simp only [dif_pos hc] at hi ⊢; exact ht₁ _ hi
    · simp only [dif_neg hc] at hi ⊢; exact ht₂ _ hi

/-- **Row `c` of `ValsB.concat`** of two sides owning every row (`Vals.WF`): `ValsB.concat_row` at `P = True`. -/
theorem Vals.concat_row {A : Obj} {n₁ n₂ n : USize} (hn : n.toNat = n₁.toNat + n₂.toNat) (x : Vals A n₁)
    (y : Vals A n₂) {z : Vals A n} (h : ValsB.concat n x y = .ok z) (hx : Vals.WF x) (hy : Vals.WF y)
    (c : Fin n.toNat) : ValsB.row z c =
      if hc : c.1 < n₁.toNat then ValsB.row x ⟨c.1, hc⟩ else ValsB.row y ⟨c.1 - n₁.toNat, by omega⟩ :=
  ValsB.concat_row hn x y h hx hy c (by split <;> trivial)

/-- **`ValsB.concat` keeps `Vals.WF`**: `ValsB.concat_wf` at `P = True`. -/
theorem Vals.concat_wf {A : Obj} {n₁ n₂ n : USize} (hn : n.toNat = n₁.toNat + n₂.toNat) {x : Vals A n₁}
    {y : Vals A n₂} {z : Vals A n} (h : ValsB.concat n x y = .ok z) (hx : Vals.WF x) (hy : Vals.WF y) : Vals.WF z :=
  (ValsB.WFOn_congr z fun _ => ⟨fun _ => trivial, fun _ => by split <;> trivial⟩).1 (ValsB.concat_wf hn h hx hy)

/-! ## Checks: CONCAT keeps every stored word -/


end Rel
