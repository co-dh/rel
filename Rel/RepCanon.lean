module

public import Rel.Run.Canon
public import Rel.KernelSpec.KSeen

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of `Vals.nub`, `Tab.canon`, `Tab.ran` and `Tab.dom` (`Rel/Run/Canon.lean`), from the five kernels' laws:
`asc_perm` (the sorted columns are the input's through a permutation), `kseen_ok` with `firsts_spec` (the first row of
each group, and every row's group), `raw_kgather` (a gathered word is the source's word at the index) and the closure
law `wordsFoR_closed` (a kernel's answer reads back as the words it wrote). `Arr.get_eq_of_raw` carries a word law to
the elements, and `ValsB.gather_row` to the rows. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **An element is the atom of its word**: in a column every kernel reads (`foR`, or `pos` at `i64`), element `i` is
`Carrier.of?` of the atom its raw word `a` reads as (`atomOfBits`), and at `u1` that word is below `2`. Stated on the
payload `e` at a row `foRNuls` flags as no null, so it serves `Arr` (no null anywhere) and `Opt` (off its nulls). -/
theorem Enc.get_raw_atom {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e)
    (hg : t ≠ .general) (i : Fin n.toNat) (h0 : (foRNuls n e)[i.1]? = some 0) :
    ∃ a, (Enc.raw .i64 n e)[i.1]? = some a ∧ (t = .u1 → a < 2) ∧
      ((Enc.get t n e i).bind fun a => (Dep.Carrier.of? t (.atom a) : Option (El t))).getD default =
        (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg)) : Option (El t)).getD default := by
  cases e with
  | foR md pk =>
    have hnul : Column.foRNul md pk (Column.blockStarts md) i = false := by simpa [foRNuls, i.2] using h0
    refine ⟨Column.foRBits md pk (Column.blockStarts md) i, by simp only [raw_foR .i64 8 rfl
      (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map, Array.getElem?_range, i.2, if_true, Option.map_some,
      Nat.reduceMul, ofNat_toNat_mod64], fun hu => by
        subst hu; simp only [Enc.WF] at hw
        exact UInt64.lt_iff_toNat_lt.2 (hw.2.1 trivial i i.2 _ (by simp [Column.foROpt, hnul])), ?_⟩
    cases t <;> first | exact absurd rfl hg |
      simp only [Enc.get, if_pos i.2, QAtomicType.width, foRBits_starts, Option.bind_some]
  | pos =>
    cases t <;> simp only [Enc.WF] at hw
    exact ⟨UInt64.ofNat i.1, by simp [Enc.raw, i.2], fun h => absurd h (by decide),
      by simp [Enc.get, i.2, Column.atomOfBits]⟩
  | _ => all_goals cases t <;> first | exact absurd rfl hg | simp only [Enc.WF] at hw

/-- `Enc.get_raw_atom` at an `Arr`, whose every row is no null (`foRNuls_plain`). -/
theorem Arr.get_raw_atom {t : QAtomicType} {n : USize} (x : Arr t n)
    (hg : t ≠ .general) (i : Fin n.toNat) : ∃ a, (Enc.raw .i64 n x.enc)[i.1]? = some a ∧ (t = .u1 → a < 2) ∧
      x.get i = (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default := by
  rw [Arr.get_ne x i hg]; exact Enc.get_raw_atom x.wf hg i (foRNuls_plain x.wf x.plain i.2)

/-- `Obj.optOf` undoes `Obj.optEl`: a band row read as `a + b` and back is the row. -/
theorem Obj.optOf_optEl {a b : Obj} {t : QAtomicType} (h : Obj.band a b = some t) (v : Option (El t)) :
    Obj.optOf h (Obj.optEl h v) = v := by
  obtain ⟨rfl, rfl⟩ := Obj.band_some h
  unfold Obj.optOf Obj.optEl; generalize Obj.band_some h = p; obtain ⟨p1, p2⟩ := p; cases v <;> rfl

/-- `Opt.get` at an atom type: `none` at a null, else `Arr.get`'s reading of the payload. -/
theorem Opt.get_ne {t : QAtomicType} {n : USize} (x : Opt t n) (i : Fin n.toNat) (h : t ≠ .general) :
    x.get i = if x.isNul i then none else
      some (((Enc.get t n x.enc i).bind fun a => Dep.Carrier.of? t (.atom a)).getD default) := by
  cases t <;> first | exact absurd rfl h | rfl

/-- **`Opt.isNul` is the flag `foRNuls` moves**: row `i` is no null exactly where its flag word is `0`; `isNul`'s `#[]`
and the kernels' `blockStarts` are one decode (`blockStarts_get`), as in `foRBits_starts`. -/
theorem Opt.isNul_eq_false {t : QAtomicType} {n : USize} (x : Opt t n) (i : Fin n.toNat) :
    x.isNul i = false ↔ (foRNuls n x.enc)[i.1]? = some 0 := by
  have hw := x.wf
  unfold Opt.isNul
  cases hc : x.enc with
  | foR md pk =>
    rw [hc] at hw; simp only [Enc.WF] at hw
    have hb : i.1 / Column.blk md ≤ Column.nblk md :=
      Nat.le_of_lt (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le i.2 hw.2.2.1))
    have hs : Column.foRNul md pk #[] i = Column.foRNul md pk (Column.blockStarts md) i := by
      unfold Column.foRNul; simp [Verify.blockStarts_get md hb, Verify.blockStarts_get md (Nat.le_refl _)]
    simp only [hs, foRNuls, Array.getElem?_map, Array.getElem?_range, i.2, if_true, Option.map_some]
    cases Column.foRNul md pk (Column.blockStarts md) i <;> simp
  | _ => simp [foRNuls, i.2]

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
  obtain ⟨a, ha, hua, ex⟩ := Arr.get_raw_atom x hg i
  obtain ⟨b, hb, hub, ey⟩ := Arr.get_raw_atom y hg j
  rw [ex, ey, h hg a b ha hb fun hu => ⟨hua hu, hub hu⟩]

/-- A column with no null read as nullable (`Opt.ofArr`) holds `some` of its element at every row. -/
theorem Opt.get_ofArr {t : QAtomicType} {n : USize} (x : Arr t n) (i : Fin n.toNat) :
    (Opt.ofArr x).get i = some (x.get i) := by
  have hn : (Opt.ofArr x).isNul i = false := (Opt.isNul_eq_false _ i).2 (foRNuls_plain x.wf x.plain i.2)
  by_cases hg : t = .general
  · subst hg; simp only [Opt.get, hn, Bool.false_eq_true, if_false]; rfl
  · rw [Opt.get_ne _ i hg, hn, Arr.get_ne x i hg]; rfl

/-- **`Arr.get_eq_of_raw` with nulls**: two `Opt`s whose rows `i`, `j` carry one null flag (`foRNuls`) and, off a null,
words that read as one atom hold one element there, `none` at a null. -/
theorem Opt.get_eq_of_raw {t : QAtomicType} {n m : USize} (x : Opt t n) (y : Opt t m) (hx : Kernel.Enc.Valid n x.enc)
    (hy : Kernel.Enc.Valid m y.enc) (i : Fin n.toNat) (j : Fin m.toNat)
    (hf : (foRNuls n x.enc)[i.1]? = (foRNuls m y.enc)[j.1]?)
    (h : (foRNuls n x.enc)[i.1]? = some 0 → ∀ (hg : t ≠ .general) a b, (Enc.raw .i64 n x.enc)[i.1]? = some a →
      (Enc.raw .i64 m y.enc)[j.1]? = some b → (t = .u1 → a < 2 ∧ b < 2) →
        Column.atomOfBits t a hg = Column.atomOfBits t b hg) : x.get i = y.get j := by
  have hg : t ≠ .general := by
    rintro rfl; have hw := x.wf
    cases hc : x.enc <;> (rw [hc] at hw hx; simp only [Enc.WF, Kernel.Enc.Valid] at hw hx) <;> exact absurd hw.1 (by decide)
  rw [Opt.get_ne x i hg, Opt.get_ne y j hg]
  by_cases h0 : (foRNuls n x.enc)[i.1]? = some 0
  · rw [(Opt.isNul_eq_false x i).2 h0, (Opt.isNul_eq_false y j).2 (hf ▸ h0)]
    obtain ⟨a, ha, hua, ex⟩ := Enc.get_raw_atom x.wf hg i h0
    obtain ⟨b, hb, hub, ey⟩ := Enc.get_raw_atom y.wf hg j (hf ▸ h0)
    simp only [Bool.false_eq_true, if_false, ex, ey, h h0 hg a b ha hb fun hu => ⟨hua hu, hub hu⟩]
  · have h1 : x.isNul i = true := by
      cases hh : x.isNul i; · exact absurd ((Opt.isNul_eq_false x i).1 hh) h0
      rfl
    have h2 : y.isNul j = true := by
      cases hh : y.isNul j; · exact absurd (hf.trans ((Opt.isNul_eq_false y j).1 hh)) h0
      rfl
    simp only [h1, h2, if_true]

section
open Ext.Enc

/-- **`kscatter` under any `op`, on words**: the answer reads back as `scatterWords` of its arguments' words where `e`
holds no null; a null row's raw word is its block's top residual, not the word scattered there. -/
theorem kscatter_words {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64} (h : kscatter op m ix e n fill = .ok o)
    (hne : hasNul e = false) :
    (raw .i64 m ix).size = m.toNat ∧ (raw .i64 m e).size = m.toNat ∧
      scatterWords op (raw .i64 m ix) (raw .i64 m e) n.toNat fill = .ok (raw .i64 n o) := by
  unfold kscatter at h
  split at h; · cases h
  cases hi : foRWords "scatter: ix" m ix with
  | error s => simp [hi, bind, Except.bind] at h
  | ok is' =>
    cases he : foRWords "scatter: e" m e with
    | error s => simp [hi, he, bind, Except.bind] at h
    | ok es' =>
      obtain ⟨rfl, hisz⟩ := foRWords_raw _ _ _ _ hi
      obtain ⟨rfl, hesz⟩ := foRWords_raw _ _ _ _ he
      simp only [hi, he, hne, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure] at h
      cases hw : scatterWords op (raw .i64 m ix) (raw .i64 m e) n.toNat fill with
      | error s => exfalso; revert h; rw [hw]; split <;> (try split) <;> (try split) <;> simp_all
      | ok ws =>
        have h8 : USize.ofNat32 8 (by decide) = 8 := USize.toNat_inj.mp (by simp)
        have hs := scatterWords_size hw
        -- the `noNul` checks and the op's guard only fail; past them the answer is the words' encoding
        have ho : o = .foR (Coc.encode 8 (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)).1
            (Coc.encode 8 (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)).2 := by
          revert h; rw [hw, h8]; split <;> (try split) <;> (try split) <;> simp_all
        obtain ⟨hxs, -, hxg⟩ := foldl_pushBits (fun v => v) 8 (by decide) ws.toList ByteArray.empty
        rw [Array.foldl_toList] at hxs hxg
        simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
        refine ⟨hisz, hesz, congrArg Except.ok ?_⟩
        have h88 : (8 : USize) = (8 : Nat).toUSize := rfl
        rw [ho, Coc.encode, h88, raw_encodeAt .i64 8 rfl (by decide) Column.lgEnc (by decide) _ n (by rw [hxs]; omega)]
        refine (Array.ext (by simp [hs]) fun i h1 _ => ?_).symm
        simp only [Array.getElem_map, Array.getElem_range]
        rw [Nat.mul_comm, hxg i (by simp at h1; omega), ofNat_toNat_mod64, Array.getElem_toList]

/-- **`colConst n w` is `n` words `w`.** -/
theorem colConst_raw {n : USize} {w : UInt64} {e : Enc} (h : colConst n w = .ok e) :
    raw .i64 n e = Array.replicate n.toNat w := by
  obtain ⟨-, -, hw⟩ := kscatter_words h rfl
  have h0 : (raw .i64 0 (.pos : Enc)).size = 0 := by simp [raw]
  unfold scatterWords at hw
  rw [h0] at hw
  exact (Except.ok.inj hw).symm

/-- **`colConst n w` read as booleans is `n` words `w % 2`** (`kscan`'s `seg`). -/
theorem colConst_u1 {n : USize} {w : UInt64} {e : Enc} (h : colConst n w = .ok e) :
    ∀ i < n.toNat, (raw .u1 n e)[i]?.getD 0 = UInt64.ofNat (w.toNat % 2) := by
  intro i hi
  obtain ⟨hfo, -⟩ := raw_scatter 0 .pos .pos n w e rfl h
  have he := colConst_raw h
  generalize Coc.encode _ _ = q at hfo; subst hfo
  have hu : raw .u1 n (.foR q.1 q.2 : Enc) = (raw .i64 n (.foR q.1 q.2 : Enc)).map fun w => UInt64.ofNat (w.toNat % 2) := by
    simp only [raw, QAtomicType.width, Array.map_map]
    refine Array.ext (by simp) fun j _ _ => ?_
    simp
  rw [hu, Array.getElem?_map, he, Array.getElem?_replicate, if_pos hi]; rfl
/-- **`colMap op n a b t s pre post` at any answer type `t`**: both arguments hold `n` words read at `s`, and word `i`
of the answer is `chain post` of `op` of `a`'s and `b`'s words `i` through `chain pre`, a boolean answer's cut to its
bit. -/
theorem colMap_chain {op : Op} {t s : QAtomicType} {n : USize} {a b o : Enc} {pre post : List (Op × UInt64)}
    (h : colMap op n a b t s pre post = .ok o)
    (hs : kscanStream op [(n, a), (n, b)] pre post = false := by lockstep) (hn : op ≠ .null := by decide)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by nulfree) :
    (raw s n a).size = n.toNat ∧ (raw s n b).size = n.toNat ∧ (raw .i64 n o).size = n.toNat ∧ ∀ i < n.toNat,
      ∃ x y v w, chain pre ((raw s n a)[i]?.getD 0) = .ok x ∧ chain pre ((raw s n b)[i]?.getD 0) = .ok y ∧
        op.eval x y = .ok v ∧ chain post v = .ok w ∧ (raw .i64 n o)[i]? = some (if t = .u1 then w % 2 else w) := by
  unfold colMap at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  unfold kscan at hr
  by_cases hd : kscanRefuses op n [(n, a), (n, b)] pre post = true
  · simp only [hd, ↓reduceIte] at hr; simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
  simp only [hd, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure, segAll] at hr
  split at hr; · cases hr
  rename_i cs hc
  split at hr; · cases hr
  rename_i ca cs' ns
  obtain ⟨-, hns, ws', hcc, hcs⟩ := kscanCols_lock hs hF hc
  rw [if_neg hn] at hcs; simp only [List.take_zero, List.map_nil, List.length_nil, List.drop_zero, List.nil_append] at hcs
  cases hcs
  obtain ⟨hl, hP⟩ := mapM_chain (es := [a, b]) hcc
  rcases cs' with _ | ⟨cb, _ | ⟨_, _⟩⟩ <;> simp at hl
  obtain ⟨ha, -, hra⟩ := hP (a, ca) (by simp)
  obtain ⟨hb, -, hrb⟩ := hP (b, cb) (by simp)
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
  refine ⟨ha, hb, ?_, fun i hi => ?_⟩
  · rw [(wordsFoR_closed _ hW.symm).2.1]; exact hW
  rw [(wordsFoR_closed _ hW.symm).2.1]
  have hr := hrow i (by omega)
  rw [if_neg (fun hh => by simp [hi] at hh)] at hr
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind,
    Except.bind] at hr
  cases he : op.eval (ca[i]?.getD 0) (cb[i]?.getD 0) with
  | error e => rw [he] at hr; cases hr
  | ok v =>
    rw [he] at hr; simp only [pure, Except.pure, Except.ok.injEq] at hr
    have hq := hpr i (by omega)
    refine ⟨_, _, v, _, hra i hi, hrb i hi, he,
      by rw [hr]; simpa [Array.getElem?_eq_getElem (show i < out₀.size by omega)] using hq, ?_⟩
    simp [Array.getElem?_eq_getElem (show i < out.size by omega)]

/-- **`colMap op n a b t` at any answer type `t`**: word `i` is `op` of `a`'s and `b`'s words `i`, a boolean answer's
cut to its bit (`colMap_chain` at no chain; `colMap_raw` is the `i64` case with the argument sizes). -/
theorem colMap_get {op : Op} {t : QAtomicType} {n : USize} {a b o : Enc}
    (h : colMap op n a b t = .ok o) (hs : kscanStream op [(n, a), (n, b)] [] [] = false := by lockstep)
    (hn : op ≠ .null := by decide)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by nulfree) :
    (raw .i64 n o).size = n.toNat ∧ ∀ i < n.toNat, ∃ v,
      op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) = .ok v ∧
      (raw .i64 n o)[i]? = some (if t = .u1 then v % 2 else v) := by
  obtain ⟨-, -, hso, hr⟩ := colMap_chain h hs hn hF
  refine ⟨hso, fun i hi => ?_⟩
  obtain ⟨x, y, v, w, hx, hy, hv, hw, ho⟩ := hr i hi
  cases hx; cases hy; cases hw
  exact ⟨v, hv, ho⟩


/-- An `i64` element is its raw word read as an `Int64`, at every encoding `Enc.WF` admits. -/
theorem Arr.get_i64 {n : USize} (x : Arr .i64 n) (i : Fin n.toNat) :
    x.get i = ((Enc.raw .i64 n x.enc)[i.1]?.getD 0).toInt64 := by
  have hw := x.wf
  rw [Arr.get_ne x i (by decide)]
  cases hc : x.enc <;> rw [hc] at hw <;>
    simp_all [Enc.WF, Enc.get, Enc.raw, QAtomicType.width, Column.atomOfBits, Dep.Carrier.of?,
      foRBits_starts]

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
theorem Arr.get_u1 {n : USize} (x : Arr .u1 n) (i : Fin n.toNat) :
    ∃ a, (Enc.raw .i64 n x.enc)[i.1]? = some a ∧ a = (if x.get i then 1 else 0) := by
  obtain ⟨a, ha, hu, e⟩ := Arr.get_raw_atom x (by decide) i
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
    obtain ⟨his, hes, hlt, -⟩ := raw_kgather m ix n _ o ho
    have ho' := kgather_plain ho x.plain
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

/-- A flag word of `foRNuls` is `0` or `1`. -/
theorem foRNuls_bit (m : USize) (e : Enc) {i : Nat} (hi : i < m.toNat) :
    (foRNuls m e)[i]? = some (if (foRNuls m e)[i]?.getD 0 != 0 then 1 else 0) := by
  cases e <;> simp only [foRNuls, Array.getElem?_map, Array.getElem?_range, Array.getElem?_replicate, hi, if_true,
    Option.map_some, Option.getD_some] <;> (try split) <;> simp_all

/-- A kernel's answer reads back its word at each row its null bitmap leaves unflagged; a flagged row's raw word is
its block's top residual, not `ws[k]`. -/
theorem raw_wordsFoR_of_bit (ws : Array UInt64) (nul : ByteArray) {m : USize} (hws : ws.size = m.toNat) (k : Nat)
    (hk : k < ws.size) (hnk : Column.bitAt nul k = false) : (Enc.raw .i64 m (wordsFoR ws nul))[k]? = some ws[k] := by
  obtain ⟨md, pk, hE⟩ : ∃ md pk, wordsFoR ws nul = .foR md pk := ⟨_, _, rfl⟩
  have h := (wordsFoR_nul ws nul hws.symm).2.2.1 md pk hE k hk
  rw [hnk, if_neg Bool.false_ne_true] at h
  unfold Column.foROpt at h; split at h; · cases h
  rw [hE, raw_foR .i64 8 rfl (by decide)]
  simp only [Array.getElem?_map, Array.getElem?_range, show k < m.toNat by omega, if_true, Option.map_some,
    Nat.reduceMul, Option.some.inj h, ofNat_toNat_mod64]

/-- **`Arr.gather_row` with nulls**: row `j` of `Opt.gather m ix x` is row `ix[j]` of `x`, null flag included, since
`kgather` moves each row's flag (`foRNuls`) with its word (`raw_kgather`). -/
theorem Opt.gather_row {t : QAtomicType} {m n : USize} {ix : Enc} (x : Opt t n) {y : Opt t m}
    (h : Opt.gather m ix x = .ok y) (j : Fin m.toNat) : ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ y.get j = x.get i := by
  simp only [Opt.gather] at h
  split at h
  · rename_i o ho
    cases h
    have hv := kgather_valid ho
    obtain ⟨his, hes, hlt, ho'⟩ := raw_kgather m ix n _ o ho
    generalize hws : (Enc.raw .i64 m ix).map (fun i => (Enc.raw .i64 n x.enc)[i.toNat]?.getD 0) = ws at ho'
    generalize hnul : (if hasNul x.enc then nulMap ((Enc.raw .i64 m ix).map fun i => (foRNuls n x.enc)[i.toNat]?.getD 0)
      else .empty) = nul at ho'
    have hwsz : ws.size = m.toNat := by rw [← hws, Array.size_map, his]
    have hj : j.1 < (Enc.raw .i64 m ix).size := by rw [his]; exact j.2
    have hjw : j.1 < ws.size := by rw [hwsz]; exact j.2
    have hi := hlt j j.2
    have hc := wordsFoR_nul ws nul (n := m) hwsz.symm
    -- the flag of row `j` is source row `ix[j]`'s
    have hf : (foRNuls m o)[j.1]? = (foRNuls n x.enc)[((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat]? := by
      rw [ho', foRNuls_wordsFoR ws nul hwsz.symm j hjw]
      cases hN : hasNul x.enc
      · rw [foRNuls_plain x.wf hN hi]; simp [← hnul, hN, bitAt_empty]
      · rw [foRNuls_bit n x.enc hi]; simp only [← hnul, hN, if_true]
        unfold nulMap
        rw [bitAt_packOf _ _ j (by simpa [his] using j.2)]
        simp [Array.getElem?_eq_getElem hj]
    refine ⟨⟨_, hi⟩, rfl, Opt.get_eq_of_raw _ x (show Kernel.Enc.Valid m o by rw [ho']; exact hc.1) hv j ⟨_, hi⟩ hf
      fun h0 _ a b ha hb _ => ?_⟩
    have h0' : (foRNuls m o)[j.1]? = some 0 := h0
    have ha' : (Enc.raw .i64 m o)[j.1]? = some a := ha
    have hbit : Column.bitAt nul j = false := by
      have h1 := foRNuls_wordsFoR ws nul hwsz.symm j hjw
      rw [← ho', h0'] at h1
      cases hb' : Column.bitAt nul j <;> simp_all
    rw [ho', raw_wordsFoR_of_bit ws nul hwsz j hjw hbit] at ha'
    obtain rfl := Option.some.inj ha'
    subst hws
    simp only [Array.getElem?_eq_getElem hj, Option.getD_some] at hb
    simp only [Array.getElem_map, hb, Option.getD_some]
  · cases h

end

/-- `ValsB.view` of a `SumCols` at `o` cast to `Obj.band a b` (the `▸` that `ValsB.ofOpt` and `ValsB.ofGen` write): the
`SumV` that `view.go` builds at `o`. -/
theorem ValsB.view_go_cast {a b : Obj} {n : USize} : ∀ {o : Option QAtomicType} (e : Obj.band a b = o)
    (y : SumCols (fun l => ValsB true a l) (fun r => ValsB true b r) n o),
    ValsB.view.go (Obj.band a b) rfl
      (show SumCols (fun l => ValsB true a l) (fun r => ValsB true b r) n (Obj.band a b) from e ▸ y) =
        ValsB.view.go o e y
  | _, rfl, _ => rfl

@[simp] theorem ValsB.view_ofOpt {o : Bool} {a b : Obj} {n : USize} {t : QAtomicType} (h : Obj.band a b = some t)
    (x : Opt t n) : (ValsB.ofOpt (o := o) h x).view = .opt h x := ValsB.view_go_cast h x

@[simp] theorem ValsB.view_ofGen {o : Bool} {a b : Obj} {n : USize} (h : Obj.band a b = none) (tag : Arr .u1 n)
    (x : ValsB true a n) (y : ValsB true b n) : (ValsB.ofGen (o := o) h tag x y).view = .gen h tag x y :=
  ValsB.view_go_cast h _

/-- **The row form of the bridge at an atom column**: row `j` of `ColB.gather m ix x` is row `ix[j]` of `x`. -/
theorem ColB.gather_row {o : Bool} {t : QAtomicType} {m n : USize} {ix : Enc} (x : ColB o t n) {y : ColB o t m}
    (h : ColB.gather m ix x = .ok y) (j : Fin m.toNat) : ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ ColB.get y j = ColB.get x i := by
  cases o
  · exact Arr.gather_row x h j
  · obtain ⟨i, e, r⟩ := Opt.gather_row x h j
    exact ⟨i, e, show (Opt.get y j).getD default = (Opt.get x i).getD default by rw [r]⟩

/-- **The row form of the bridge**: row `j` of `ValsB.gather m ix x` is row `ix[j]` of `x`, the index being below `n`. -/
theorem ValsB.gather_row {m : USize} {ix : Enc} : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) →
    {y : ValsB o A m} → ValsB.gather m ix x = .ok y → ∀ j : Fin m.toNat, ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ ValsB.row y j = ValsB.row x i
  | _, .atom _, _, x, _, h, j => ColB.gather_row x h j
  | _, .prod a b, n, x, y, h, j => by
    simp only [ValsB.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    obtain ⟨i1, e1, r1⟩ := ValsB.gather_row x.1 h1 j
    obtain ⟨i2, e2, r2⟩ := ValsB.gather_row x.2 h2 j
    obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
    exact ⟨i1, e1, by simp only [ValsB.row, r1, r2]⟩
  | _, .arr _, _, ⟨c, lo, hi, f⟩, _, h, j => by
    simp only [ValsB.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i lo' h1
    split at h; · cases h
    rename_i hi' h2
    cases h
    obtain ⟨i1, e1, r1⟩ := ColB.gather_row lo h1 j
    obtain ⟨i2, e2, r2⟩ := ColB.gather_row hi h2 j
    obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
    exact ⟨i1, e1, by simp only [ValsB.row, r1, r2]⟩
  | _, .sum a b, _, s, _, h, j => by
    simp only [ValsB.gather] at h
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> rw [hv] at h <;>
      simp only [bind, Except.bind, pure, Except.pure] at h
    · split at h; · cases h
      rename_i x' h1
      cases h
      obtain ⟨i, e, r⟩ := Opt.gather_row x h1 j
      exact ⟨i, e, by simp only [ValsB.row, hv, ValsB.view_ofOpt, r]⟩
    · split at h; · cases h
      rename_i tag' h1
      split at h; · cases h
      rename_i x' h2
      split at h; · cases h
      rename_i y' h3
      cases h
      obtain ⟨i1, e1, r1⟩ := Arr.gather_row tag h1 j
      obtain ⟨i2, e2, r2⟩ := ValsB.gather_row x h2 j
      obtain ⟨i3, e3, r3⟩ := ValsB.gather_row y h3 j
      obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
      obtain rfl : i1 = i3 := Fin.ext (e1.symm.trans e3)
      exact ⟨i1, e1, by simp only [ValsB.row, hv, ValsB.view_ofGen, r1, r2, r3]⟩
  | _, .one, n, _, _, h, j => by
    simp only [ValsB.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p h1
    obtain ⟨i, e, -⟩ := Arr.gather_row (Arr.mk (t := .i64) (n := n) .pos trivial rfl) h1 j
    exact ⟨i, e, rfl⟩

/-- What a row `Opt.fill` writes reads as: the null, or at `general`, which has no null, its `default`. -/
def Opt.filler : (t : QAtomicType) → Option (El t)
  | .general => some (default : QValue)
  | _ => none

/-- **A side whose every cell is a slice of its payload** (PLAN 8.5), over the rows `P` the side owns: at an `arr` side
each owned row's `[lo, hi)` has `0 ≤ lo ≤ hi ≤ m` and the payload is `WFOn` all its rows; an `Opt` leaf (`o = true`) is
no null on `P` and the filler (`Opt.filler`) off `P`, so two unowned rows read alike; a generic sum has tag `false` off `P`, and each summand owns the rows of `P` its tag names.
`readVals` checks the cells (`cellBad`) and each producer keeps it, so a reader may take `[lo, hi)` as it is, where
`ValsB.row` clamps it. -/
def ColB.OwnedOn : {o : Bool} → {t : QAtomicType} → {n : USize} → ColB o t n → (Fin n.toNat → Prop) → Prop
  | false, _, _, _, _ => True
  | true, t, _, x, P => ∀ i, (P i → Opt.get x i ≠ none) ∧ (¬P i → Opt.get x i = Opt.filler t)

/-- The rows `P` of `x` are the rows `ValsB.WFOn` says it owns. -/
def ValsB.WFOn : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → (Fin n.toNat → Prop) → Prop
  | _, .atom _, _, x, P => ColB.OwnedOn x P
  | _, .one, _, _, _ => True
  | _, .prod _ _, _, x, P => ValsB.WFOn x.1 P ∧ ValsB.WFOn x.2 P
  | _, .arr _, _, ⟨m, lo, hi, f⟩, P => ColB.OwnedOn lo P ∧ ColB.OwnedOn hi P ∧
      (∀ i, P i → 0 ≤ (ColB.get lo i).toInt ∧ (ColB.get lo i).toInt ≤ (ColB.get hi i).toInt ∧
        (ColB.get hi i).toInt ≤ (m.toNat : Int)) ∧ ValsB.WFOn f fun _ => True
  | _, .sum _ _, _, s, P => match s.view with
    | .opt _ x => ∀ i, ¬P i → x.get i = none
    | .gen _ tag x y => (∀ i, ¬P i → tag.get i = false) ∧ ValsB.WFOn x (fun i => P i ∧ tag.get i = false) ∧
      ValsB.WFOn y (fun i => P i ∧ tag.get i = true)

/-- Every row owned. -/
def Vals.WF {A : Obj} {n : USize} (x : Vals A n) : Prop := ValsB.WFOn x fun _ => True

/-- Both sides of `R` `Vals.WF`. -/
def Tab.WF {k v : Obj} (R : Tab k v) : Prop := Vals.WF R.key ∧ Vals.WF R.val

/-- `ValsB.WFOn` depends on `P` only through its values. -/
theorem ColB.OwnedOn_congr {o : Bool} {t : QAtomicType} {n : USize} (x : ColB o t n) {P Q : Fin n.toNat → Prop}
    (h : ∀ i, P i ↔ Q i) : ColB.OwnedOn x P ↔ ColB.OwnedOn x Q := by
  cases o
  · exact Iff.rfl
  · exact forall_congr' fun i => by rw [h i]

/-- `ValsB.WFOn` depends on `P` only through its values. -/
theorem ValsB.WFOn_congr : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → {P Q : Fin n.toNat → Prop} →
    (∀ i, P i ↔ Q i) → (ValsB.WFOn x P ↔ ValsB.WFOn x Q)
  | _, .atom _, _, x, _, _, h => ColB.OwnedOn_congr x h
  | _, .one, _, _, _, _, _ => Iff.rfl
  | _, .prod _ _, _, x, _, _, h => and_congr (ValsB.WFOn_congr x.1 h) (ValsB.WFOn_congr x.2 h)
  | _, .arr _, _, ⟨m, lo, hi, f⟩, _, _, h => by
    simp only [ValsB.WFOn]
    exact and_congr (ColB.OwnedOn_congr lo h) (and_congr (ColB.OwnedOn_congr hi h)
      (and_congr (forall_congr' fun i => by rw [h i]) Iff.rfl))
  | _, .sum a b, _, s, _, _, h => by
    simp only [ValsB.WFOn]
    cases hv : s.view with
    | opt hb x => exact forall_congr' fun i => by rw [h i]
    | gen hb tag x y =>
      exact and_congr (forall_congr' fun i => by rw [h i])
        (and_congr (ValsB.WFOn_congr x fun i => by rw [h i]) (ValsB.WFOn_congr y fun i => by rw [h i]))

/-- **`ColB.gather` keeps `WFOn` at an atom column**, over the rows whose index lands in `P`. -/
theorem ColB.gather_wf {o : Bool} {t : QAtomicType} {m n : USize} {ix : Enc} {x : ColB o t n} {y : ColB o t m}
    (h : ColB.gather m ix x = .ok y) (P : Fin n.toNat → Prop) (hx : ColB.OwnedOn x P) :
    ColB.OwnedOn y fun j => ∃ i : Fin n.toNat, ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ P i := by
  cases o
  · trivial
  · intro j
    obtain ⟨i, e, r⟩ := Opt.gather_row x h j
    have hx' : ∀ i, (P i → Opt.get x i ≠ none) ∧ (¬P i → Opt.get x i = Opt.filler t) := hx
    rw [r]
    refine ⟨fun ⟨i', e', hp⟩ => ?_, fun hn => (hx' i).2 fun hp => hn ⟨i, e, hp⟩⟩
    obtain rfl : i' = i := Fin.ext (e'.symm.trans e)
    exact (hx' i').1 hp

/-- **`ValsB.gather` keeps `WFOn`**: a gathered row `j` is owned when the row `ix[j]` of `x` is. -/
theorem ValsB.gather_wf {m : USize} {ix : Enc} : {o : Bool} → {A : Obj} → {n : USize} → {x : ValsB o A n} →
    {y : ValsB o A m} → ValsB.gather m ix x = .ok y → ∀ P, ValsB.WFOn x P →
    ValsB.WFOn y fun j => ∃ i : Fin n.toNat, ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ P i
  | _, .atom _, _, _, _, h, P, hx => ColB.gather_wf h P hx
  | _, .one, _, _, _, _, _, _ => trivial
  | _, .prod _ _, _, x, y, h, P, hx => by
    simp only [ValsB.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i a ha; split at h; · cases h
    rename_i b hb; cases h
    exact ⟨ValsB.gather_wf ha P hx.1, ValsB.gather_wf hb P hx.2⟩
  | _, .arr _, _, ⟨c, lo, hi, f⟩, y, h, P, hx => by
    simp only [ValsB.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i L hL; split at h; · cases h
    rename_i H hH; cases h
    obtain ⟨hl, hh, hb, hf⟩ := hx
    refine ⟨ColB.gather_wf hL P hl, ColB.gather_wf hH P hh, fun j ⟨i, e, hp⟩ => ?_, hf⟩
    obtain ⟨i1, e1, r1⟩ := ColB.gather_row lo hL j
    obtain ⟨i2, e2, r2⟩ := ColB.gather_row hi hH j
    obtain rfl : i1 = i := Fin.ext (e1.symm.trans e)
    obtain rfl : i2 = i1 := Fin.ext (e2.symm.trans e1)
    rw [r1, r2]; exact hb _ hp
  | _, .sum _ _, _, s, y, h, P, hx => by
    simp only [ValsB.gather] at h
    simp only [ValsB.WFOn] at hx
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> rw [hv] at h hx <;>
      simp only [bind, Except.bind, pure, Except.pure] at h
    · split at h; · cases h
      rename_i x' h1
      cases h; simp only [ValsB.WFOn, ValsB.view_ofOpt]
      intro j hj
      obtain ⟨i, e, r⟩ := Opt.gather_row x h1 j
      rw [r]; exact hx i fun hp => hj ⟨i, e, hp⟩
    · split at h; · cases h
      rename_i tag' h1
      split at h; · cases h
      rename_i x' h2
      split at h; · cases h
      rename_i y' h3
      cases h
      simp only [ValsB.WFOn, ValsB.view_ofGen]
      obtain ⟨ht, hx1, hy1⟩ := hx
      have key : ∀ (k : Bool) (j : Fin m.toNat), (∃ i : Fin _, ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧
          P i ∧ tag.get i = k) ↔ ((∃ i : Fin _, ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ P i) ∧
          tag'.get j = k) := fun k j => by
        obtain ⟨i0, e0, r0⟩ := Arr.gather_row tag h1 j
        constructor
        · rintro ⟨i, e, hp, hk⟩
          obtain rfl : i = i0 := Fin.ext (e.symm.trans e0)
          exact ⟨⟨i, e, hp⟩, by rw [r0]; exact hk⟩
        · rintro ⟨⟨i, e, hp⟩, hk⟩
          obtain rfl : i = i0 := Fin.ext (e.symm.trans e0)
          exact ⟨i, e, hp, by rw [← r0]; exact hk⟩
      refine ⟨fun j hj => ?_, (ValsB.WFOn_congr x' (key false)).1 (ValsB.gather_wf h2 _ hx1),
        (ValsB.WFOn_congr y' (key true)).1 (ValsB.gather_wf h3 _ hy1)⟩
      obtain ⟨i, e, r⟩ := Arr.gather_row tag h1 j
      rw [r]; exact ht i fun hp => hj ⟨i, e, hp⟩

/-- **`ValsB.gather` keeps `Vals.WF`**: every index is in range (`gather_row`), so `gather_wf` at `P = True` owns all rows. -/
theorem Vals.gather_wf {m : USize} {ix : Enc} {o : Bool} {A : Obj} {n : USize} {x : ValsB o A n} {y : ValsB o A m}
    (h : ValsB.gather m ix x = .ok y) (hx : ValsB.WFOn x fun _ => True) : ValsB.WFOn y fun _ => True :=
  (ValsB.WFOn_congr _ fun j => ⟨fun _ => trivial,
    fun _ => (ValsB.gather_row _ h j).imp fun _ e => ⟨e.1, trivial⟩⟩).1 (ValsB.gather_wf h _ hx)

/-- What `ValsB.cols` answers at a `sum` side, unfolded: the tag's column, then each summand's columns. -/
theorem ValsB.cols_sum {o : Bool} {a b : Obj} {n : USize} {s : ValsB o (.sum a b) n} {hb : Obj.band a b = none}
    {tag : Arr .u1 n} {x : ValsB true a n} {y : ValsB true b n} (hv : s.view = .gen hb tag x y)
    {es : List (AscKey × Enc)} (hes : ValsB.cols s = .ok es) :
    ∃ xs ys, es = (.atom .u1, tag.enc) :: (xs ++ ys) ∧ ValsB.cols x = .ok xs ∧ ValsB.cols y = .ok ys := by
  simp only [ValsB.cols, hv, bind, Except.bind, pure, Except.pure] at hes
  split at hes; · cases hes
  rename_i xs hxs
  split at hes; · cases hes
  rename_i ys hys
  cases hes
  exact ⟨xs, ys, rfl, hxs, hys⟩

/-- What `Vals.nub` answers, unfolded: each kernel's answer named, in the order of the composition. -/
theorem Vals.nub_ok {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∃ es vs p k g f ix y, ValsB.cols x = .ok es ∧ kasc n es = .ok (vs, p) ∧
      kseen n ((es.map (·.1)).zip vs) = .ok (k, g, f) ∧ kgather k.toUSize f n p = .ok ix ∧
      ValsB.gather k.toUSize ix x = .ok y ∧ r = ⟨k.toUSize, y⟩ := by
  simp only [Vals.nub, bind, Except.bind] at h
  repeat (split at h; · cases h)
  rename_i _ es hes _ vp hvp _ kgf hkgf _ ix hix
  cases hg : ValsB.gather kgf.1.toUSize ix x with
  | error s => simp [hg, Functor.map, Except.map] at h
  | ok y =>
    simp only [hg, Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨es, vp.1, vp.2, kgf.1, kgf.2.1, kgf.2.2, ix, y, hes, hvp, hkgf, hix, hg, h.symm⟩

/-- **Every row of `Vals.nub x` is a row of `x`.** -/
theorem Vals.nub_sub {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∀ j : Fin r.1.toNat, ∃ i : Fin n.toNat, ValsB.row r.2 j = ValsB.row x i := by
  obtain ⟨_, _, _, _, _, _, _, y, _, _, _, _, hy, rfl⟩ := Vals.nub_ok h
  exact fun j => (ValsB.gather_row x hy j).imp fun _ h => h.2

/-- **`asc_perm`'s permutation is `kasc`'s grade** of the codes (`ascGrade`): both are what `p` reads back as. -/
theorem Verify.asc_perm_grade {n : USize} {es : List (AscKey × Enc)} {vs : List Enc} {p : Enc} {ps : List Nat}
    (ha : kasc n es = .ok (vs, p)) (hp : p = wordsFoR (ps.map Nat.toUInt64).toArray)
    (hperm : ps.Perm (List.range n.toNat)) : ps = ascGrade n.toNat (ascKeys n es) := by
  obtain ⟨cs, hc, -, -, -, -, -, -, -, hpk⟩ := kasc_ok ha
  rw [ascCol_keys hc] at hpk
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hperm' := (ascGrade_spec n.toNat (ascKeys n es)).1
  have hlen' : (ascGrade n.toNat (ascKeys n es)).length = n.toNat := by simpa using hperm'.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have e : ((ascGrade n.toNat (ascKeys n es)).map Nat.toUInt64).toArray = (ps.map Nat.toUInt64).toArray := by
    rw [← hrp, hpk]; exact ((wordsFoR_closed _ (by simp [hlen'])).2.1).symm
  refine List.ext_getElem (by rw [hlen, hlen']) fun q h1 h2 => ?_
  have e2 := congrArg (fun a : Array UInt64 => a[q]?) e
  simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq] at e2
  rw [← hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem h1))),
    ← hc64 _ (List.mem_range.1 (hperm'.mem_iff.1 (List.getElem_mem h2))), e2]

/-- **A sorted column agrees with its input row by row, nulls included**: `v`, `asc_perm`'s answer for the input
column `e` through the permutation `ps`, holds at row `q` input row `ps[q]`'s null flag and, off a null, its word; and
`v` holds a null exactly where `e` does (`hasNul_flags`, `e` being `Ext.Enc.WF`). -/
theorem asc_col_row {m : USize} {t : QAtomicType} {e v : Enc} {ws : Array UInt64} {nul : ByteArray} {ps : List Nat}
    (hw : Ext.Enc.WF t m e) (hv : v = wordsFoR ws nul) (hws : ws.size = m.toNat)
    (hwq : ∀ k (hk : k < ps.length), ws[k]? = (Enc.raw .i64 m e)[ps[k]]?)
    (h0 : hasNul e = false → nul = .empty)
    (h1 : hasNul e = true → ∃ nf : Array UInt64, nul = nulMap nf ∧ nf.size = m.toNat ∧
      ∀ k (hk : k < ps.length), nf[k]? = (foRNuls m e)[ps[k]]?)
    (hperm : ps.Perm (List.range m.toNat)) (q : Nat) (hq : q < ps.length) :
    (nulWords m v (Enc.raw .i64 m v))[q]? = (nulWords m e (Enc.raw .i64 m e))[ps[q]]? ∧
      hasNul v = hasNul e ∧ (foRNuls m v)[q]? = (foRNuls m e)[ps[q]]? := by
  subst hv
  have hlen : ps.length = m.toNat := by simpa using hperm.length_eq
  have hlt : ∀ k (hk : k < ps.length), ps[k] < m.toNat := fun k hk => List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hk))
  -- the flags: `nul` is `e`'s flags through `ps`, or empty where `e` has none
  have hfv : ∀ k (hk : k < ps.length), (foRNuls m (wordsFoR ws nul))[k]? = (foRNuls m e)[ps[k]]? := by
    intro k hk
    rw [foRNuls_wordsFoR ws nul hws.symm k (by omega)]
    rw [foRNuls_bit m e (hlt k hk)]
    cases hN : hasNul e
    · rw [h0 hN, bitAt_empty]
      have hz : (foRNuls m e)[ps[k]]?.getD 0 = 0 := by
        have hf := hasNul_flags hw; rw [hN] at hf
        cases hx : (foRNuls m e)[ps[k]]? with
        | none => rfl
        | some x =>
          simp only [Option.getD_some]
          refine Decidable.byContradiction fun hne => Bool.false_ne_true (hf.trans (Array.any_eq_true.2 ?_))
          obtain ⟨hlt', hx'⟩ := Array.getElem?_eq_some_iff.1 hx
          exact ⟨ps[k], hlt', by rw [hx']; simpa using hne⟩
      simp [hz]
    · obtain ⟨nf, rfl, hnf, hnk⟩ := h1 hN
      unfold nulMap; rw [bitAt_packOf _ _ k (by omega), hnk k hk]
  have hwv : Ext.Enc.WF .i64 m (wordsFoR ws nul) := (wordsFoR_nul ws nul hws.symm).2.2.2 rfl fun h => by cases h
  have hsz : (foRNuls m (wordsFoR ws nul)).size = m.toNat := foRNuls_size m _
  have hse : (foRNuls m e).size = m.toNat := foRNuls_size m e
  -- `v` holds a null exactly where `e` does: its flags are `e`'s through the permutation `ps`
  have hH : hasNul (wordsFoR ws nul) = hasNul e := by
    rw [hasNul_flags hwv, hasNul_flags hw, Bool.eq_iff_iff, Array.any_eq_true, Array.any_eq_true]
    constructor
    · rintro ⟨k, hk, hf⟩
      have := hfv k (by omega)
      rw [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem (by rw [hse]; exact hlt k (by omega))] at this
      exact ⟨_, _, (Option.some.inj this) ▸ hf⟩
    · rintro ⟨i, hi, hf⟩
      obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 (show i < m.toNat by omega)))
      have := hfv k hk
      rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by rw [hse]; exact hlt k hk)] at this
      refine ⟨k, by omega, ?_⟩
      rw [Option.some.inj this]; simp only [hki]; exact hf
  refine ⟨?_, hH, hfv q hq⟩
  unfold nulWords
  rw [hH]
  have hrq : (Enc.raw .i64 m e)[ps[q]]? = ws[q]? := (hwq q hq).symm
  have hrv : (Enc.raw .i64 m (wordsFoR ws nul)).size = m.toNat := (wordsFoR_nul ws nul hws.symm).2.1
  cases hN : hasNul e
  · obtain rfl := h0 hN
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [raw_wordsFoR_of_bit ws _ hws q (by omega) (bitAt_empty q), hrq, Array.getElem?_eq_getElem (by omega)]
  · simp only [↓reduceIte, Array.getElem?_mapIdx, hfv q hq, hrq, Array.getElem?_eq_getElem (show q < ws.size by omega),
      Array.getElem?_eq_getElem (show q < (Enc.raw .i64 m (wordsFoR ws nul)).size by omega), Option.map_some]
    cases hf : (foRNuls m e)[ps[q]]?.getD 0 == 0
    · simp
    · -- a row whose flag is `0` is no null in `nul`, so it reads back its word
      have hnq : Column.bitAt nul q = false := by
        have h := (foRNuls_wordsFoR ws nul hws.symm q (by omega)).symm.trans (hfv q hq)
        cases hb : Column.bitAt nul q
        · rfl
        · rw [hb] at h; rw [← h] at hf; simp at hf
      have h := raw_wordsFoR_of_bit ws nul hws q (by omega) hnq
      rw [Array.getElem?_eq_getElem (show q < (Enc.raw .i64 m (wordsFoR ws nul)).size by omega)] at h
      simp [Option.some.inj h]

/-- `kasc`'s grade holds no null: it is `wordsFoR` of the permutation (`asc_perm`). -/
theorem kasc_plain {N : USize} {es : List (AscKey × Enc)} {vs : List Enc} {p : Enc} (h : kasc N es = .ok (vs, p)) :
    hasNul p = false := by
  obtain ⟨_, he, -⟩ := asc_perm _ _ _ _ h; rw [he]; exact hasNul_wordsFoR _

/-- `kseen`'s group and first-row columns hold no null: both are `wordsFoR` (`kseen_ok`). -/
theorem kseen_plain {n : USize} {es : List (AscKey × Enc)} {k : Nat} {g f : Enc} (h : kseen n es = .ok (k, g, f)) :
    hasNul g = false ∧ hasNul f = false := by
  obtain ⟨-, hg, hf⟩ := kseen_ok h; rw [hg, hf]; exact ⟨hasNul_wordsFoR _, hasNul_wordsFoR _⟩

/-- **`kasc`'s grade**: `p` reads as the stable grade `ps` of the codes (`Verify.asc_perm_grade`), and the `kseen` key
of sorted row `q` (over the sorted columns `vs`) is input row `ps[q]`'s: every key column is `Ext.Enc.WF` (so its
`hasNul` is its rows' flags (`asc_col_row`). -/
theorem kasc_grade {N : USize} {es : List (AscKey × Enc)} {vs : List Enc} {p : Enc}
    (ha : kasc N es = .ok (vs, p)) (hwf : ∀ x ∈ es, ∃ t, Ext.Enc.WF t N x.2) :
    ∃ cs, es.mapM (ascCol N) = .ok cs ∧
      Enc.raw .i64 N p = ((ascGrade N.toNat (ascKeys N es)).map Nat.toUInt64).toArray ∧
      ∀ q (hq : q < (ascGrade N.toNat (ascKeys N es)).length),
        seenKey N ((es.map (·.1)).zip vs) q = seenKey N es (ascGrade N.toNat (ascKeys N es))[q] := by
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm N es vs p ha
  obtain ⟨cs, hc, -⟩ := kasc_ok ha
  have hpsg := asc_perm_grade ha hp hperm
  have hrp : Enc.raw .i64 N p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [show ps.length = N.toNat by simpa using hperm.length_eq])).2.1
  refine ⟨cs, hc, hpsg ▸ hrp, fun q hq => ?_⟩
  revert hq; rw [← hpsg]; intro hq
  -- the sorted columns hold input row `ps[q]`'s words at row `q`, so every code does (`ascKeys_row`), `cells` keys' too
  simp only [seenKey]
  have hc : ∀ c (h : c < ((es.map (·.1)).zip vs).length) (h' : c < es.length),
      (nulWords N vs[c] (Enc.raw .i64 N vs[c]))[q]? = (nulWords N es[c].2 (Enc.raw .i64 N es[c].2))[ps[q]]? ∧
        hasNul vs[c] = hasNul es[c].2 ∧ (foRNuls N vs[c])[q]? = (foRNuls N es[c].2)[ps[q]]? := fun c h h' => by
    obtain ⟨ws, nul, hv, hws, hwq, h0, h1⟩ := hcol c es[c] (vs[c]'(by simp at h; omega)) (List.getElem?_eq_getElem h')
      (List.getElem?_eq_getElem _)
    obtain ⟨t, hw⟩ := hwf es[c] (List.getElem_mem h')
    exact asc_col_row hw hv hws hwq h0 h1 hperm q hq
  refine ascKeys_row (List.map_fst_zip (by simp [hvl])) (fun c h h' => ?_) fun c h h' => ?_
  · simp only [List.getElem_zip]; exact (hc c h h').1
  · simp only [List.getElem_zip]; exact (hc c h h').2

/-- **Every key column of a side is a column**, `Ext.Enc.WF` at some type and the side's `n`: an atom's and a sum's
tag are their `Arr`'s, a `cells` key is `.pos`, a summand's are those of the side gathered from it, and a `1+atom t`
band is its own `Opt` column, which holds its nulls in band (`kasc` codes them first, `nulCodes`). -/
theorem ColB.enc_wf {o : Bool} {t : QAtomicType} {n : USize} (x : ColB o t n) : Ext.Enc.WF t n (ColB.enc x) := by
  cases o <;> exact x.wf

theorem ValsB.cols_wf : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → {es : List (AscKey × Enc)} →
    ValsB.cols x = .ok es → ∀ c ∈ es, ∃ t, Ext.Enc.WF t n c.2
  | _, .atom t, _, x, _, h, c, hc => by
    simp only [ValsB.cols, Except.ok.injEq] at h; subst h
    rw [List.mem_singleton.1 hc]; exact ⟨t, ColB.enc_wf x⟩
  | _, .prod _ _, _, x, _, h, c, hc => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i h1
    split at h; · cases h
    rename_i h2
    cases h
    rcases List.mem_append.1 hc with hc | hc
    · exact ValsB.cols_wf _ h1 c hc
    · exact ValsB.cols_wf _ h2 c hc
  | _, .arr _, _, ⟨_, _, _, _⟩, _, h, c, hc => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    cases h; rw [List.mem_singleton.1 hc]; exact ⟨.i64, trivial⟩
  | _, .sum _ _, _, s, _, h, c, hc => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩
    · simp only [ValsB.cols, hv, Except.ok.injEq] at h; subst h
      rw [List.mem_singleton.1 hc]; exact ⟨_, x.wf⟩
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := ValsB.cols_sum hv h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨.u1, tag.wf⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact ValsB.cols_wf _ hxs c hc
    · exact ValsB.cols_wf _ hys c hc
  | _, .one, _, _, _, h, c, hc => by
    simp only [ValsB.cols, Except.ok.injEq] at h; subst h; cases hc

/-- **The sorted rows' key at `q` is input row `ps[q]`'s**, `ps` the permutation `asc_perm` reads `p` as: `kasc_grade`
on a side's columns (`ValsB.cols_wf`). -/
theorem Vals.sorted_key {A : Obj} {n : USize} {x : Vals A n} {es : List (AscKey × Enc)} (hes : ValsB.cols x = .ok es)
    {vs : List Enc} {p : Enc} (ha : kasc n es = .ok (vs, p)) {ps : List Nat}
    (hp : p = wordsFoR (ps.map Nat.toUInt64).toArray) (hperm : ps.Perm (List.range n.toNat)) :
    ∀ q (hq : q < ps.length), seenKey n ((es.map (·.1)).zip vs) q = seenKey n es ps[q] := by
  obtain ⟨-, -, -, hk⟩ := kasc_grade ha (ValsB.cols_wf x hes)
  rw [asc_perm_grade ha hp hperm]; exact hk

/-- **Every row of `x` has a row of `Vals.nub x` equal to it in the kernels' order codes** (`seenKey` over the side's
columns `es`): the first input row of its run among the sorted rows. Where equal codes mean equal rows, the two sides
hold the same rows (`Vals.nub_rows`). -/
theorem Vals.nub_cover {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (AscKey × Enc)} (hes : ValsB.cols x = .ok es) (i : Fin n.toNat) :
    ∃ j : Fin r.1.toNat, ∃ i' : Fin n.toNat, ValsB.row r.2 j = ValsB.row x i' ∧ seenKey n es i' = seenKey n es i := by
  obtain ⟨es', vs, p, k, g, f, ix, y, hes', ha, hs, hix, hy, rfl⟩ := Vals.nub_ok h
  have hee : es = es' := Except.ok.inj (hes.symm.trans hes'); subst hee
  obtain ⟨ps, hp, hperm, -, -⟩ := asc_perm n es vs p ha
  obtain ⟨hk, -, hf⟩ := kseen_ok hs
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hkey := Vals.sorted_key hes ha hp hperm
  generalize seenKey n ((es.map (·.1)).zip vs) = K at hk hf hkey
  obtain ⟨q, hq, hqi⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 i.2))
  obtain ⟨hgl, -, hgk, -⟩ := (firsts_spec K n.toNat).2.2.2.2.2 q (by omega)
  have hq' : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < n.toNat := firsts_lt K n.toNat (List.getElem_mem hgl)
  have hkn : k ≤ n.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  obtain ⟨i', e1, r1⟩ := ValsB.gather_row x hy ⟨Verify.groupOf K n.toNat q, by rw [hkU, hk]; exact hgl⟩
  refine ⟨_, i', r1, ?_⟩
  -- `ix[G]` is `ps[firsts[G]]`
  obtain ⟨his, hps, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 k.toUSize f = ((firstsOf K n.toNat).map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hkU, hk]; simp)).2.1
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hri : Enc.raw .i64 k.toUSize ix = (((firstsOf K n.toNat).map Nat.toUInt64).toArray.map fun w =>
      ((ps.map Nat.toUInt64).toArray)[w.toNat]?.getD 0) := by
    rw [kgather_plain hix (by rw [hp]; exact hasNul_wordsFoR _), (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1,
      hrf, hrp]
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hfG : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < ps.length := by omega
  have hi' : i'.1 = ps[(firstsOf K n.toNat)[Verify.groupOf K n.toNat q]] := by
    rw [← e1, hri]
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hgl,
      Option.map_some, Option.getD_some, hc64 _ hq', List.getElem?_eq_getElem hfG]
    exact hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hfG)))
  rw [hi', ← hkey _ hfG, hgk, hkey q hq, hqi]

/-- A column `kasc` reads is one every kernel reads: `ascCol` answers only on `foRWords`' columns. -/
theorem Verify.ascCol_valid {m : USize} {c : AscKey × Enc} {xk : Array UInt64 × List (Array UInt64)}
    (h : ascCol m c = .ok xk) : Kernel.Enc.Valid m c.2 := by
  obtain ⟨a, e⟩ := c
  cases a with
  | atom t =>
    rw [ascCol] at h
    split at h; · cases h
    cases hw : ascWords m (t, e) with
    | error s => simp [hw, Functor.map, Except.map] at h
    | ok x => exact (foRWords_valid _ _ _).2 _ (ascWords_foR hw)
  | cells n c lo hi els =>
    rw [ascCol] at h
    cases hix : foRWords "asc: cells" m e with
    | error s => simp [hix, bind, Except.bind] at h
    | ok ix => exact (foRWords_valid _ _ _).2 _ hix

/-- **Equal order codes of one column, equal elements**: where `kasc` reads `x` (`ascCol` answers), `x` is a column
every kernel reads, and rows with equal codes (`seenKey`) hold one atom (`ascOrd_atom`), so one element. -/
theorem Arr.eq_of_codes {t : QAtomicType} {n : USize} (x : Arr t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) : Kernel.Enc.Valid n x.enc ∧ ∀ i i' : Fin n.toNat,
      seenKey n [(.atom t, x.enc)] i = seenKey n [(.atom t, x.enc)] i' → x.get i = x.get i' := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨f, hof⟩ := (ascCol_ok hac).2.2.2 t rfl
  have hv := ascCol_valid hac
  refine ⟨hv, fun i i' hk => ?_⟩
  simp only [seenKey, ascKeys, ascKey, nulCodes, nulWords, Arr.plain, Bool.false_eq_true, if_false, List.nil_append, List.append_nil, List.map_cons, List.map_nil, hof, Option.getD_some, List.cons.injEq, and_true,
    Array.getElem?_map] at hk
  exact Arr.get_eq_of_raw x x hv hv i i' fun hg a b ha hb hu =>
    (ascOrd_atom hof hg hu).1 (by simpa only [ha, hb, Option.map_some, Option.getD_some] using hk)

/-- **`Arr.eq_of_codes` with nulls**: rows of an `Opt` with equal order codes (`nulCodes`: the null column, then the
word codes with `0` at a null) carry one null flag and, off a null, one atom, so one element. -/
theorem Opt.eq_of_codes {t : QAtomicType} {n : USize} (x : Opt t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) : Kernel.Enc.Valid n x.enc ∧ ∀ i i' : Fin n.toNat,
      seenKey n [(.atom t, x.enc)] i = seenKey n [(.atom t, x.enc)] i' → x.get i = x.get i' := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨hraw, hsz, -, hat⟩ := ascCol_ok hac
  obtain ⟨f, hof⟩ := hat t rfl
  have hv := ascCol_valid hac
  dsimp only at hof hv hraw
  have hs : (Enc.raw .i64 n x.enc).size = n.toNat := by rw [← hraw]; exact hsz
  refine ⟨hv, fun i i' hk => ?_⟩
  have hbit : ∀ q : Fin n.toNat, ∃ u, (foRNuls n x.enc)[q.1]? = some u ∧ (u = 0 ∨ u = 1) := fun q => by
    rw [foRNuls_bit n x.enc q.2]; split <;> simp
  obtain ⟨u, hu, hu2⟩ := hbit i
  obtain ⟨u', hu', hu2'⟩ := hbit i'
  have hw := Array.getElem?_eq_getElem (show i.1 < _ by rw [hs]; exact i.2)
  have hw' := Array.getElem?_eq_getElem (show i'.1 < _ by rw [hs]; exact i'.2)
  simp only [seenKey, ascKeys, ascKey, nulCodes, nulWords, hof, Option.getD_some, List.append_nil] at hk
  cases hN : hasNul x.enc
  · have h0 := foRNuls_plain x.wf hN i.2
    have h0' := foRNuls_plain x.wf hN i'.2
    simp only [hN, Bool.false_eq_true, if_false, List.nil_append, List.map_cons, List.map_nil, List.cons.injEq,
      and_true, Array.getElem?_map, hw, hw', Option.map_some, Option.getD_some] at hk
    exact Opt.get_eq_of_raw x x hv hv i i' (h0.trans h0'.symm) fun _ hg a b ha hb hh => by
      rw [hw] at ha; rw [hw'] at hb; cases ha; cases hb; exact (ascOrd_atom hof hg hh).1 hk
  · simp only [hN, if_true, List.singleton_append, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      Array.getElem?_map, Array.getElem?_mapIdx, hu, hu', hw, hw', Option.map_some, Option.getD_some] at hk
    have huu : u = u' := by
      rcases hu2 with rfl | rfl <;> rcases hu2' with rfl | rfl <;> first | rfl | exact absurd hk.1 (by decide)
    subst huu
    refine Opt.get_eq_of_raw x x hv hv i i' (hu.trans hu'.symm) fun h0 hg a b ha hb hh => ?_
    rw [hu] at h0; cases h0
    rw [hw] at ha; rw [hw'] at hb; cases ha; cases hb
    exact (ascOrd_atom hof hg hh).1 (by simpa using hk.2)

/-- **A duplicate-free list inside another is no longer**: each element of `l₁` erased from `l₂` in turn. -/
theorem nodup_length_le {α : Type} [DecidableEq α] : ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ →
    l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, d, h => by
    obtain ⟨ha, d⟩ := List.nodup_cons.1 d
    have hm : a ∈ l₂ := h (List.mem_cons.2 (Or.inl rfl))
    have := nodup_length_le (l₂ := l₂.erase a) d fun x hx =>
      (List.mem_erase_of_ne fun e => ha (by rw [← e]; exact hx)).2 (h (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem hm] at this
    have := List.length_pos_of_mem hm
    simp only [List.length_cons]; omega

/-- **A duplicate-free list inside another is as long as it exactly when it holds all of it**: an element of `l₂`
missing from `l₁` leaves `l₁` inside `l₂` less that element (`nodup_length_le`). -/
theorem nodup_length_eq_iff {α : Type} [DecidableEq α] {l₁ l₂ : List α} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
    (h : l₁ ⊆ l₂) : l₁.length = l₂.length ↔ l₂ ⊆ l₁ :=
  ⟨fun e y hy => Classical.byContradiction fun hn => by
      have := nodup_length_le d₁ fun x hx => (List.mem_erase_of_ne (a := x) (b := y) fun e' => hn (by rw [← e']; exact hx)).2 (h hx)
      rw [List.length_erase_of_mem hy] at this
      have := List.length_pos_of_mem hy; omega,
   fun h' => Nat.le_antisymm (nodup_length_le d₁ h) (nodup_length_le d₂ h')⟩

/-- **Two lists ascending by a strict order `lt` with the same elements are equal**: their heads are each other's
least element. -/
theorem pairwise_eq_of_mem {α : Type} {lt : α → α → Prop} (hirr : ∀ x, ¬lt x x)
    (hasym : ∀ x y, lt x y → ¬lt y x) : ∀ {l l' : List α}, l.Pairwise lt → l'.Pairwise lt →
      (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, hm => absurd ((hm y).2 (List.mem_cons_self ..)) List.not_mem_nil
  | x :: _, [], _, _, hm => absurd ((hm x).1 (List.mem_cons_self ..)) List.not_mem_nil
  | x :: xs, y :: ys, h, h', hm => by
    rw [List.pairwise_cons] at h h'
    have exy : x = y := by
      rcases List.mem_cons.1 ((hm x).1 (List.mem_cons_self ..)) with e | hx; · exact e
      rcases List.mem_cons.1 ((hm y).2 (List.mem_cons_self ..)) with e | hy; · exact e.symm
      exact absurd (h.1 y hy) (hasym _ _ (h'.1 x hx))
    subst exy
    refine congrArg _ (pairwise_eq_of_mem hirr hasym h.2 h'.2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · rcases List.mem_cons.1 ((hm z).1 (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd (h.1 _ hz) (hirr _)
      · exact e
    · rcases List.mem_cons.1 ((hm z).2 (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd (h'.1 _ hz) (hirr _)
      · exact e

/-- The positions below `m` that pass `P`, ascending. -/
theorem exists_range_filter (m : Nat) (P : (j : Nat) → j < m → Prop) :
    ∃ L : List Nat, L.Pairwise (· < ·) ∧ ∀ j, j ∈ L ↔ ∃ hj : j < m, P j hj := by
  classical
  refine ⟨(List.range m).filter fun j => decide (∃ hj : j < m, P j hj), (pairwise_range m).filter _, fun j => ?_⟩
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A `flatMap` of blocks of one length is equal exactly where each block is. -/
theorem flatMap_eq_iff {α β : Type} {k : Nat} {F G : α → List β} (hF : ∀ a, (F a).length = k)
    (hG : ∀ a, (G a).length = k) : ∀ l : List α, l.flatMap F = l.flatMap G ↔ ∀ a ∈ l, F a = G a
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h; obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hF, hG])
      exact ⟨h1, (flatMap_eq_iff hF hG l).1 h2⟩
    · rintro ⟨h1, h2⟩; rw [h1, (flatMap_eq_iff hF hG l).2 h2]

/-- The positions below `c` in the window `[a, b)` are `range'` from the window's start clamped to `[0, c]`. -/
theorem filter_range_window (a b : Int) : ∀ c : Nat,
    (List.range c).filter (fun k : Nat => decide (a ≤ (k : Int) ∧ (k : Int) < b)) =
      List.range' (min (max a 0).toNat c) ((min b (c : Int)).toNat - min (max a 0).toNat c)
  | 0 => by simp; omega
  | c + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_window a b c]
    by_cases h : a ≤ (c : Int) ∧ (c : Int) < b
    · rw [List.filter_cons, List.filter_nil, if_pos (decide_eq_true h)]
      have e1 : min (max a 0).toNat (c + 1) = min (max a 0).toNat c := by omega
      have e2 : (min b ((c + 1 : Nat) : Int)).toNat - min (max a 0).toNat c =
          ((min b (c : Int)).toNat - min (max a 0).toNat c) + 1 := by omega
      rw [e1, e2, List.range'_concat]
      congr 2; omega
    · rw [List.filter_cons, List.filter_nil, if_neg fun e => h (of_decide_eq_true e), List.append_nil]
      by_cases h0 : (min b (c : Int)).toNat - min (max a 0).toNat c = 0
      · rw [h0, show (min b ((c + 1 : Nat) : Int)).toNat - min (max a 0).toNat (c + 1) = 0 by omega]; rfl
      · congr 1 <;> omega

/-- `filterMap` of an `if` is a `filter` then a `map`. -/
theorem filterMap_ite {α β : Type} (p : α → Bool) (g : α → β) : ∀ l : List α,
    l.filterMap (fun x => if p x then some (g x) else none) = (l.filter p).map g
  | [] => rfl
  | x :: l => by by_cases h : p x <;> simp [h, filterMap_ite p g l]

/-- Two runs of `g` from `s` and `s'` are equal exactly where they have one length and agree position by position. -/
theorem map_range'_eq_iff {β : Type} (g : Nat → β) (s l s' l' : Nat) :
    (List.range' s l).map g = (List.range' s' l').map g ↔ l = l' ∧ ∀ k < l, g (s + k) = g (s' + k) := by
  constructor
  · intro h
    have hl : l = l' := by simpa using congrArg List.length h
    subst hl
    refine ⟨rfl, fun k hk => ?_⟩
    have := congrArg (·[k]?) h
    simpa [List.getElem?_map, List.getElem?_range', hk] using this
  · rintro ⟨rfl, h⟩
    exact List.ext_getElem (by simp) fun k h1 _ => by simp at h1; simp [h k h1]

/-- `cellFns`' codes at two words, for any start `s` and length `len ≤ c`: equal exactly where the lengths are and the
payload codes `ks` agree element by element. -/
theorem cellBlocks_eq_iff (c : Nat) (s len : UInt64 → Nat) (ks : List (Array UInt64))
    (r r' : UInt64) (hr : len r ≤ c) (hr' : len r' ≤ c) :
    (List.range c).flatMap (fun j => (if j < len r then 1 else 0) ::
        ks.map (fun x => if j < len r then x[s r + j]?.getD 0 else 0)) =
      (List.range c).flatMap (fun j => (if j < len r' then 1 else 0) ::
        ks.map (fun x => if j < len r' then x[s r' + j]?.getD 0 else 0)) ↔
      len r = len r' ∧ ∀ k < len r, ks.map (·[s r + k]?.getD 0) = ks.map (·[s r' + k]?.getD 0) := by
  rw [flatMap_eq_iff (k := ks.length + 1) (by simp) (by simp)]
  simp only [List.mem_range, List.cons.injEq]
  constructor
  · intro h
    have hl : len r = len r' := by
      have h1 := fun j (hj : j < c) => (h j hj).1
      rcases Nat.lt_trichotomy (len r) (len r') with hlt | heq | hlt
      · have := h1 (len r) (by have := hr'; omega); simp [hlt] at this
      · exact heq
      · have := h1 (len r') (by have := hr; omega); simp [hlt] at this
    refine ⟨hl, fun k hk => ?_⟩
    have := (h k (by have := hr; omega)).2
    simpa [hk, show k < len r' by omega] using this
  · rintro ⟨hl, h⟩ j hj
    by_cases hk : j < len r
    · simpa [hk, show j < len r' by omega] using h j hk
    · simp [hk, show ¬ j < len r' by omega]

/-- **Equal codes of two cells** (`cellFns`): the cells the words `r` and `r'` name have one length and equal payload
codes `ks` element by element. -/
theorem cellFns_eq_iff (c : Nat) (lo hi : Array UInt64) (ks : List (Array UInt64)) (r r' : UInt64)
    (hr : cellLen lo hi r ≤ c) (hr' : cellLen lo hi r' ≤ c) :
    (cellFns c lo hi ks).map (· r) = (cellFns c lo hi ks).map (· r') ↔
      cellLen lo hi r = cellLen lo hi r' ∧ ∀ k < cellLen lo hi r,
        ks.map (·[cellStart lo r + k]?.getD 0) = ks.map (·[cellStart lo r' + k]?.getD 0) := by
  simp only [cellFns, List.map_flatMap, List.map_cons, List.map_map, Function.comp_def]
  exact cellBlocks_eq_iff c (cellStart lo) (cellLen lo hi) ks r r' hr hr'

/-- `Opt.get` at an `i64` column off a null: the raw word read as an `Int64` (`Arr.get_i64` at a column with nulls). -/
theorem Opt.get_i64 {n : USize} (x : Opt .i64 n) (i : Fin n.toNat) (h : x.isNul i = false) :
    x.get i = some ((Enc.raw .i64 n x.enc)[i.1]?.getD 0).toInt64 := by
  have hw := x.wf
  rw [Opt.get_ne x i (by decide), h]
  simp only [Bool.false_eq_true, if_false]
  congr 1
  clear h
  cases hc : x.enc <;> rw [hc] at hw <;>
    simp_all [Enc.WF, Enc.get, Enc.raw, QAtomicType.width, Column.atomOfBits, Dep.Carrier.of?, foRBits_starts]

/-- No row of the atom column `x` is flagged null (`foRNuls`): what `noNul` of a `cells` key's `lo` and `hi` answers. -/
def ColB.Flat {o : Bool} {t : QAtomicType} {n : USize} (x : ColB o t n) : Prop :=
  ∀ i : Fin n.toNat, (foRNuls n (ColB.enc x))[i.1]? = some 0

/-- **An `i64` column's row, `ColB.get`, with no row flagged null**: its raw word read as an `Int64`. -/
theorem ColB.get_i64 {o : Bool} {n : USize} (x : ColB o .i64 n) (hn : ColB.Flat x) (i : Fin n.toNat) :
    ColB.get x i = ((Enc.raw .i64 n (ColB.enc x))[i.1]?.getD 0).toInt64 := by
  cases o
  · exact Arr.get_i64 x i
  · have h := Opt.get_i64 x i ((Opt.isNul_eq_false x i).2 (hn i))
    simp only [ColB.get, h, Option.getD_some]
    try rfl

/-- A column with no row flagged null owns every row it is `OwnedOn`. -/
theorem ColB.owned_of_flat {n : USize} {P : Fin n.toNat → Prop} (x : ColB true .i64 n) (hn : ColB.Flat x)
    (hx : ColB.OwnedOn x P) (i : Fin n.toNat) : P i := by
  refine Classical.byContradiction fun hp => ?_
  have h0 : Opt.get x i = none := (hx i).2 hp
  rw [Opt.get_i64 x i ((Opt.isNul_eq_false x i).2 (hn i))] at h0
  cases h0

/-- A row of an `Opt` read as its element, where it is not null. -/
theorem Opt.get_eq_of_getD {t : QAtomicType} {n : USize} (x : Opt t n) (i i' : Fin n.toNat) (hi : x.get i ≠ none)
    (hi' : x.get i' ≠ none) (h : (x.get i).getD default = (x.get i').getD default) : x.get i = x.get i' := by
  cases h1 : x.get i with
  | none => exact absurd h1 hi
  | some a =>
    cases h2 : x.get i' with
    | none => exact absurd h2 hi'
    | some b => rw [h1, h2] at h; exact congrArg some h

/-- `noNul` answering leaves no row flagged null. -/
theorem noNul_flags {w : String} {t : QAtomicType} {m : USize} {e : Enc} (hw : Ext.Enc.WF t m e)
    (h : noNul w m e = .ok ()) {i : Nat} (hi : i < m.toNat) : (foRNuls m e)[i]? = some 0 := by
  unfold noNul at h
  by_cases hN : hasNul e = true
  · rw [if_pos hN] at h
    split at h
    · cases h
    · rename_i hn
      have hlt : i < (foRNuls m e).size := by rw [foRNuls_size]; exact hi
      have := Array.findIdx?_eq_none_iff.1 hn _ (Array.getElem_mem hlt)
      simp at this
      rw [Array.getElem?_eq_getElem hlt, this]
  · exact foRNuls_plain hw (Bool.eq_false_iff.2 hN) hi

/-- A `cells` column `kasc` reads has `lo` and `hi` without a null row: `ascCol` answers only past `noNul` of each. -/
theorem Verify.ascCol_cells_flags {m n c : USize} {lo hi e : Enc} {els : List (AscKey × Enc)} {xk}
    (h : ascCol m (.cells n c lo hi els, e) = .ok xk) :
    noNul "asc: cells lo" n lo = .ok () ∧ noNul "asc: cells hi" n hi = .ok () := by
  rw [ascCol] at h
  constructor
  · cases hl : noNul "asc: cells lo" n lo with
    | ok u => rfl
    | error s => exfalso; revert h; simp only [bind, Except.bind, hl]; repeat' (split <;> try simp_all)
  · cases hl : noNul "asc: cells hi" n hi with
    | ok u => rfl
    | error s => exfalso; revert h; simp only [bind, Except.bind, hl]; repeat' (split <;> try simp_all)

/-- **A cell of a `WF` side lies in its payload**: `cellStart` and `cellLen` read `0 ≤ lo ≤ hi ≤ c` as they are. -/
theorem ValsB.cell_le {o : Bool} {B : Obj} {n c : USize} {lo hi : ColB o .i64 n} {f : Vals B c} {P : Fin n.toNat → Prop}
    (hlo : ColB.Flat lo) (hhi : ColB.Flat hi) (hw : ValsB.WFOn (o := o) (A := .arr B) ⟨c, lo, hi, f⟩ P)
    (i : Fin n.toNat) (hp : P i) :
    cellStart (Enc.raw .i64 n (ColB.enc lo)) i.1.toUInt64 +
      cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i.1.toUInt64 ≤ c.toNat := by
  have hu : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  obtain ⟨h1, h2, h3⟩ := hw.2.2.1 i hp
  simp only [cellLen, cellStart, hu, ← ColB.get_i64 lo hlo, ← ColB.get_i64 hi hhi]; omega

/-- **An `arr` side's row is its cell**: the payload rows from `cellStart` for `cellLen` rows (`cellFns`' reading of
`lo` and `hi` at the row's own word), read through `f`; `ValsB.row`'s clamp to `[0, c)` is the identity on a `WF`
cell. -/
theorem ValsB.row_arr {o : Bool} {B : Obj} {n c : USize} {lo hi : ColB o .i64 n} {f : Vals B c} (hlo : ColB.Flat lo)
    (hhi : ColB.Flat hi) (i : Fin n.toNat)
    (hc : 0 ≤ (ColB.get lo i).toInt ∧ (ColB.get lo i).toInt ≤ (ColB.get hi i).toInt ∧
      (ColB.get hi i).toInt ≤ (c.toNat : Int)) :
    ValsB.row (o := o) (A := .arr B) ⟨c, lo, hi, f⟩ i =
      (List.range' (cellStart (Enc.raw .i64 n (ColB.enc lo)) i.1.toUInt64)
        (cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i.1.toUInt64)).map
        fun k => if h : k < c.toNat then ValsB.row f ⟨k, h⟩ else B.dflt := by
  have hu : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  have hfr : (List.finRange c.toNat).map Fin.val = List.range c.toNat := List.ext_getElem (by simp) (by simp)
  obtain ⟨h1, h2, h3⟩ := hc
  have hs : cellStart (Enc.raw .i64 n (ColB.enc lo)) i.1.toUInt64 = min (max (ColB.get lo i).toInt 0).toNat c.toNat := by
    simp only [cellStart, hu, ← ColB.get_i64 lo hlo]; omega
  have hl : cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i.1.toUInt64 =
      (min (ColB.get hi i).toInt (c.toNat : Int)).toNat - min (max (ColB.get lo i).toInt 0).toNat c.toNat := by
    simp only [cellLen, cellStart, hu, ← ColB.get_i64 lo hlo, ← ColB.get_i64 hi hhi]; omega
  rw [hs, hl]
  simp only [ValsB.row]
  rw [← filter_range_window, ← filterMap_ite, ← hfr, List.filterMap_map]
  exact congrArg (fun F => List.filterMap F _) (funext fun j => by simp [j.2])

/-- **A cell whose `lo` is its `hi` reads empty**, wherever it lies: no payload row is in `[lo, lo)`. -/
theorem Vals.row_empty {o : Bool} {B : Obj} {n c : USize} {lo hi : ColB o .i64 n} {f : Vals B c} (i : Fin n.toNat)
    (h : ColB.get lo i = ColB.get hi i) : ValsB.row (o := o) (A := .arr B) ⟨c, lo, hi, f⟩ i = [] := by
  simp only [ValsB.row, h]
  exact List.filterMap_eq_nil_iff.2 fun j _ => if_neg fun ⟨h1, h2⟩ => by omega

theorem Verify.ascCodes_mapM : ∀ {m : USize} {es : List (AscKey × Enc)} {ks},
    ascCodes m es = .ok ks → ∃ cs, es.mapM (ascCol m) = .ok cs
  | _, [], _, _ => ⟨[], rfl⟩
  | m, e :: es, ks, h => by
    rw [ascCodes] at h; simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc
    split at h; · cases h
    rename_i ks' hks
    obtain ⟨cs, hcs⟩ := ascCodes_mapM hks
    exact ⟨c :: cs, by simp [List.mapM_cons, hc, hcs, bind, Except.bind, pure, Except.pure]⟩

/-- A `cells` column `kasc` reads has a payload it reads: `ascCol` answers only where `ascCodes` does. -/
theorem Verify.ascCodes_of_cells {m n c : USize} {lo hi e : Enc} {els : List (AscKey × Enc)} {xk}
    (h : ascCol m (.cells n c lo hi els, e) = .ok xk) : ∃ ks, ascCodes c els = .ok ks := by
  rw [ascCol] at h
  cases hks : ascCodes c els with
  | ok ks => exact ⟨ks, rfl⟩
  | error s =>
    -- every step before `ascCodes` only fails or passes, and past them `ascCodes`' error is the answer
    exfalso; revert h; simp only [bind, Except.bind]
    repeat' (split <;> try simp_all)

/-- What `ValsB.cols` answers at an `arr` side, unfolded: one `cells` key over the payload's columns `fs`, which `kasc`
reads; two rows have equal codes exactly where their cells have one length and equal payload codes element by
element (`cellFns_eq_iff`). -/
theorem ValsB.cols_arr {o : Bool} {B : Obj} {n c : USize} {lo hi : ColB o .i64 n} {f : Vals B c}
    {P : Fin n.toNat → Prop} {es : List (AscKey × Enc)} {cs}
    (hw : ValsB.WFOn (o := o) (A := .arr B) ⟨c, lo, hi, f⟩ P)
    (hes : ValsB.cols (o := o) (A := .arr B) ⟨c, lo, hi, f⟩ = .ok es) (hc : es.mapM (ascCol n) = .ok cs) :
    ColB.Flat lo ∧ ColB.Flat hi ∧ ∃ fs, ValsB.cols f = .ok fs ∧ (∃ cs', fs.mapM (ascCol c) = .ok cs') ∧
      ∀ i i' : Fin n.toNat, P i → P i' →
      (seenKey n es i = seenKey n es i' ↔
        cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i.1.toUInt64 =
          cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i'.1.toUInt64 ∧
        ∀ k < cellLen (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) i.1.toUInt64,
          seenKey c fs (cellStart (Enc.raw .i64 n (ColB.enc lo)) i.1.toUInt64 + k) =
            seenKey c fs (cellStart (Enc.raw .i64 n (ColB.enc lo)) i'.1.toUInt64 + k)) := by
  simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at hes
  split at hes; · cases hes
  rename_i fs hfs
  cases hes
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨ks, hks⟩ := ascCodes_of_cells hac
  obtain ⟨hnl, hnh⟩ := Verify.ascCol_cells_flags hac
  have hlo : ColB.Flat lo := fun i => noNul_flags (ColB.enc_wf lo) hnl i.2
  have hhi : ColB.Flat hi := fun i => noNul_flags (ColB.enc_wf hi) hnh i.2
  refine ⟨hlo, hhi, fs, hfs, ascCodes_mapM hks, fun i i' hp hp' => ?_⟩
  have hr : ∀ q : Fin n.toNat, seenKey n [(AscKey.cells n c (ColB.enc lo) (ColB.enc hi) fs, .pos)] q =
      (cellFns c.toNat (Enc.raw .i64 n (ColB.enc lo)) (Enc.raw .i64 n (ColB.enc hi)) (ascKeys c fs)).map
        (· q.1.toUInt64) :=
    fun q => by simp [seenKey, ascKeys, ascKey, nulCodes, nulWords, hasNul, List.map_map, Function.comp_def, Enc.raw, q.2]
  have h1 := ValsB.cell_le hlo hhi hw i hp; have h2 := ValsB.cell_le hlo hhi hw i' hp'
  rw [hr, hr, cellFns_eq_iff _ _ _ _ _ _ (by omega) (by omega)]
  rfl

/-- **Equal order codes, equal rows**, over any side whose columns `kasc` reads (`ascCol` answers on each): the codes
of row `i` and row `i'` agree in every column (`seenKey`), so their atoms do (`ascOrd_atom`), so their elements do
(`Arr.get_eq_of_raw`). -/
theorem ValsB.row_of_codes : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → (P : Fin n.toNat → Prop) →
    ValsB.WFOn x P → {es : List (AscKey × Enc)} → ValsB.cols x = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs →
    ∀ i i' : Fin n.toNat, P i → P i' → seenKey n es i = seenKey n es i' → ValsB.row x i = ValsB.row x i'
  | o, .atom t, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp', hk => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes
    cases o
    · exact (Arr.eq_of_codes x hc).2 i i' hk
    · exact congrArg (·.getD default) ((Opt.eq_of_codes x hc).2 i i' hk)
  | _, .prod _ _, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp', hk => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys_append]
    rw [hs, hs] at hk
    obtain ⟨k1, k2⟩ := List.append_inj hk (by simp [seenKey])
    show (ValsB.row x.1 i, ValsB.row x.2 i) = (ValsB.row x.1 i', ValsB.row x.2 i')
    rw [ValsB.row_of_codes x.1 P hw.1 h1 hc1 i i' hp hp' k1, ValsB.row_of_codes x.2 P hw.2 h2 hc2 i i' hp hp' k2]
  | _, .arr _, n, ⟨c, lo, hi, f⟩, P, hw, es, hes, cs, hc, i, i', hp, hp', hk => by
    obtain ⟨hlo, hhi, fs, hfs, ⟨cs', hcs'⟩, hkey⟩ := ValsB.cols_arr hw hes hc
    obtain ⟨hl, hk⟩ := (hkey i i' hp hp').1 hk
    have b := hw.2.2.1
    rw [ValsB.row_arr hlo hhi i (b i hp), ValsB.row_arr hlo hhi i' (b i' hp'), map_range'_eq_iff]
    refine ⟨hl, fun k hkl => ?_⟩
    have b1 := hkl; have b2 := hl ▸ hkl
    have c1 := ValsB.cell_le hlo hhi hw i hp; have c2 := ValsB.cell_le hlo hhi hw i' hp'
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact ValsB.row_of_codes f (fun _ => True) hw.2.2.2 hfs hcs' _ _ trivial trivial (hk k hkl)
  | _, .sum _ _, n, s, P, hw, es, hes, cs, hc, i, i', hp, hp', hk => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩
    · simp only [ValsB.cols, hv, Except.ok.injEq] at hes; subst hes
      simp only [ValsB.row, hv, (Opt.eq_of_codes x hc).2 i i' hk]
    simp only [ValsB.WFOn, hv] at hw
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := ValsB.cols_sum hv hes
    obtain ⟨c0, c12, hc0, hc12, -⟩ := mapM_append_ok (l1 := [(.atom .u1, tag.enc)]) (l2 := xs ++ ys) hc
    obtain ⟨c1, c2, hc1, hc2, -⟩ := mapM_append_ok hc12
    obtain ⟨hvt, heq⟩ := Arr.eq_of_codes tag hc0
    have hs : ∀ (e1 e2 : List (AscKey × Enc)) q, seenKey n (e1 ++ e2) q = seenKey n e1 q ++ seenKey n e2 q :=
      fun _ _ q => by simp [seenKey, ascKeys_append]
    rw [show (AscKey.atom .u1, tag.enc) :: (xs ++ ys) = [(AscKey.atom .u1, tag.enc)] ++ (xs ++ ys) from rfl,
      hs, hs, hs, hs] at hk
    obtain ⟨k0, k12⟩ := List.append_inj hk (by simp [seenKey, ascKeys])
    obtain ⟨k1, k2⟩ := List.append_inj k12 (by simp [seenKey])
    have ht := heq i i' k0
    simp only [ValsB.row, hv, ht]
    cases htt : tag.get i'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ValsB.row_of_codes x _ hw.2.1 hxs hc1 i i' ⟨hp, ht.trans htt⟩ ⟨hp', htt⟩ k1]
    · simp only [↓reduceIte]
      rw [ValsB.row_of_codes y _ hw.2.2 hys hc2 i i' ⟨hp, ht.trans htt⟩ ⟨hp', htt⟩ k2]
  | _, .one, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl

/-- **`Arr.get_eq_of_raw`'s converse**: where two `Arr`s of one type in a column every kernel reads hold one element
at `i` and `j`, their raw words `a`, `b` there read as one atom; and a `u1` word is below `2`, the bound every `Arr`
keeps. -/
theorem Arr.atom_of_get_eq {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hx : Kernel.Enc.Valid n x.enc) (hy : Kernel.Enc.Valid m y.enc) (i : Fin n.toNat) (j : Fin m.toNat)
    (hg : t ≠ .general) {a b : UInt64} (ha : (Enc.raw .i64 n x.enc)[i.1]? = some a)
    (hb : (Enc.raw .i64 m y.enc)[j.1]? = some b) :
    (t = .u1 → a < 2 ∧ b < 2) ∧ (x.get i = y.get j → Column.atomOfBits t a hg = Column.atomOfBits t b hg) := by
  -- an element is `Carrier.of?` of its word's atom (`Arr.get_raw_atom`, any encoding), which keeps the atom
  obtain ⟨a', ha', hua, ex⟩ := Arr.get_raw_atom x hg i
  obtain ⟨b', hb', hub, ey⟩ := Arr.get_raw_atom y hg j
  obtain rfl := Option.some.inj (ha.symm.trans ha'); obtain rfl := Option.some.inj (hb.symm.trans hb')
  refine ⟨fun hu => ⟨hua hu, hub hu⟩, fun h => ?_⟩
  rw [ex, ey] at h
  cases t <;> first | exact absurd rfl hg | simp_all [Column.atomOfBits, Dep.Carrier.of?]

/-- **Equal elements of one column, equal order codes**, `Arr.eq_of_codes`' converse: equal elements are equal atoms
(`Arr.atom_of_get_eq`), which have equal codes (`ascOrd_atom`). -/
theorem Arr.codes_of_eq {t : QAtomicType} {n : USize} (x : Arr t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat) (hr : x.get i = x.get i') :
    seenKey n [(.atom t, x.enc)] i = seenKey n [(.atom t, x.enc)] i' := by
    obtain ⟨hlen, hf⟩ := mapM_ok hc
    have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
    obtain ⟨hraw, hsz, -, hat⟩ := ascCol_ok hac
    obtain ⟨f, hof⟩ := hat t rfl
    have hv := ascCol_valid hac
    dsimp only at hof hv
    have hs : (Enc.raw .i64 n (Arr.enc (t := t) x)).size = n.toNat := by rw [← hraw]; exact hsz
    have hg : t ≠ .general := by rintro rfl; simp [ascOrd, ascLayout, orderKind] at hof
    have hi := Array.getElem?_eq_getElem (show i.1 < _ by rw [hs]; exact i.2)
    have hi' := Array.getElem?_eq_getElem (show i'.1 < _ by rw [hs]; exact i'.2)
    obtain ⟨hu, he⟩ := Arr.atom_of_get_eq x x hv hv i i' hg hi hi'
    simp only [seenKey, ascKeys, ascKey, nulCodes, nulWords, Arr.plain, Bool.false_eq_true, if_false, List.nil_append, List.append_nil, List.map_cons, List.map_nil, hof, Option.getD_some, Array.getElem?_map, hi, hi',
      Option.map_some]
    exact congrArg (· :: []) ((ascOrd_atom hof hg hu).2 (he hr))

/-- **Equal elements of an `Opt`, equal order codes**, `Opt.eq_of_codes`' converse: equal elements are both null
(one flag, code `0`) or both one atom (`ascOrd_atom`), and `nulCodes_row` reads no more. -/
theorem Opt.codes_of_eq {t : QAtomicType} {n : USize} (x : Opt t n) {cs}
    (hc : [(.atom t, x.enc)].mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat) (hr : x.get i = x.get i') :
    seenKey n [(.atom t, x.enc)] i = seenKey n [(.atom t, x.enc)] i' := by
  obtain ⟨hlen, hf⟩ := mapM_ok hc
  have hac := hf 0 _ (cs[0]'(by simp at hlen; omega)) rfl (List.getElem?_eq_getElem _)
  obtain ⟨hraw, hsz, -, hat⟩ := ascCol_ok hac
  obtain ⟨f, hof⟩ := hat t rfl
  have hv := ascCol_valid hac
  dsimp only at hof hv hraw
  have hs : (Enc.raw .i64 n x.enc).size = n.toNat := by rw [← hraw]; exact hsz
  have hg : t ≠ .general := by rintro rfl; simp [ascOrd, ascLayout, orderKind] at hof
  have hw := Array.getElem?_eq_getElem (show i.1 < _ by rw [hs]; exact i.2)
  have hw' := Array.getElem?_eq_getElem (show i'.1 < _ by rw [hs]; exact i'.2)
  have hbit : ∀ q : Fin n.toNat, x.isNul q = true → (foRNuls n x.enc)[q.1]? = some 1 := fun q h => by
    have h1 := foRNuls_bit n x.enc q.2
    have h2 : (foRNuls n x.enc)[q.1]? ≠ some 0 := fun e => absurd ((Opt.isNul_eq_false x q).2 e) (by simp [h])
    rw [h1] at h2 ⊢; split at h2 <;> simp_all
  rw [Opt.get_ne x i hg, Opt.get_ne x i' hg] at hr
  -- equal elements: one flag, and off a null one atom
  have key : (foRNuls n x.enc)[i.1]? = (foRNuls n x.enc)[i'.1]? ∧
      ((foRNuls n x.enc)[i.1]? = some 0 → f (Enc.raw .i64 n x.enc)[i.1] = f (Enc.raw .i64 n x.enc)[i'.1]) := by
    cases h1 : x.isNul i <;> cases h2 : x.isNul i' <;> simp only [h1, h2, Bool.false_eq_true, if_false, if_true,
      reduceCtorEq] at hr
    · have e1 := (Opt.isNul_eq_false x i).1 h1
      have e2 := (Opt.isNul_eq_false x i').1 h2
      refine ⟨e1.trans e2.symm, fun _ => ?_⟩
      obtain ⟨a, ha, hua, ex⟩ := Enc.get_raw_atom x.wf hg i e1
      obtain ⟨b, hb, hub, ey⟩ := Enc.get_raw_atom x.wf hg i' e2
      rw [hw] at ha; rw [hw'] at hb; cases ha; cases hb
      rw [Option.some.injEq, ex, ey] at hr
      refine (ascOrd_atom hof hg fun hu => ⟨hua hu, hub hu⟩).2 ?_
      cases t <;> first | exact absurd rfl hg | simp_all [Column.atomOfBits, Dep.Carrier.of?]
    · exact ⟨(hbit i h1).trans (hbit i' h2).symm, fun e => by rw [hbit i h1] at e; cases e⟩
  simp only [seenKey, ascKeys, ascKey, hof, Option.getD_some, List.append_nil]
  rw [← Array.map_id (Array.map f (Enc.raw .i64 n x.enc))]
  refine nulCodes_row rfl key.1 ?_
  unfold nulWords; split
  · simp only [Array.getElem?_mapIdx, Array.getElem?_map, hw, hw', Option.map_some, ← key.1]
    cases hq : (foRNuls n x.enc)[i.1]?.getD 0 == 0 <;> simp only [if_true, Bool.false_eq_true, if_false]
    have hz : (foRNuls n x.enc)[i.1]?.getD 0 = 0 := by simpa using hq
    rw [key.2 (by rw [foRNuls_bit n x.enc i.2, hz]; rfl)]
  · rename_i hN
    simp only [Array.getElem?_map, hw, hw', Option.map_some,
      key.2 (foRNuls_plain x.wf (Bool.eq_false_iff.2 hN) i.2)]

/-- **Two rows a summand does not own have equal order codes**: each leaf there is the in-band null, and an `arr` summand
has no unowned row `kasc` reads (its `lo` has no null row, `ColB.owned_of_flat`). -/
theorem ValsB.codes_of_unowned : {A : Obj} → {n : USize} → (x : ValsB true A n) → (P : Fin n.toNat → Prop) →
    ValsB.WFOn x P → {es : List (AscKey × Enc)} → ValsB.cols x = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs →
    ∀ i i' : Fin n.toNat, ¬P i → ¬P i' → seenKey n es i = seenKey n es i'
  | .atom t, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp' => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes
    have hx : ∀ i, (P i → Opt.get x i ≠ none) ∧ (¬P i → Opt.get x i = Opt.filler t) := hw
    exact Opt.codes_of_eq x hc i i' (by rw [(hx i).2 hp, (hx i').2 hp'])
  | .prod _ _, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp' => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys_append]
    rw [hs, hs, ValsB.codes_of_unowned x.1 P hw.1 h1 hc1 i i' hp hp', ValsB.codes_of_unowned x.2 P hw.2 h2 hc2 i i' hp hp']
  | .arr _, n, ⟨c, lo, hi, f⟩, P, hw, es, hes, cs, hc, i, i', hp, hp' => by
    obtain ⟨hlo, -⟩ := ValsB.cols_arr hw hes hc
    exact absurd (ColB.owned_of_flat lo hlo hw.1 i) hp
  | .sum _ _, n, s, P, hw, es, hes, cs, hc, i, i', hp, hp' => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩
    · simp only [ValsB.cols, hv, Except.ok.injEq] at hes; subst hes
      simp only [ValsB.WFOn, hv] at hw
      exact Opt.codes_of_eq x hc i i' (by rw [hw i hp, hw i' hp'])
    simp only [ValsB.WFOn, hv] at hw
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := ValsB.cols_sum hv hes
    obtain ⟨c0, c12, hc0, hc12, -⟩ := mapM_append_ok (l1 := [(.atom .u1, tag.enc)]) (l2 := xs ++ ys) hc
    obtain ⟨c1, c2, hc1, hc2, -⟩ := mapM_append_ok hc12
    have hs : ∀ (e1 e2 : List (AscKey × Enc)) q, seenKey n (e1 ++ e2) q = seenKey n e1 q ++ seenKey n e2 q :=
      fun _ _ q => by simp [seenKey, ascKeys_append]
    have t1 := hw.1 i hp
    have t2 := hw.1 i' hp'
    rw [show (AscKey.atom .u1, tag.enc) :: (xs ++ ys) = [(AscKey.atom .u1, tag.enc)] ++ (xs ++ ys) from rfl,
      hs, hs, hs, hs, Arr.codes_of_eq tag hc0 i i' (t1.trans t2.symm),
      ValsB.codes_of_unowned x _ hw.2.1 hxs hc1 i i' (fun h => hp h.1) (fun h => hp' h.1),
      ValsB.codes_of_unowned y _ hw.2.2 hys hc2 i i' (fun h => hp h.1) (fun h => hp' h.1)]
  | .one, n, _, _, _, es, hes, _, _, _, _, _, _ => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes; simp [seenKey, ascKeys]

/-- **Equal rows, equal order codes**, `ValsB.row_of_codes`' converse, over the rows `P` owns. -/
theorem ValsB.codes_of_row : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → (P : Fin n.toNat → Prop) →
    ValsB.WFOn x P → {es : List (AscKey × Enc)} → ValsB.cols x = .ok es → ∀ {cs}, es.mapM (ascCol n) = .ok cs →
    ∀ i i' : Fin n.toNat, P i → P i' → ValsB.row x i = ValsB.row x i' → seenKey n es i = seenKey n es i'
  | o, .atom t, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp', hr => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes
    cases o
    · exact Arr.codes_of_eq x hc i i' hr
    · have hx : ∀ i, Opt.get x i = none ↔ ¬P i := hw
      exact Opt.codes_of_eq x hc i i' (Opt.get_eq_of_getD x i i' (fun h => (hx i).1 h hp) (fun h => (hx i').1 h hp') hr)
  | _, .prod _ _, n, x, P, hw, es, hes, cs, hc, i, i', hp, hp', hr => by
    simp only [ValsB.cols, bind, Except.bind, pure, Except.pure] at hes
    split at hes; · cases hes
    rename_i es1 h1
    split at hes; · cases hes
    rename_i es2 h2
    cases hes
    obtain ⟨cs1, cs2, hc1, hc2, -⟩ := mapM_append_ok hc
    obtain ⟨r1, r2⟩ := Prod.mk.inj (show (ValsB.row x.1 i, ValsB.row x.2 i) = (ValsB.row x.1 i', ValsB.row x.2 i') from hr)
    have hs : ∀ q, seenKey n (es1 ++ es2) q = seenKey n es1 q ++ seenKey n es2 q := fun q => by
      simp [seenKey, ascKeys_append]
    rw [hs, hs, ValsB.codes_of_row x.1 P hw.1 h1 hc1 i i' hp hp' r1, ValsB.codes_of_row x.2 P hw.2 h2 hc2 i i' hp hp' r2]
  | _, .arr _, n, ⟨c, lo, hi, f⟩, P, hw, es, hes, cs, hc, i, i', hp, hp', hr => by
    obtain ⟨hlo, hhi, fs, hfs, ⟨cs', hcs'⟩, hkey⟩ := ValsB.cols_arr hw hes hc
    have b := hw.2.2.1
    rw [ValsB.row_arr hlo hhi i (b i hp), ValsB.row_arr hlo hhi i' (b i' hp'), map_range'_eq_iff] at hr
    refine (hkey i i' hp hp').2 ⟨hr.1, fun k hkl => ?_⟩
    have b1 := hkl; have b2 := hr.1 ▸ hkl
    have c1 := ValsB.cell_le hlo hhi hw i hp; have c2 := ValsB.cell_le hlo hhi hw i' hp'
    have e := hr.2 k hkl
    rw [dif_pos (by omega), dif_pos (by omega)] at e
    exact ValsB.codes_of_row f (fun _ => True) hw.2.2.2 hfs hcs' _ _ trivial trivial e
  | _, .sum _ _, n, s, P, hw, es, hes, cs, hc, i, i', hp, hp', hr => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩
    · simp only [ValsB.cols, hv, Except.ok.injEq] at hes; subst hes
      simp only [ValsB.row, hv] at hr
      exact Opt.codes_of_eq x hc i i' (by simpa only [Obj.optOf_optEl] using congrArg (Obj.optOf hb) hr)
    simp only [ValsB.WFOn, hv] at hw
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := ValsB.cols_sum hv hes
    obtain ⟨c0, c12, hc0, hc12, -⟩ := mapM_append_ok (l1 := [(.atom .u1, tag.enc)]) (l2 := xs ++ ys) hc
    obtain ⟨c1, c2, hc1, hc2, -⟩ := mapM_append_ok hc12
    have hs : ∀ (e1 e2 : List (AscKey × Enc)) q, seenKey n (e1 ++ e2) q = seenKey n e1 q ++ seenKey n e2 q :=
      fun _ _ q => by simp [seenKey, ascKeys_append]
    simp only [ValsB.row, hv] at hr
    -- equal rows sit in one summand; in the other both rows are unowned
    have ht : tag.get i = tag.get i' := by revert hr; cases tag.get i <;> cases tag.get i' <;> simp
    have k1 : seenKey n xs i = seenKey n xs i' := by
      cases htt : tag.get i'
      · exact ValsB.codes_of_row x _ hw.2.1 hxs hc1 i i' ⟨hp, ht.trans htt⟩ ⟨hp', htt⟩ (by simpa [ht, htt] using hr)
      · exact ValsB.codes_of_unowned x _ hw.2.1 hxs hc1 i i' (fun h => by simp [ht.trans htt] at h)
          (fun h => by simp [htt] at h)
    have k2 : seenKey n ys i = seenKey n ys i' := by
      cases htt : tag.get i'
      · exact ValsB.codes_of_unowned y _ hw.2.2 hys hc2 i i' (fun h => by simp [ht.trans htt] at h)
          (fun h => by simp [htt] at h)
      · exact ValsB.codes_of_row y _ hw.2.2 hys hc2 i i' ⟨hp, ht.trans htt⟩ ⟨hp', htt⟩ (by simpa [ht, htt] using hr)
    rw [show (AscKey.atom .u1, tag.enc) :: (xs ++ ys) = [(AscKey.atom .u1, tag.enc)] ++ (xs ++ ys) from rfl,
      hs, hs, hs, hs, Arr.codes_of_eq tag hc0 i i' ht, k1, k2]
  | _, .one, n, _, _, _, es, hes, _, _, _, _, _, _, _ => by
    simp only [ValsB.cols, Except.ok.injEq] at hes; subst hes; simp [seenKey, ascKeys]

/-- **Rows of `x` are equal iff their order codes are** where `Vals.nub x` answers: `kasc` read every column
(`Vals.row_of_codes`, `Vals.codes_of_row`). -/
theorem Vals.seenKey_iff_row {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m}
    (h : Vals.nub x = .ok r) (hw : Vals.WF x) {es} (hes : ValsB.cols x = .ok es) (i i' : Fin n.toNat) :
    seenKey n es i = seenKey n es i' ↔ x.row i = x.row i' := by
  obtain ⟨es', _, _, _, _, _, _, _, hes', ha, -⟩ := Vals.nub_ok h
  obtain rfl : es = es' := Except.ok.inj (hes.symm.trans hes')
  obtain ⟨cs, hc, -⟩ := kasc_ok ha
  exact ⟨fun hk => ValsB.row_of_codes x _ hw hes hc i i' trivial trivial hk,
    fun hr => ValsB.codes_of_row x _ hw hes hc i i' trivial trivial hr⟩

/-- **Rows of `x` with equal order codes are equal** where `Vals.nub x` answers. -/
theorem Vals.row_of_seenKey {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m}
    (h : Vals.nub x = .ok r) (hw : Vals.WF x) {es} (hes : ValsB.cols x = .ok es) (i i' : Fin n.toNat)
    (hk : seenKey n es i = seenKey n es i') : x.row i = x.row i' := (Vals.seenKey_iff_row h hw hes i i').1 hk

/-- **Equal rows of `x` have equal order codes** where `Vals.nub x` answers. -/
theorem Vals.seenKey_of_row {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m}
    (h : Vals.nub x = .ok r) (hw : Vals.WF x) {es} (hes : ValsB.cols x = .ok es) (i i' : Fin n.toNat)
    (hr : x.row i = x.row i') : seenKey n es i = seenKey n es i' := (Vals.seenKey_iff_row h hw hes i i').2 hr

/-- **`Vals.nub x` holds exactly `x`'s rows**: `Vals.nub_sub` one way, `Vals.nub_cover` with `Vals.row_of_seenKey`
the other. -/
theorem Vals.nub_rows {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    (hw : Vals.WF x) (a : A.El) : (∃ j, ValsB.row r.2 j = a) ↔ ∃ i, ValsB.row x i = a := by
  obtain ⟨es, _, _, _, _, _, _, _, hes, _⟩ := Vals.nub_ok h
  constructor
  · rintro ⟨j, rfl⟩; obtain ⟨i, hi⟩ := Vals.nub_sub h j; exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩; obtain ⟨j, i', h1, h2⟩ := Vals.nub_cover h hes i
    exact ⟨j, h1.trans (Vals.row_of_seenKey h hw hes i' i h2)⟩

/-- **Which input row each row of `Vals.nub x` is**: `kasc`'s permutation `ps` (its grade by the codes `ascKeys`),
`K` the sorted rows' keys (`K q` the key of input row `ps[q]`), and row `j` of the answer input row `ps[F[j]]`, `F` the
first rows of `K` (`firstsOf`, `k` of them). -/
theorem Vals.nub_sel {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (AscKey × Enc)} (hes : ValsB.cols x = .ok es) :
    ∃ (ps : List Nat) (K : Nat → List UInt64), ps = ascGrade n.toNat (ascKeys n es) ∧
      (∀ q (hq : q < ps.length), K q = seenKey n es ps[q]) ∧ r.1.toNat = (firstsOf K n.toNat).length ∧
      ∀ j : Fin r.1.toNat, ∃ i : Fin n.toNat, ValsB.row r.2 j = ValsB.row x i ∧
        ((firstsOf K n.toNat)[j.1]?.bind (ps[·]?)) = some i.1 := by
  obtain ⟨es', vs, p, k, g, f, ix, y, hes', ha, hs, hix, hy, rfl⟩ := Vals.nub_ok h
  have hee : es = es' := Except.ok.inj (hes.symm.trans hes'); subst hee
  obtain ⟨ps, hp, hperm, -, -⟩ := asc_perm n es vs p ha
  obtain ⟨hk, -, hf⟩ := kseen_ok hs
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hpsg := asc_perm_grade ha hp hperm
  have hkey := Vals.sorted_key hes ha hp hperm
  generalize seenKey n ((es.map (·.1)).zip vs) = K at hk hf hkey
  have hkn : k ≤ n.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  refine ⟨ps, K, hpsg, hkey, by rw [hkU, hk], fun j => ?_⟩
  have hgl : j.1 < (firstsOf K n.toNat).length := by have h2 : j.1 < k.toUSize.toNat := j.2; omega
  obtain ⟨i', e1, r1⟩ := ValsB.gather_row x hy j
  refine ⟨i', r1, ?_⟩
  -- `ix[j]` is `ps[firsts[j]]`
  obtain ⟨his, hps, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 k.toUSize f = ((firstsOf K n.toNat).map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hkU, hk]; simp)).2.1
  have hri : Enc.raw .i64 k.toUSize ix = (((firstsOf K n.toNat).map Nat.toUInt64).toArray.map fun w =>
      ((ps.map Nat.toUInt64).toArray)[w.toNat]?.getD 0) := by
    rw [kgather_plain hix (by rw [hp]; exact hasNul_wordsFoR _), (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1,
      hrf, hrp]
  have hq' : (firstsOf K n.toNat)[j.1] < n.toNat := firsts_lt K n.toNat (List.getElem_mem hgl)
  have hfG : (firstsOf K n.toNat)[j.1] < ps.length := by omega
  rw [List.getElem?_eq_getElem hgl, Option.bind_some, List.getElem?_eq_getElem hfG, ← e1, hri]
  simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hgl,
    Option.map_some, Option.getD_some, hc64 _ hq', List.getElem?_eq_getElem hfG]
  exact congrArg some (hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hfG)))).symm

/-- **The groups' first rows ascend, with unequal codes**: with `ps` the grade of the codes (`ascGrade`) and `K q` the
code of input row `ps[q]`, groups `G < G'` have first input rows `i`, `i'` (`ps` at `firstsOf K`) ascending in
`lexLe`, no two with one code (`firsts_spec`). -/
theorem Verify.firsts_sorted {n : USize} {es : List (AscKey × Enc)} {K : Nat → List UInt64}
    (hkey : ∀ q (hq : q < (ascGrade n.toNat (ascKeys n es)).length),
      K q = seenKey n es (ascGrade n.toNat (ascKeys n es))[q])
    {G G' i i' : Nat} (hGG : G < G')
    (e : (firstsOf K n.toNat)[G]?.bind ((ascGrade n.toNat (ascKeys n es))[·]?) = some i)
    (e' : (firstsOf K n.toNat)[G']?.bind ((ascGrade n.toNat (ascKeys n es))[·]?) = some i') :
    lexLe (ascKeys n es) i i' = true ∧ seenKey n es i ≠ seenKey n es i' := by
  obtain ⟨hperm, hsort⟩ := ascGrade_spec n.toNat (ascKeys n es)
  generalize ascGrade n.toNat (ascKeys n es) = ps at hperm hsort hkey e e'
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have fs := firsts_spec K n.toNat
  have pick : ∀ {G i}, (firstsOf K n.toNat)[G]?.bind (ps[·]?) = some i →
      ∃ hG : G < (firstsOf K n.toNat).length, ∃ hf : (firstsOf K n.toNat)[G] < ps.length, ps[(firstsOf K n.toNat)[G]] = i := by
    intro G i e
    cases h : (firstsOf K n.toNat)[G]? with
    | none => rw [h] at e; cases e
    | some f =>
      rw [h] at e
      obtain ⟨hG, rfl⟩ := List.getElem?_eq_some_iff.1 h
      obtain ⟨hf, rfl⟩ := List.getElem?_eq_some_iff.1 e
      exact ⟨hG, hf, rfl⟩
  obtain ⟨hj, hf, rfl⟩ := pick e
  obtain ⟨hj', hf', rfl⟩ := pick e'
  have hlt : (firstsOf K n.toNat)[G] < (firstsOf K n.toNat)[G'] := List.pairwise_iff_getElem.1 fs.1 _ _ hj hj' hGG
  refine ⟨(List.pairwise_iff_getElem.1 hsort _ _ hf hf' hlt).1, fun hk => ?_⟩
  replace hk : K (firstsOf K n.toNat)[G] = K (firstsOf K n.toNat)[G'] := by rw [hkey _ hf, hkey _ hf']; exact hk
  have g := (fs.2.2.1 _ (by omega) _ (by omega)).2 hk
  rw [fs.2.2.2.1 _ hj, fs.2.2.2.1 _ hj'] at g; omega

/-- **`Vals.nub x` is sorted and has no two rows with one key**: its rows are input rows `sel j`, ascending in `kasc`'s
order of their codes (`lexLe` over `ascKeys`), no two with equal codes (`seenKey`). -/
theorem Vals.nub_sorted {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (AscKey × Enc)} (hes : ValsB.cols x = .ok es) :
    ∃ sel : Fin r.1.toNat → Fin n.toNat, (∀ j, ValsB.row r.2 j = ValsB.row x (sel j)) ∧
      ∀ j j' : Fin r.1.toNat, j.1 < j'.1 → lexLe (ascKeys n es) (sel j) (sel j') = true ∧
        seenKey n es (sel j) ≠ seenKey n es (sel j') := by
  obtain ⟨ps, K, hps, hkey, -, hsel⟩ := Vals.nub_sel h hes
  obtain ⟨sel, hs⟩ := Classical.axiomOfChoice hsel
  subst hps
  exact ⟨sel, fun j => (hs j).1, fun j j' hjj => Verify.firsts_sorted hkey hjj (hs j).2 (hs j').2⟩

/-- **The rows of `Vals.nub x` are pairwise distinct**: two of them are input rows with unequal codes
(`Vals.nub_sorted`), so unequal rows (`Vals.seenKey_of_row`). -/
theorem Vals.nub_distinct {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    (hw : Vals.WF x) {j j' : Fin r.1.toNat} (hjj : j ≠ j') : ValsB.row r.2 j ≠ ValsB.row r.2 j' := by
  obtain ⟨es, _, _, _, _, _, _, _, hes, _⟩ := Vals.nub_ok h
  obtain ⟨sel, hs, hlt⟩ := Vals.nub_sorted h hes
  intro e
  rw [hs, hs] at e
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hjj) with l | l
  · exact (hlt j j' l).2 (Vals.seenKey_of_row h hw hes _ _ e)
  · exact (hlt j' j l).2 (Vals.seenKey_of_row h hw hes _ _ e.symm)

namespace Tab
variable {k v : Obj}

/-- **`R.canon` denotes `R`**. -/
theorem canon_holds {R S : Tab k v} (h : R.canon = .ok S) (hw : R.WF) (a : k.El) (b : v.El) : S.Holds a b ↔ R.Holds a b := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn hw (a, b)
    simp only [Tab.Holds, ValsB.row, Prod.mk.injEq] at this ⊢
    exact this

/-- **`R.ran` denotes `𝟙 ∩ R° ≫ R°°`** (`CRel.rep_ran`'s statement, pointwise). -/
theorem ran_holds {R : Tab k v} {S : Tab v v} (h : R.ran = .ok S) (hw : Vals.WF R.val) (a b : v.El) : S.Holds a b ↔ a = b ∧ ∃ x, R.Holds x a := by
  unfold Tab.ran at h
  cases hn : Vals.nub R.val with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn hw a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, ValsB.row R.key i, i, rfl, hi⟩
    · rintro ⟨rfl, x, i, -, hi⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

/-- **`R.dom` denotes `𝟙 ∩ R ≫ R°`** (`CRel.rep_dom`'s statement, pointwise). -/
theorem dom_holds {R : Tab k v} {S : Tab k k} (h : R.dom = .ok S) (hw : Vals.WF R.key) (a b : k.El) : S.Holds a b ↔ a = b ∧ ∃ y, R.Holds a y := by
  unfold Tab.dom at h
  cases hn : Vals.nub R.key with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn hw a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, ValsB.row R.val i, i, hi, rfl⟩
    · rintro ⟨rfl, y, i, hi, -⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

end Tab

/-! ## Checks on `foR` tables -/




/-- **Equal codes, equal rows** of a side owning every row (`Vals.WF`): `ValsB.row_of_codes` at `P = True`. -/
theorem Vals.row_of_codes {A : Obj} {n : USize} (x : Vals A n) (hw : Vals.WF x) {es : List (AscKey × Enc)}
    (hes : ValsB.cols x = .ok es) {cs} (hc : es.mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat)
    (hk : seenKey n es i = seenKey n es i') : ValsB.row x i = ValsB.row x i' :=
  ValsB.row_of_codes x _ hw hes hc i i' trivial trivial hk

/-- **Equal rows, equal codes** of a side owning every row (`Vals.WF`): `ValsB.codes_of_row` at `P = True`. -/
theorem Vals.codes_of_row {A : Obj} {n : USize} (x : Vals A n) (hw : Vals.WF x) {es : List (AscKey × Enc)}
    (hes : ValsB.cols x = .ok es) {cs} (hc : es.mapM (ascCol n) = .ok cs) (i i' : Fin n.toNat)
    (hr : ValsB.row x i = ValsB.row x i') : seenKey n es i = seenKey n es i' :=
  ValsB.codes_of_row x _ hw hes hc i i' trivial trivial hr

end Rel
