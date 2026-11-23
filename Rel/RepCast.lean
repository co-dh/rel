module

public import Rel.Run.Cast
public import Rel.RepSetOps
public import Rel.RepCanon
public import Rel.RepCols
public import Rel.RepTabDiv
public import Rel.RepTabArith
public import Rel.Lang.Den

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The law of `$` (`Tab.cast`): its table is the graph of `QAtomicType.embed` on the values in demand. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- The rows of an `Arr.gather` read a valid column. -/
theorem gather_valid {u : QAtomicType} {m n : USize} {ix : Enc} {x : Arr u n} {y : Arr u m}
    (h : Arr.gather m ix x = .ok y) : Kernel.Enc.Valid n x.enc := by
  unfold Arr.gather at h; split at h
  · exact kgather_valid (by assumption)
  · cases h

/-- **A column map followed by a filter of nulls** (`$`, the unary float verbs): `Tab.keep` of the rows `(X i, w i)` at
the flag `flag` holds `a b` exactly where `a` is a value of `X` and `P a b`, given that row by row the flag is a bit,
set exactly where `P` relates the value to the answer `w i`. -/
theorem keep_map_holds {A : Obj} {t : QAtomicType} {n : USize} {X : Vals A n} {w : Arr t n} {flag : Enc}
    {T : Tab A (.atom t)} {P : A.El → (Obj.atom t).El → Prop}
    (hU : Tab.keep (k := A) (v := .atom t) ⟨n, X, w⟩ flag = .ok T)
    (row : ∀ i : Fin n.toNat, wd n flag i < 2 ∧ ∀ v, (wd n flag i ≠ 0 ∧ w.get i = v) ↔ P (X.row i) v)
    (a : A.El) (b : (Obj.atom t).El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ P a b := by
  rw [keep_holds hU (fun i hi => (row ⟨i, hi⟩).1)]
  constructor
  · rintro ⟨i, hf, rfl, rfl⟩
    exact ⟨⟨i, rfl⟩, by rw [Vals.row_atom w]; exact ((row i).2 _).1 ⟨hf, rfl⟩⟩
  · rintro ⟨⟨i, rfl⟩, hp⟩
    obtain ⟨hf, hw⟩ := ((row i).2 b).2 hp
    exact ⟨i, hf, rfl, by rw [Vals.row_atom]; exact hw⟩

/-- **`X $ t` denotes the graph of `embed s t`** on the values `X`: a value with no image at `t` has no row. -/
theorem cast_holds {s t : QAtomicType} {n : USize} {X : Vals (.atom s) n} {T : Tab (.atom s) (.atom t)}
    (h : Tab.cast X = .ok T) (a : (Obj.atom s).El) (b : (Obj.atom t).El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ QAtomicType.embed s t a = some b := by
  dsimp only [Tab.cast] at h
  split at h
  case isFalse => cases h
  rename_i hok
  have hst : s.storeFmt?.isSome ∧ t.storeFmt?.isSome := by
    unfold QAtomicType.castOK at hok
    revert hok; cases s.storeFmt? <;> cases t.storeFmt? <;> simp
  obtain ⟨hgs, -, -⟩ := storeFmt_ne hst.1
  obtain ⟨hgt, -, htu⟩ := storeFmt_ne hst.2
  obtain ⟨w, hw, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨flag, hf, hU⟩ := Except.bind_eq_ok'.1 h
  have hv : Kernel.Enc.Valid n X.enc ∧ Kernel.Enc.Valid n w.enc := by
    unfold Tab.keep at hU
    obtain ⟨⟨M, sel⟩, -, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨K, hK, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨V, hV, -⟩ := Except.bind_eq_ok'.1 hU
    exact ⟨gather_valid (x := X) hK, gather_valid (x := w) hV⟩
  have hcm := colMap_get (colArr_ok hw) (hn := nofun)
  have hfl := colMap_post hf
  -- each row: the flag `1` and the image read back, or the flag `0` and no image
  have row : ∀ i : Fin n.toNat,
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 1 ∧ QAtomicType.embed s t (X.get i) = some (w.get i)) ∨
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 0 ∧ QAtomicType.embed s t (X.get i) = none) := by
    intro i
    obtain ⟨a, ha, -, hxa⟩ := Arr.get_raw_atom X hgs i
    obtain ⟨v, hev, hwv⟩ := hcm.2 i.1 i.2
    obtain ⟨b, hb, -, hwb⟩ := Arr.get_raw_atom w hgt i
    rw [ha] at hev
    simp only [Option.getD_some, Op.eval, Except.ok.injEq] at hev
    rw [if_neg htu] at hwv
    rw [hwv] at hb; cases hb
    have hfi := hfl.2 i.1 i.2
    rw [hwv] at hfi
    simp only [Option.getD_some] at hfi
    have hfv := eval_ne_word hfi
    simp only [ne_comm (a := nulWord)] at hfv
    rw [hxa, of_atomOfBits _ hgs hst.1, hwb, of_atomOfBits _ hgt hst.2]
    subst hev
    cases he : QAtomicType.embed s t (QAtomicType.ofBits s a) with
    | none =>
      refine .inr ⟨?_, rfl⟩
      rw [hfv]; simp [QAtomicType.castWord, he, nulWord]
    | some y =>
      have hy := QAtomicType.word_ne_nul he
      refine .inl ⟨?_, ?_⟩
      · rw [hfv]; simp [QAtomicType.castWord, he, nulWord, hy]
      · simp [QAtomicType.castWord, he, QAtomicType.ofBits_word y hst.2]
  refine keep_map_holds (P := fun x y => QAtomicType.embed s t x = some y) hU (fun i => ?_) a b
  rcases row i with h | h <;> simp only [wd, Vals.row_atom, h.1, h.2] <;> simp

/-- No `floatOps` row is the stream `.first` (`fmapCols_spec` reads `colMap`, which `.first` makes a stream). -/
theorem floatOps_ne {s : String} {o : Op} {u : QAtomicType} (hs : floatOps.lookup s = some (o, u)) : o ≠ .first ∧ o ≠ .null := by
  simp only [floatOps, List.lookup] at hs
  repeat' split at hs
  all_goals first | (cases hs; decide) | cases hs

/-- **A `floatOps` row `s` on the values `X`** denotes `floatDen o` of its `Op` there: no row at an object holding no
float or a target holding no number, nor where the answer has no word at the target. -/
theorem floatOp_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} {s : String} {o : Op} {u : QAtomicType}
    (hs : floatOps.lookup s = some (o, u)) (h : Tab.floatOp s X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.floatDen o A B a b := by
  match A, B, X, T, h, a, b with
  | .atom t, .atom u, X, T, h, a, b =>
    simp only [Tab.floatOp, hs] at h
    split at h
    case isFalse => cases h
    rename_i hf
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    refine keep_map_holds hU (fun i => ?_) a b
    obtain ⟨h2, hi⟩ := fmapCols_spec hf.2.1 hf.2.2 hm i (floatOps_ne hs).1 (floatOps_ne hs).2
    -- a unary `Op` reads its second operand alone (`Op.eval_acc`), so `X X` is `0 X`
    refine ⟨h2, fun v => (hi v).trans ⟨fun ⟨X, X', Y, R, hX, hX', hY, hR⟩ => ?_,
      fun ⟨_, X, Y, R, hX, hY, hR⟩ => ⟨X, X, Y, R, hX, hX, by rw [Op.eval_acc hf.1]; exact hY, hR⟩⟩⟩
    rw [hX] at hX'; cases hX'
    exact ⟨hf.1, X, Y, R, hX, by rw [← Op.eval_acc hf.1 X X]; exact hY, hR⟩
  | .prod (.atom t) (.atom t'), .atom u, X, T, h, a, b =>
    simp only [Tab.floatOp, hs] at h
    split at h
    case isFalse => cases h
    rename_i hf
    obtain ⟨ho, rfl, hf, hu⟩ := hf
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    refine keep_map_holds hU (fun i => ?_) a b
    obtain ⟨h2, hi⟩ := fmapCols_spec hf hu hm i (floatOps_ne hs).1 (floatOps_ne hs).2
    exact ⟨h2, fun v => (hi v).trans ⟨fun hr => ⟨ho, rfl, hr⟩, fun ⟨_, _, hr⟩ => hr⟩⟩
  | .atom _, .prod .., _, _, h, _, _ | .atom _, .arr _, _, _, h, _, _ | .atom _, .sum .., _, _, h, _, _
  | .prod (.atom _) (.atom _), .prod .., _, _, h, _, _ | .prod (.atom _) (.atom _), .arr _, _, _, h, _, _
  | .prod (.atom _) (.atom _), .sum .., _, _, h, _, _
  | .prod (.atom _) (.prod ..), _, _, _, h, _, _ | .prod (.atom _) (.arr _), _, _, _, h, _, _
  | .prod (.atom _) (.sum ..), _, _, _, h, _, _
  | .prod (.prod ..) _, _, _, _, h, _, _ | .prod (.arr _) _, _, _, _, h, _, _ | .prod (.sum ..) _, _, _, _, h, _, _
  | .arr _, _, _, _, h, _, _ | .sum .., _, _, _, h, _, _ => simp [Tab.floatOp, hs] at h
  | .one, _, _, _, h, _, _ | .prod .one _, _, _, _, h, _, _ | .prod (.atom _) .one, _, _, _, h, _, _
  | .atom _, .one, _, _, h, _, _ | .prod (.atom _) (.atom _), .one, _, _, h, _, _ => simp [Tab.floatOp, hs] at h

/-- `$` at any objects: the graph `castDen A B` on the values `X`, no row where a side is no atom. -/
theorem cast_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} (h : Tab.cast X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.castDen A B a b := by
  match A, B, X, T, h, a, b with
  | .atom _, .atom _, _, _, h, a, b => exact cast_holds h a b
  | .atom _, .prod .., _, _, h, _, _ | .atom _, .arr _, _, _, h, _, _ | .atom _, .sum .., _, _, h, _, _
  | .prod .., _, _, _, h, _, _ | .arr _, _, _, _, h, _, _ | .sum .., _, _, _, h, _, _ =>
    simp [Tab.cast] at h

/-- A `1+i64` row as its flag word `N` and value word `W` give it: the null where `N` is set, else `W` as an `i64`. -/
def optWord (N W : UInt64) : (Obj.opt .long).El := if N ≠ 0 then .inl () else .inr W.toInt64

/-- A `1+i64` row read as `1 + i64`: `Obj.optEl` at the band of `1+i64`, the null `inl ()`. -/
theorem optEl_long (v : Option Int64) : Obj.optEl (a := .one) (b := .long) (t := .i64) rfl v = v.elim (.inl ()) .inr := by
  unfold Obj.optEl; generalize Obj.band_some (a := .one) (b := .long) (t := .i64) rfl = p; obtain ⟨p1, p2⟩ := p
  cases v <;> rfl

/-- **Row `i` of a `1+i64` column is read off its words** (`optWord`): its flag `rdNul` and its raw word. -/
theorem row_opt_i64 {n : USize} (x : Opt .i64 n) (i : Fin n.toNat) :
    Vals.row (A := .opt .long) x i = optWord (rdNul n x.enc i) ((Enc.raw .i64 n x.enc)[i.1]?.getD 0) := by
  change Obj.optEl (a := .one) (b := .long) (t := .i64) rfl (x.get i) = _
  rw [optEl_long, Opt.get_ne x i (by decide)]
  cases hn : x.isNul i
  · have h0 := (Opt.isNul_eq_false x i).1 hn
    obtain ⟨a, ha, -, ex⟩ := Enc.get_raw_atom x.wf (by decide) i h0
    simp only [Bool.false_eq_true, if_false, ex, optWord, rdNul, h0, ha, Option.getD_some, ne_eq, not_true_eq_false]
    rfl
  · have h1 : (foRNuls n x.enc)[i.1]? ≠ some 0 := fun e => absurd ((Opt.isNul_eq_false x i).2 e) (by simp [hn])
    have hb := foRNuls_bit n x.enc i.2
    have hne : rdNul n x.enc i ≠ 0 := fun h => h1 (by rw [hb]; simp only [rdNul] at h; simp [h])
    simp only [if_true, optWord, hne, ne_eq, not_false_eq_true]
    rfl

/-- A row's flag word is `0` or `1` (`foRNuls_bit`). -/
theorem rdNul_bit (n : USize) (e : Enc) (i : Fin n.toNat) : rdNul n e i = 0 ∨ rdNul n e i = 1 := by
  have hb := foRNuls_bit n e i.2
  simp only [rdNul] at hb ⊢; rw [hb]; split <;> simp

/-- **The word step of `nulStep`**: `max`/`min` (`nulVerb`) of the operands' words `X`, `Y`, a null (flag `NX`, `NY`)
    read as the order's identity `f`, is the answer's word `W` where the flags' `b` (`and`/`or`) is `0`, the answer's
    flag `NW` being whether it is set; read back by `optWord`, a pair `nulStep k` relates. -/
theorem nulStep_words {k : UInt8} {o b : Op} {f : UInt64} (hv : nulVerb k = some (o, b, f)) {X Y Z NX NY NZ NW W : UInt64}
    (hX : NX = 0 ∨ NX = 1) (hY : NY = 0 ∨ NY = 1)
    (hz : o.eval (if NX != 0 then f else X) (if NY != 0 then f else Y) = .ok Z) (hn : b.eval NX NY = .ok NZ)
    (hW : NW = if NZ != 0 then 1 else 0) (hZ : NZ = 0 → W = Z) :
    Lang.nulStep k (optWord NX X, optWord NY Y) (optWord NW W) := by
  refine ⟨o, b, f, hv, ?_⟩
  have hc : (o = .max ∧ b = .and ∧ f = 0x8000000000000000 ∧ k = Ew.greater) ∨
      (o = .min ∧ b = .or ∧ f = 0x7fffffffffffffff ∧ k = Ew.lesser) := by
    unfold nulVerb at hv
    by_cases h1 : k = Ew.greater
    · simp [h1, Op.nulFold] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact .inl ⟨rfl, rfl, rfl, h1⟩
    · by_cases h2 : k = Ew.lesser
      · simp [h2, Op.nulFold] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact .inr ⟨rfl, rfl, rfl, h2⟩
      · simp [h1, h2] at hv
  rcases hc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> rcases hX with rfl | rfl <;>
    rcases hY with rfl | rfl <;> simp only [Op.eval, Except.ok.injEq] at hz hn <;> subst hn <;> subst hW <;>
    simp (config := {decide := true}) [optWord, Op.i] at hz hZ ⊢ <;> (try subst hZ) <;> (try subst hz) <;>
    first
    | done
    | (simp only [Verify.Ew.intStep_greater, Verify.Ew.intStep_lesser]; split <;> split <;> grind)
    -- a null beside a value under `max`: the identity `0x8000…` is `Int64.minValue`, below or equal to every value
    | (split <;> rename_i hlt <;> first | rfl | (simp only [Int64.lt_iff_toInt_lt] at hlt; first
        | (have := Int64.minValue_le_toInt X.toInt64; simp at this hlt; omega)
        | (have := Int64.minValue_le_toInt Y.toInt64; apply Int64.toInt_inj.1; simp at this hlt ⊢; omega)))

/-- `nulStep k` is a partial function: one `nulVerb k`, one answer at each pair. -/
theorem nulStep_fun {k : UInt8} {p : (Obj.prod (.opt .long) (.opt .long)).El} {w w' : (Obj.opt .long).El}
    (h : Lang.nulStep k p w) (h' : Lang.nulStep k p w') : w = w' := by
  obtain ⟨o, b, f, hv, h⟩ := h
  obtain ⟨o', b', f', hv', h'⟩ := h'
  rw [hv] at hv'; cases hv'
  obtain ⟨_ | x, _ | y⟩ := p <;> simp only at h h'
  · rw [h, h']
  all_goals first | rw [h, h'] |
    (rcases h with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ <;> rcases h' with ⟨hb', rfl⟩ | ⟨hb', rfl⟩ <;>
      first | rfl | exact absurd hb hb' | exact absurd hb' hb)

/-- `Tab.arithOp` at `1+i64`: one `kscan` of the verb's `Op` (`nulVerb`) over the two columns, its answer the column. -/
theorem arithOp_opt {n : USize} {X : Vals (.prod (.opt .long) (.opt .long)) n}
    {T : Tab (.prod (.opt .long) (.opt .long)) (.opt .long)} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) :
    ∃ o b f r hz, nulVerb k = some (o, b, f) ∧
      kscan o false .i64 .i64 n none [(n, (X.1 : Opt .i64 n).enc), (n, (X.2 : Opt .i64 n).enc)] = .ok r ∧
      T = ⟨n, X, (Opt.mk r.1 hz : Opt .i64 n)⟩ := by
  simp only [Tab.arithOp, hs] at h
  rcases hv : nulVerb k with _ | ⟨o, b, f⟩ <;> simp only [hv] at h
  · cases h
  obtain ⟨r, hr, h⟩ := Except.bind_eq_ok'.1 h
  rcases hw : Enc.wf? .i64 n r.1 with _ | ⟨⟨hz⟩⟩ <;> simp only [hw] at h
  · cases h
  exact ⟨o, b, f, r, hz, rfl, hr, (Except.ok.inj h).symm⟩

/-- **`Tab.arithOp` at `1+i64` denotes `nulStep`**: a source holding a null is read through `kscan_nul_row`, none
    through `colMap_raw` (the answer then holds none, `kscan_lock_closed`), both giving `nulStep_words` row by row. -/
theorem arithOp_opt_den {n : USize} {X : Vals (.prod (.opt .long) (.opt .long)) n}
    {T : Tab (.prod (.opt .long) (.opt .long)) (.opt .long)} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) (a : (Obj.prod (.opt .long) (.opt .long)).El)
    (w : (Obj.opt .long).El) : T.Holds a w ↔ (∃ i, X.row i = a) ∧ Lang.nulStep k a w := by
  obtain ⟨o, b, f, r, hz, hv, hr, rfl⟩ := arithOp_opt hs h
  obtain ⟨x, y⟩ := X
  change Opt .i64 n at x y
  have ho : (o = .max ∨ o = .min) ∧ o.nulFold = some (b, f) := by
    unfold nulVerb at hv
    by_cases h1 : k = Ew.greater
    · simp [h1, Op.nulFold] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact ⟨.inl rfl, rfl⟩
    · by_cases h2 : k = Ew.lesser
      · simp [h1, h2, Op.nulFold] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact ⟨.inr rfl, rfl⟩
      · simp [h1, h2] at hv
  have hk : kscanStream o [(n, x.enc), (n, y.enc)] [] [] = false := by rcases ho.1 with rfl | rfl <;> rfl
  -- row `i`: the verb on the words a null reads as `f`, the flags' `b`, and the answer's word off its null
  have row : ∀ i : Fin n.toNat, ∃ NZ Z, o.eval (rdFill f .i64 n x.enc i) (rdFill f .i64 n y.enc i) = .ok Z ∧
      b.eval (rdNul n x.enc i) (rdNul n y.enc i) = .ok NZ ∧ rdNul n r.1 i = (if NZ != 0 then 1 else 0) ∧
      (NZ = 0 → (Enc.raw .i64 n r.1)[i.1]?.getD 0 = Z) := fun i => by
    by_cases hN : ∃ p ∈ [(n, x.enc), (n, y.enc)], hasNul p.2 = true
    · obtain ⟨out, nl, hos, hns, hre, -, -, p, ps, hes, hrow⟩ :=
        Verify.kscan_nul_row ho.2 rfl rfl hk (by simp [x.wf, y.wf]) hN hr
      simp only [List.cons.injEq] at hes; obtain ⟨rfl, rfl⟩ := hes
      obtain ⟨h1, h2, h3⟩ := hrow i i.2
      simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_pure] at h1 h2
      refine ⟨_, _, h1, h2, by simp [rdNul, h3], fun h0 => ?_⟩
      have hbit : Column.bitAt (nulMap nl) i = false := by
        rw [nulMap, Verify.bitAt_packOf _ _ _ (by rw [hns]; exact i.2)]; simp [h0]
      rw [hre, raw_wordsFoR_of_bit _ _ (by simp [hos]) i (by simp [hos]) hbit]
      simp [Verify.cutBit, Array.getElem?_eq_getElem (show i.1 < out.size by rw [hos]; exact i.2)]
    · simp only [not_exists, not_and, Bool.not_eq_true] at hN
      have hF : o.nulFold = none ∨ ∀ p ∈ [(n, x.enc), (n, y.enc)], hasNul p.2 = false := .inr hN
      have hc : colMap o n x.enc y.enc .i64 .i64 = .ok r.1 := by
        simp only [colMap, hr, bind, Except.bind, pure, Except.pure]
      obtain ⟨-, -, -, hcr⟩ := colMap_raw hc hk (by rcases ho.1 with rfl | rfl <;> decide) hF
      have h0 : ∀ e : Enc, Enc.WF .i64 n e → hasNul e = false → rdNul n e i = 0 := fun e hw he => by
        simp [rdNul, Verify.foRNuls_plain hw he i.2]
      have hx0 := h0 _ x.wf (hN (n, x.enc) (by simp)); have hy0 := h0 _ y.wf (hN (n, y.enc) (by simp))
      refine ⟨0, _, by simp only [rdFill, hx0, hy0]; exact hcr i i.2, ?_,
        by simp [h0 _ hz (Verify.kscan_lock_closed hk hF hr).2.2], fun _ => rfl⟩
      rw [hx0, hy0]; rcases ho with ⟨rfl | rfl, hnf⟩ <;> simp [Op.nulFold] at hnf <;> obtain ⟨rfl, rfl⟩ := hnf <;> rfl
  have rz : ∀ i : Fin n.toNat, Lang.nulStep k (Vals.row (A := .prod (.opt .long) (.opt .long)) (x, y) i)
      (Vals.row (A := .opt .long) (Opt.mk r.1 hz : Opt .i64 n) i) := fun i => by
    obtain ⟨NZ, Z, h1, h2, h3, h4⟩ := row i
    show Lang.nulStep k (Vals.row (A := .opt .long) x i, Vals.row (A := .opt .long) y i) _
    rw [row_opt_i64, row_opt_i64, row_opt_i64]
    exact nulStep_words hv (rdNul_bit n _ i) (rdNul_bit n _ i) h1 h2 h3 h4
  constructor
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, rz i⟩
  · rintro ⟨⟨i, rfl⟩, hw⟩; exact ⟨i, rfl, nulStep_fun (rz i) hw⟩

/-- **A row `s` of `arithOps` on the pairs `X`** denotes `stepOn` of its verb there: `stepColsAt_spec` at an atom,
    `arithOp_opt_den` at `1+i64`, no row at any other object. -/
theorem arithOp_den {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) B} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) (a : (Obj.prod B B).El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.stepOn k B a b := by
  cases B
  case atom u =>
    simp only [Tab.arithOp, hs, and_self] at h
    obtain ⟨⟨w, flag⟩, hm, h⟩ := Except.bind_eq_ok'.1 h
    obtain ⟨-, -, hU⟩ := Except.bind_eq_ok'.1 h
    exact keep_map_holds hU (fun i => stepColsAt_spec hm i) a b
  case sum c d =>
    cases c <;> cases d <;> first
      | (rename_i t; cases t <;> first | exact arithOp_opt_den hs h a b | simp [Tab.arithOp, hs] at h)
      | simp [Tab.arithOp, hs] at h
  all_goals simp [Tab.arithOp, hs] at h

/-- **A row of `arithOps` keeps `Tab.WF`**: `X` keyed to the answer words (`keep`), or to the `1+i64` answer. -/
theorem arithOp_wf {s : String} {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) B}
    (h : Tab.arithOp s X = .ok T) (hX : Vals.WF X) : T.WF := by
  rcases hl : arithOps.lookup s with _ | k
  · cases B <;> simp [Tab.arithOp, hl] at h
  cases B
  case atom u =>
    simp only [Tab.arithOp, hl, and_self] at h
    obtain ⟨⟨w, f⟩, -, h⟩ := Except.bind_eq_ok'.1 h
    obtain ⟨-, -, h⟩ := Except.bind_eq_ok'.1 h
    exact keep_wf h ⟨hX, trivial⟩
  case sum c d =>
    cases c <;> cases d <;> first
      | (rename_i t; cases t <;> first
          | (obtain ⟨-, -, -, -, -, -, -, rfl⟩ := arithOp_opt hl h; exact ⟨hX, trivial⟩)
          | simp [Tab.arithOp, hl] at h)
      | simp [Tab.arithOp, hl] at h
  all_goals simp [Tab.arithOp, hl] at h

/-- **The row `succ` on the values `X`** denotes `succOn`: each `u` to `Ew.intStep`'s `u + 1` (the null to itself),
    the step of `Tab.succ_holds`; no row at an object other than `i64`. -/
theorem succOp_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.succOp X = .ok T) (x w : A.El) :
    T.Holds x w ↔ (∃ i, X.row i = x) ∧ Lang.succOn A x w := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.succOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨s, hs, h⟩ := h
      obtain ⟨_, -, h⟩ := h
      obtain ⟨-, -, h⟩ := h
      cases h
      have hrow := Tab.succCol_row hs
      simp only [Tab.Holds, Lang.succOn]
      constructor
      · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hrow i⟩
      · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hrow i⟩
    all_goals simp [Tab.succOp] at h
  all_goals simp [Tab.succOp] at h

/-- **The row `succ` keeps `Tab.WF`**: `X` keyed to the answer words. -/
theorem succOp_wf {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.succOp X = .ok T) (hX : Vals.WF X) :
    T.WF := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.succOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨_, -, h⟩ := h
      obtain ⟨_, -, h⟩ := h
      obtain ⟨-, -, h⟩ := h
      cases h; exact ⟨hX, trivial⟩
    all_goals simp [Tab.succOp] at h
  all_goals simp [Tab.succOp] at h

/-- **The row `mix` on the values `X`** denotes `mixOn`: each counter `u` to `Op.mixWord u`; no row at an object other
    than `i64`. -/
theorem mixOp_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.mixOp X = .ok T) (x w : A.El) :
    T.Holds x w ↔ (∃ i, X.row i = x) ∧ Lang.mixOn A x w := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.mixOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨s, hs, h⟩ := h
      cases h
      have hrow := Tab.mixCol_row hs
      simp only [Tab.Holds, Lang.mixOn]
      constructor
      · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hrow i⟩
      · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hrow i⟩
    all_goals simp [Tab.mixOp] at h
  all_goals simp [Tab.mixOp] at h

/-- **The row `mix` keeps `Tab.WF`**: `X` keyed to the answer words. -/
theorem mixOp_wf {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.mixOp X = .ok T) (hX : Vals.WF X) :
    T.WF := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.mixOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨_, -, h⟩ := h
      cases h; exact ⟨hX, trivial⟩
    all_goals simp [Tab.mixOp] at h
  all_goals simp [Tab.mixOp] at h

/-- **The words of `Arr.ofFn t n f`** as the kernels read them: word `i` is `f i` cut to `t`'s `8 * w` bits
(`raw_encodeAt` of the packing `foldl_pushBits` reads back). -/
theorem _root_.Rel.Arr.raw_ofFn {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hu : t ≠ .u1 ∧ t.width.isSome)
    {n : USize} (f : Fin n.toNat → UInt64) (i : Fin n.toNat) :
    (Enc.raw t n (Arr.ofFn t n f hu).enc)[i.1]? = some (UInt64.ofNat ((f i).toNat % 2 ^ (8 * w))) := by
  have hw : 0 < w ∧ w ≤ 8 := by cases t <;> simp [QAtomicType.width] at ht ⊢ <;> omega
  have hf := Verify.foldl_pushBits (fun x : UInt64 => x) w hw.2 (List.ofFn f) .empty
  simp only [ht, Option.getD_some] at hf
  simp only [Arr.ofFn, Arr.ofBytes, Ext.Enc.ofBytes, ht, Option.getD_some, Kernel.Coc.encode]
  change (Enc.raw t n (Enc.foR _ _))[i.1]? = _
  rw [Verify.raw_encodeAt t w ht hu.1 Column.lgEnc (by decide) _ n
    (by rw [hf.1]; simp [Nat.mul_div_cancel_left _ hw.1])]
  have := hf.2.2 i.1 (by simp)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_ofFn] at this
  simp [i.2, Nat.mul_comm, this]

/-- **`ymd` keeps `Tab.WF`**: `X` keyed to the day words, `keep`. -/
theorem ymd_wf {A B : Obj} {n : USize} {X : Vals A n} {t : Tab A B} (h : Tab.ymd X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  unfold Tab.ymd at h
  split at h
  · exact keep_wf h ⟨hX, trivial⟩
  · cases h

/-- **`ymd X` denotes `ymdDen`** on the texts `X`: a cell to the day it spells (`Db.Csv.ymd`), no row where it
spells none. -/
theorem ymd_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} (h : Tab.ymd X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.ymdDen A B a b := by
  unfold Tab.ymd at h
  split at h
  case h_2 => cases h
  show _ ↔ _ ∧ (Db.Csv.ymd a).map Int32.ofInt = some b
  rename_i X
  have hr : ∀ i : Fin n.toNat,
      ((Tab.toArray (k := .arr (.atom .char)) (v := .one) ⟨n, X, ()⟩)[i.1]?.map (·.1)).getD [] = X.row i := by
    intro i; simp [Tab.toArray, i.2]
  simp only [Tab.ymd, hr] at h
  have hf : ∀ i : Fin n.toNat, (Enc.raw .i64 n (Arr.ofFn .i64 n fun j =>
      if (Db.Csv.ymd (X.row j)).isSome then 1 else 0).enc)[i.1]?.getD 0 =
      if (Db.Csv.ymd (X.row i)).isSome then 1 else 0 := by
    intro i; rw [Arr.raw_ofFn rfl]; simp only [Option.getD_some]; split <;> decide
  have hd : ∀ i : Fin n.toNat, Vals.row (A := .atom .date) (Arr.ofFn .date n fun j =>
      (Int32.ofInt ((Db.Csv.ymd (X.row j)).getD 0)).toUInt32.toUInt64) i =
      Int32.ofInt ((Db.Csv.ymd (X.row i)).getD 0) := by
    intro i
    rw [Vals.row_atom, Arr.get_word _ rfl, Arr.raw_ofFn rfl]
    simp only [Option.getD_some, QAtomicType.ofBits]
    rw [Nat.mod_eq_of_lt (by simpa using (Int32.ofInt _).toUInt32.toNat_lt)]
    simp
  rw [keep_holds h (fun i hi => by
    have := hf ⟨i, hi⟩; dsimp only at this ⊢; rw [this]; split <;> decide)]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    have hi' := hf i ▸ hi
    show _ = some (Vals.row (A := .atom .date) _ i)
    rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
  · rintro ⟨⟨i, rfl⟩, hb⟩
    refine ⟨i, ?_, rfl, ?_⟩
    · rw [hf i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
    · show Vals.row (A := .atom .date) _ i = _
      rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all

end Tab
end Rel
