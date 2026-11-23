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
    intro i; dsimp only [Vals.get]
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
    ValsB.row (o := false) (A := .opt .long) x i = optWord (rdNul n x.enc i) ((Enc.raw .i64 n x.enc)[i.1]?.getD 0) := by
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

/-- **The rows of `nulVerb`**: `max`/`min`, which `kscan` orders null by (`Op.nulFold`), or a verb that propagates
    null (`b = or`, `f = nulWord`) whose `Op` orders none. -/
theorem nulVerb_cases {k : UInt8} {o b : Op} {f : UInt64} (h : nulVerb k = some (o, b, f)) :
    (o = .max ∧ b = .and ∧ f = 0x8000000000000000 ∧ k = Ew.greater) ∨
    (o = .min ∧ b = .or ∧ f = 0x7fffffffffffffff ∧ k = Ew.lesser) ∨
    (b = .or ∧ f = nulWord ∧ o.nulFold = none ∧ (k = Ew.add ∨ k = Ew.sub ∨ k = Ew.mul)) := by
  unfold nulVerb at h
  by_cases h1 : k = Ew.greater
  · simp [h1, Op.nulFold] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .inl ⟨rfl, rfl, rfl, h1⟩
  by_cases h2 : k = Ew.lesser
  · simp [h2, Op.nulFold] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .inr (.inl ⟨rfl, rfl, rfl, h2⟩)
  refine .inr (.inr ?_)
  by_cases h3 : k = Ew.add
  · subst h3; simp (config := {decide := true}) [List.lookup, beq_iff_eq, Ew.add, Ew.sub, Ew.mul] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inl rfl⟩
  by_cases h4 : k = Ew.sub
  · subst h4; simp (config := {decide := true}) [List.lookup, beq_iff_eq, Ew.add, Ew.sub, Ew.mul] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inr (.inl rfl)⟩
  by_cases h5 : k = Ew.mul
  · subst h5; simp (config := {decide := true}) [List.lookup, beq_iff_eq, Ew.add, Ew.sub, Ew.mul] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, .inr (.inr rfl)⟩
  have e3 : (k == Ew.add) = false := by simp [h3]
  have e4 : (k == Ew.sub) = false := by simp [h4]
  have e5 : (k == Ew.mul) = false := by simp [h5]
  simp [h1, h2, e3, e4, e5, List.lookup] at h

/-- **The word step of `nulStep`**: `max`/`min` (`nulVerb`) of the operands' words `X`, `Y`, a null (flag `NX`, `NY`)
    read as the order's identity `f`, is the answer's word `W` where the flags' `b` (`and`/`or`) is `0`, the answer's
    flag `NW` being whether it is set; read back by `optWord`, a pair `nulStep k` relates. -/
theorem nulStep_words {k : UInt8} {o b : Op} {f : UInt64} (hv : nulVerb k = some (o, b, f))
    (hnf : o.nulFold = some (b, f)) {X Y Z NX NY NZ NW W : UInt64}
    (hX : NX = 0 ∨ NX = 1) (hY : NY = 0 ∨ NY = 1)
    (hz : o.eval (if NX != 0 then f else X) (if NY != 0 then f else Y) = .ok Z) (hn : b.eval NX NY = .ok NZ)
    (hW : NW = if NZ != 0 then 1 else 0) (hZ : NZ = 0 → W = Z) :
    Lang.nulStep k (optWord NX X, optWord NY Y) (optWord NW W) := by
  refine (Lang.nulStep_iff _ _ _).2 ⟨o, b, f, hv, ?_⟩
  have hc : (o = .max ∧ b = .and ∧ f = 0x8000000000000000 ∧ k = Ew.greater) ∨
      (o = .min ∧ b = .or ∧ f = 0x7fffffffffffffff ∧ k = Ew.lesser) := by
    rcases nulVerb_cases hv with h | h | ⟨-, -, h, -⟩
    · exact .inl h
    · exact .inr h
    · rw [h] at hnf; cases hnf
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
  obtain ⟨o, b, f, hv, h⟩ := (Lang.nulStep_iff _ _ _).1 h
  obtain ⟨o', b', f', hv', h'⟩ := (Lang.nulStep_iff _ _ _).1 h'
  rw [hv] at hv'; cases hv'
  obtain ⟨_ | x, _ | y⟩ := p <;> simp only at h h'
  · rw [h, h']
  all_goals first | rw [h, h'] |
    (rcases h with ⟨hb, rfl⟩ | ⟨hb, rfl⟩ <;> rcases h' with ⟨hb', rfl⟩ | ⟨hb', rfl⟩ <;>
      first | rfl | exact absurd hb hb' | exact absurd hb' hb)

/-- `Tab.arithOp` at `1+i64`: one `kscan` of the verb's `Op` (`nulVerb`) over the two columns where it orders null,
    else `nulStepCol`; its answer the column. -/
theorem arithOp_opt {n : USize} {X : Vals (.prod (.opt .long) (.opt .long)) n}
    {T : Tab (.prod (.opt .long) (.opt .long)) (.opt .long)} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) :
    ∃ o b f r hz, nulVerb k = some (o, b, f) ∧
      (if o.nulFold = some (b, f) then
        (·.1) <$> kscan o false .i64 .i64 n none [(n, (X.1 : Opt .i64 n).enc), (n, (X.2 : Opt .i64 n).enc)]
       else Tab.nulStepCol s k n (X.1 : Opt .i64 n).enc (X.2 : Opt .i64 n).enc) = .ok r ∧
      T = ⟨n, X, (Opt.mk r hz : Opt .i64 n)⟩ := by
  simp only [Tab.arithOp, hs] at h
  rcases hv : nulVerb k with _ | ⟨o, b, f⟩ <;> simp only [hv] at h
  · cases h
  refine ⟨o, b, f, ?_⟩
  by_cases hnf : o.nulFold = some (b, f) <;> simp only [hnf, ↓reduceIte] at h ⊢ <;>
  · obtain ⟨r, hr, h⟩ := Except.bind_eq_ok'.1 h
    rcases hw : Enc.wf? .i64 n r with _ | ⟨⟨hz⟩⟩ <;> simp only [hw] at h
    · cases h
    exact ⟨r, hz, by first | rfl | trivial, hr, (Except.ok.inj h).symm⟩

/-- **Row `i` of a two-column `kscan` map of an op `o` that orders null** (`Op.nulFold = some (b, f)`), the answer
    through `chain post`, a source null or not: the answer is `WF`, its flag is `b` of the sources' flags, and where
    that is `0` its word is `chain post` of `o` on the sources' words, a null read as `f` (`rdFill`). -/
theorem kscan_nul_map {o b : Op} {f : UInt64} (hnf : o.nulFold = some (b, f)) {n : USize} {x y : Enc}
    {post : List (Op × UInt64)} {r : Enc × Option UInt64} (hx : Enc.WF .i64 n x) (hy : Enc.WF .i64 n y)
    (h : kscan o false .i64 .i64 n none [(n, x), (n, y)] [] post = .ok r) :
    Enc.WF .i64 n r.1 ∧ ∀ i : Fin n.toNat, ∃ NZ Z,
      (o.eval (rdFill f .i64 n x i) (rdFill f .i64 n y i) >>= chain post) = .ok Z ∧
      b.eval (rdNul n x i) (rdNul n y i) = .ok NZ ∧ rdNul n r.1 i = (if NZ != 0 then 1 else 0) ∧
      (NZ = 0 → wd n r.1 i = Z) := by
  have hk : kscanStream o [(n, x), (n, y)] [] post = false := by cases o <;> simp_all [Op.nulFold, kscanStream]
  by_cases hN : ∃ p ∈ [(n, x), (n, y)], hasNul p.2 = true
  · obtain ⟨out, nl, hos, hns, hre, -, hwf, p, ps, hes, hrow⟩ :=
      Verify.kscan_nul_row hnf rfl rfl hk (by simp [hx, hy]) hN h
    simp only [List.cons.injEq] at hes; obtain ⟨rfl, rfl⟩ := hes
    refine ⟨hwf, fun i => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrow i i.2
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_pure] at h1 h2
    refine ⟨_, _, h1, h2, by simp [rdNul, h3], fun h0 => ?_⟩
    have hbit : Column.bitAt (nulMap nl) i = false := by
      rw [nulMap, Verify.bitAt_packOf _ _ _ (by rw [hns]; exact i.2)]; simp [h0]
    rw [wd, hre, raw_wordsFoR_of_bit _ _ (by simp [hos]) i (by simp [hos]) hbit]
    simp [Verify.cutBit, Array.getElem?_eq_getElem (show i.1 < out.size by rw [hos]; exact i.2)]
  · simp only [not_exists, not_and, Bool.not_eq_true] at hN
    have hF : o.nulFold = none ∨ ∀ p ∈ [(n, x), (n, y)], hasNul p.2 = false := .inr hN
    have hc : colMap o n x y .i64 .i64 [] post = .ok r.1 := by
      simp only [colMap, h, bind, Except.bind, pure, Except.pure]
    have hon : o ≠ .null := by rintro rfl; simp [Op.nulFold] at hnf
    have cl := Verify.kscan_lock_closed hk hF h
    obtain ⟨-, -, -, hcr⟩ := colMap_chain hc hk hon hF
    have h0 : ∀ e : Enc, Enc.WF .i64 n e → hasNul e = false → ∀ i : Fin n.toNat, rdNul n e i = 0 :=
      fun e hw he i => by simp [rdNul, Verify.foRNuls_plain hw he i.2]
    refine ⟨cl.2.1, fun i => ?_⟩
    obtain ⟨X, Y, v, W, hX, hY, hv, hW, ho⟩ := hcr i i.2
    have hx0 := h0 _ hx (hN (n, x) (by simp)) i; have hy0 := h0 _ hy (hN (n, y) (by simp)) i
    cases hX; cases hY
    refine ⟨0, W, ?_, ?_, by simp [h0 _ cl.2.1 cl.2.2 i], fun _ => by simp [wd, ho]⟩
    · simp only [rdFill, hx0, hy0, bne_self_eq_false, Bool.false_eq_true, if_false, hv]; exact hW
    · rw [hx0, hy0]; cases o <;> simp [Op.nulFold] at hnf <;> obtain ⟨rfl, rfl⟩ := hnf <;> rfl

/-- **`fillNulCol` writes each row's word, a null row's as `nulWord`.** -/
theorem fillNulCol_row {n : USize} {x : Enc} (hx : Enc.WF .i64 n x) {z : Arr .i64 n} (h : Tab.fillNulCol n x = .ok z)
    (i : Fin n.toNat) : wd n z.enc i = if rdNul n x i != 0 then nulWord else wd n x i := by
  unfold Tab.fillNulCol at h
  obtain ⟨c, hc, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨m, hm, h⟩ := Except.bind_eq_ok'.1 h
  have hz : z.enc = m.1 := by
    split at h <;> first | (cases h; rfl) | simp [throw, throwThe, MonadExceptOf.throw] at h
  have hck : kscanStream .null [(n, x)] [] [(.first, nulWord)] = false := rfl
  obtain ⟨-, hzc⟩ := kscan_null_chain hck hc
  have cl := Verify.kscan_lock_closed hck (.inl rfl) hc
  have hc0 : rdNul n c.1 i = 0 := by simp [rdNul, Verify.foRNuls_plain cl.2.1 cl.2.2 i.2]
  have hzi : rdFill 0x8000000000000000 .i64 n c.1 i = nulWord := by
    obtain ⟨v, hw, hr⟩ := hzc i i.2
    simp [chain, Op.eval] at hw
    simp [rdFill, hc0, hr, ← hw]
  obtain ⟨-, row⟩ := kscan_nul_map (o := .max) (post := []) rfl hx cl.2.1 hm
  obtain ⟨NZ, Z, h1, h2, -, h4⟩ := row i
  have hNZ : NZ = 0 := by rw [hc0] at h2; simpa [Op.eval] using h2.symm
  rw [hz, h4 hNZ]
  rw [show chain ([] : List (Op × UInt64)) = (pure : UInt64 → Except String UInt64) from rfl, bind_pure, hzi] at h1
  rcases rdNul_bit n x i with h0 | h0 <;> simp only [rdFill, h0] at h1 ⊢
  · simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at h1 ⊢
    simp only [Op.eval, Except.ok.injEq, Op.i] at h1
    rw [← h1, if_neg]; intro hl; rw [Int64.lt_iff_toInt_lt] at hl
    have := Int64.minValue_le_toInt ((Enc.raw .i64 n x)[i.1]?.getD 0).toInt64; simp [nulWord] at hl this; omega
  · simp only [Op.eval, Except.ok.injEq] at h1; rw [← h1]; simp [nulWord]

/-- **`arithOvf` passing keeps every checked row**: where `arithOvf` answers `.ok ()` on the `i64` pairs `X` and the
    `0`/`1` column `keep`, a row with both words not `nulWord` and the divisor not `0` has keep word `1`. -/
theorem arithOvf_keep {s : String} {n : USize} {X : Vals (.prod .long .long) n} {keep : Enc}
    (h : Tab.arithOvf s (t := .i64) (t' := .i64) X keep = .ok ()) (hb : ∀ j < n.toNat, wd n keep j < 2)
    (i : Fin n.toNat) (h1 : wd n X.1.enc i ≠ nulWord) (h2 : wd n X.2.enc i ≠ nulWord) (h3 : wd n X.2.enc i ≠ 0) :
    wd n keep i = 1 := by
  simp only [Tab.arithOvf] at h
  obtain ⟨z, hz, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨n1, hn1, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨n2, hn2, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨a1, ha1, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨nk, hnk, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨nz, hnz, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨a2, ha2, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨f, hf, h⟩ := Except.bind_eq_ok'.1 h
  unfold Tab.failAt at h
  obtain ⟨T, hT, h⟩ := Except.bind_eq_ok'.1 h
  have hT0 : ¬ 0 < T.n.toNat := fun h0 => by simp [h0, throw, throwThe, MonadExceptOf.throw] at h
  have hw : ∀ c : Bool, Op.w c = 0 ∨ Op.w c = 1 := fun c => by cases c <;> simp [Op.w]
  -- row `j` of the flag: both words not null, keep `0`, divisor not `0`
  have row : ∀ j < n.toNat, wd n f j = (Op.w (nulWord != wd n X.1.enc j) &&& Op.w (nulWord != wd n X.2.enc j)) &&&
      ((wd n keep j ^^^ 1) &&& (Op.w (0 == wd n X.2.enc j) ^^^ 1)) := fun j hj => by
    have e1 := (colMap_post hn1).2 j hj; have e2 := (colMap_post hn2).2 j hj; have ez := (colMap_post hz).2 j hj
    have ea1 := (colMap_raw ha1).2.2.2 j hj; have enk := (colMap_raw hnk).2.2.2 j hj
    have enz := (colMap_raw hnz).2.2.2 j hj; have ea2 := (colMap_raw ha2).2.2.2 j hj
    have ef := (colMap_raw hf).2.2.2 j hj
    simp only [Op.eval, Except.ok.injEq] at e1 e2 ez ea1 enk enz ea2 ef
    simp only [wd]; rw [← ef, ← ea1, ← ea2, ← enk, ← enz, ← e1, ← e2, ← ez]
  have bit2 : ∀ c : UInt64, c < 2 → c = 0 ∨ c = 1 := fun c h => by
      have := UInt64.lt_iff_toNat_lt.1 h; simp at this
      exact (by omega : c.toNat = 0 ∨ c.toNat = 1).imp UInt64.toNat_inj.1 UInt64.toNat_inj.1
  have hfb : ∀ j < n.toNat, wd n f j < 2 := fun j hj => by
    rw [row j hj]
    have hk : wd n keep j = 0 ∨ wd n keep j = 1 := bit2 _ (hb j hj)
    rcases hw (nulWord != wd n X.1.enc j) with e1 | e1 <;> rcases hw (nulWord != wd n X.2.enc j) with e2 | e2 <;>
      rcases hw (0 == wd n X.2.enc j) with e3 | e3 <;> rcases hk with e4 | e4 <;> rw [e1, e2, e3, e4] <;> decide
  refine Classical.byContradiction fun hk1 => hT0 ?_
  have hk0 : wd n keep i = 0 := (bit2 _ (hb i i.2)).resolve_right hk1
  have hf1 : wd n f i ≠ 0 := by
    rw [row i i.2, hk0]
    simp [Op.w, Ne.symm h1, Ne.symm h2, Ne.symm h3, bne_iff_ne, beq_iff_eq]
  obtain ⟨j, -⟩ := (keep_holds hT hfb (X.row i) (X.row i)).2 ⟨i, hf1, rfl, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) j.2

/-- **`nulStepCol` denotes `nulStep`** at a verb that propagates null (`+ - *`): a row with a null operand is the null
    (`p`'s flag), else the step's word (`keep` `1`, `stepCols_spec`) or `nulWord` where `Ew.intStep` answers the null
    (`keep` `0`, by `arithOvf_keep` and, at a zero operand, `stepDen`). -/
theorem nulStepCol_den {n : USize} {x y : Opt .i64 n} {s : String} {k : UInt8} {o b : Op} {f : UInt64} {r : Enc}
    (hv : nulVerb k = some (o, b, f)) (hnf : ¬o.nulFold = some (b, f))
    (hr : Tab.nulStepCol s k n x.enc y.enc = .ok r) (hz : Enc.WF .i64 n r)
    (a : (Obj.prod (.opt .long) (.opt .long)).El) (w : (Obj.opt .long).El) :
    (⟨n, (x, y), (Opt.mk r hz : Opt .i64 n)⟩ : Tab (.prod (.opt .long) (.opt .long)) (.opt .long)).Holds a w ↔
      (∃ i, ValsB.row (o := false) (A := .prod (.opt .long) (.opt .long)) (x, y) i = a) ∧ Lang.nulStep k a w := by
  obtain ⟨rfl, rfl, -, hk⟩ : b = .or ∧ f = nulWord ∧ o.nulFold = none ∧ (k = Ew.add ∨ k = Ew.sub ∨ k = Ew.mul) := by
    rcases nulVerb_cases hv with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | h
    · exact absurd rfl hnf
    · exact absurd rfl hnf
    · exact h
  unfold Tab.nulStepCol at hr
  obtain ⟨p, hp, hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨x', hx', hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨y', hy', hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨⟨W, keep⟩, hst, hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨⟨⟩, hov, hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨c1, hc1, hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨d, hd, hr⟩ := Except.bind_eq_ok'.1 hr
  obtain ⟨q, hq, hr⟩ := Except.bind_eq_ok'.1 hr
  cases hr
  obtain ⟨hpw, hpi⟩ := kscan_nul_map (o := .min) rfl x.wf y.wf hp
  obtain ⟨-, hdw, hdn⟩ := colMap_closed (by rfl) hd
  obtain ⟨-, hqi⟩ := kscan_nul_map (o := .min) (post := []) rfl hdw hpw hq
  obtain ⟨-, hc1r⟩ := colMap_post hc1
  obtain ⟨-, -, -, hdr⟩ := colMap_chain hd
  have hspec := stepCols_spec hst
  have imax : ∀ v : UInt64, Op.min.eval v 0x7fffffffffffffff = .ok v := fun v => by
    simp only [Op.eval, Except.ok.injEq, Op.i]
    rw [if_neg]; intro h; rw [Int64.lt_iff_toInt_lt] at h; have := Int64.toInt_lt v.toInt64; simp at h this; omega
  have rz : ∀ i : Fin n.toNat, Lang.nulStep k (ValsB.row (o := false) (A := .prod (.opt .long) (.opt .long)) (x, y) i)
      (ValsB.row (o := false) (A := .opt .long) (Opt.mk q.1 hz : Opt .i64 n) i) := fun i => by
    show Lang.nulStep k (ValsB.row (o := false) (A := .opt .long) x i, ValsB.row (o := false) (A := .opt .long) y i) _
    rw [row_opt_i64, row_opt_i64, row_opt_i64]
    refine (Lang.nulStep_iff _ _ _).2 ⟨o, .or, nulWord, hv, ?_⟩
    obtain ⟨NP, ZP, hp1, hp2, hp3, hp4⟩ := hpi i
    obtain ⟨NQ, ZQ, hq1, hq2, hq3, hq4⟩ := hqi i
    have hd0 : rdNul n d i = 0 := by simp [rdNul, Verify.foRNuls_plain hdw hdn i.2]
    -- `p`'s word is `i64` max wherever its flag is `0`, so `rdFill` reads it as `i64` max at every row
    have hpf : rdFill 0x7fffffffffffffff .i64 n p.1 i = 0x7fffffffffffffff := by
      unfold rdFill; split
      · rfl
      · rename_i hn
        have hNP : NP = 0 := by rw [hp3] at hn; revert hn; split <;> simp_all
        refine (hp4 hNP).trans ?_; revert hp1
        cases Op.min.eval _ _ <;> simp [bind, Except.bind, chain, Op.eval] <;> exact fun h => (Except.ok.inj h).symm
    rw [hpf] at hq1; rw [hd0] at hq2
    rw [show chain ([] : List (Op × UInt64)) = (pure : UInt64 → Except String UInt64) from rfl, bind_pure] at hq1
    simp only [rdFill, hd0, bne_self_eq_false, Bool.false_eq_true, if_false, imax, Except.ok.injEq] at hq1
    -- both operands non-null: the answer word is `d`'s, `Ew.intStep` of the operands
    have hnn : rdNul n x.enc i = 0 → rdNul n y.enc i = 0 →
        (wd n d i).toInt64 = Ew.intStep k Alg.nul (wd n x.enc i).toInt64 (wd n y.enc i).toInt64 := fun hX hY => by
      have hfx : wd n x'.enc i = wd n x.enc i := by rw [fillNulCol_row x.wf hx' i, hX]; rfl
      have hfy : wd n y'.enc i = wd n y.enc i := by rw [fillNulCol_row y.wf hy' i, hY]; rfl
      obtain ⟨hb2, hsp⟩ := hspec i i.2
      rw [hfx, hfy] at hsp
      have hc := hc1r i i.2
      obtain ⟨u, v, m, e, hu, hv', hm, he, hde⟩ := hdr i i.2
      cases hu; cases hv'
      simp only [Op.eval, Except.ok.injEq] at hc hm
      simp only [chain, List.foldlM_cons, List.foldlM_nil, Op.eval, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at he
      have hdv : wd n d i = nulWord - (nulWord - wd n W.enc i) * wd n keep i := by
        simp only [wd, hde, if_neg (by decide : QAtomicType.i64 ≠ .u1), Option.getD_some]; rw [← he, ← hm, hc]
      have bit2 : ∀ c : UInt64, c < 2 → c = 0 ∨ c = 1 := fun c h => by
        have := UInt64.lt_iff_toNat_lt.1 h; simp at this
        exact (by omega : c.toNat = 0 ∨ c.toNat = 1).imp UInt64.toNat_inj.1 UInt64.toNat_inj.1
      have s1 : ∀ a b : UInt64, a - (a - b) * 1 = b := fun a b => by grind
      have s0 : ∀ a b : UInt64, a - (a - b) * 0 = a := fun a b => by grind
      rcases bit2 _ hb2 with hk0 | hk1
      · rw [hdv, hk0, s0]
        refine Classical.byContradiction fun hne => ?_
        have hnul : Alg.nul = nulWord.toInt64 := rfl
        have hsd : Lang.stepDen k ((wd n x.enc i).toInt64, (wd n y.enc i).toInt64)
            (Ew.intStep k Alg.nul (wd n x.enc i).toInt64 (wd n y.enc i).toInt64) := by
          have hX' : (wd n x.enc i).toInt64 ≠ Alg.nul := fun h => hne (by
            rw [h]; rcases hk with rfl | rfl | rfl <;> simp [Verify.Ew.intStep_add, Verify.Ew.intStep_sub,
              Verify.Ew.intStep_mul, hnul])
          have hY' : (wd n y.enc i).toInt64 ≠ Alg.nul := fun h => hne (by
            rw [h]; rcases hk with rfl | rfl | rfl <;> simp [Verify.Ew.intStep_add, Verify.Ew.intStep_sub,
              Verify.Ew.intStep_mul, hnul])
          by_cases hy0 : wd n y.enc i = 0
          · rw [hy0]
            rcases hk with rfl | rfl | rfl <;>
              simp (config := {decide := true}) [Lang.stepDen, Verify.Ew.intStep_add, Verify.Ew.intStep_sub,
                Verify.Ew.intStep_mul, Verify.Ew.intStep_idiv, hX'] <;>
              first | done | exact (Classical.em _).symm | (intro h; exact hX' (by rw [h]; decide))
          · have hw1 := arithOvf_keep hov (fun j hj => (hspec j hj).1) i
              (by show wd n x'.enc i ≠ _; rw [hfx]; intro h; exact hX' (by rw [h]; rfl))
              (by show wd n y'.enc i ≠ _; rw [hfy]; intro h; exact hY' (by rw [h]; rfl))
              (by show wd n y'.enc i ≠ _; rw [hfy]; exact hy0)
            rw [hk0] at hw1; exact absurd hw1 (by decide)
        obtain ⟨hk', -⟩ := (hsp _).2 hsd
        exact hk' hk0
      · rw [hdv, hk1, s1]
        exact ((hsp _).1 ⟨by rw [hk1]; decide, rfl⟩).1
    have hqe : (Opt.mk q.1 hz : Opt .i64 n).enc = q.1 := rfl
    rcases rdNul_bit n x.enc i with hX | hX <;> rcases rdNul_bit n y.enc i with hY | hY <;>
      simp only [hX, hY, Op.eval, Except.ok.injEq] at hp2 <;> subst hp2 <;>
      simp only [Op.eval, Except.ok.injEq] at hq2 <;> subst hq2 <;> simp (config := {decide := true}) at hp3 <;>
      simp (config := {decide := true}) only [hp3] at hq3 hq4 <;>
      simp (config := {decide := true}) [hX, hY, hq3, hqe, optWord]
    show (wd n q.1 i).toInt64 = _; rw [hq4 trivial, ← hq1]; exact hnn hX hY
  constructor
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, rz i⟩
  · rintro ⟨⟨i, rfl⟩, hw⟩; exact ⟨i, rfl, nulStep_fun (rz i) hw⟩

/-- **`Tab.arithOp` at `1+i64` denotes `nulStep`**: a source holding a null is read through `kscan_nul_row`, none
    through `colMap_raw` (the answer then holds none, `kscan_lock_closed`), both giving `nulStep_words` row by row. -/
theorem arithOp_opt_den {n : USize} {X : Vals (.prod (.opt .long) (.opt .long)) n}
    {T : Tab (.prod (.opt .long) (.opt .long)) (.opt .long)} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) (a : (Obj.prod (.opt .long) (.opt .long)).El)
    (w : (Obj.opt .long).El) : T.Holds a w ↔ (∃ i, X.row i = a) ∧ Lang.nulStep k a w := by
  obtain ⟨o, b, f, r, hz, hv, hr, rfl⟩ := arithOp_opt hs h
  obtain ⟨x, y⟩ := X
  change Opt .i64 n at x y
  by_cases hnf : o.nulFold = some (b, f)
  case neg =>
    rw [if_neg hnf] at hr
    exact nulStepCol_den hv hnf hr hz a w
  rw [if_pos hnf] at hr
  obtain ⟨r, hkr, rfl⟩ : ∃ r', kscan o false .i64 .i64 n none [(n, x.enc), (n, y.enc)] = .ok r' ∧ r'.1 = r := by
    revert hr; cases kscan o false .i64 .i64 n none [(n, x.enc), (n, y.enc)] <;>
      simp [Functor.map, Except.map]
  have ho : (o = .max ∨ o = .min) ∧ o.nulFold = some (b, f) := by
    refine ⟨?_, hnf⟩
    rcases nulVerb_cases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, h, -⟩
    · exact .inl rfl
    · exact .inr rfl
    · rw [h] at hnf; cases hnf
  obtain ⟨-, row⟩ := kscan_nul_map (post := []) ho.2 x.wf y.wf hkr
  have rz : ∀ i : Fin n.toNat, Lang.nulStep k (ValsB.row (o := false) (A := .prod (.opt .long) (.opt .long)) (x, y) i)
      (ValsB.row (o := false) (A := .opt .long) (Opt.mk r.1 hz : Opt .i64 n) i) := fun i => by
    obtain ⟨NZ, Z, h1, h2, h3, h4⟩ := row i
    rw [show chain ([] : List (Op × UInt64)) = (pure : UInt64 → Except String UInt64) from rfl, bind_pure] at h1
    show Lang.nulStep k (ValsB.row (o := false) (A := .opt .long) x i, ValsB.row (o := false) (A := .opt .long) y i) _
    rw [row_opt_i64, row_opt_i64, row_opt_i64]
    exact nulStep_words hv hnf (rdNul_bit n _ i) (rdNul_bit n _ i) h1 h2 h3 h4
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
          | (obtain ⟨-, -, -, -, -, -, -, rfl⟩ := arithOp_opt hl h; exact ⟨hX, fun _ h => absurd trivial h⟩)
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
  have hd : ∀ i : Fin n.toNat, ValsB.row (o := false) (A := .atom .date) (Arr.ofFn .date n fun j =>
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
    show _ = some (ValsB.row (o := false) (A := .atom .date) _ i)
    rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
  · rintro ⟨⟨i, rfl⟩, hb⟩
    refine ⟨i, ?_, rfl, ?_⟩
    · rw [hf i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
    · show ValsB.row (o := false) (A := .atom .date) _ i = _
      rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all

end Tab
end Rel
