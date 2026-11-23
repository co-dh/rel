module

public import Rel.RepAsc
public import Rel.RepTabDiv
public import Rel.Lang.DfnLaw
public import Rel.Run.SetOps

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The law of `Tab.sums` (`Rel/Run/SetOps.lean`): `canon` puts each key's rows in one run ascending in the position
(`kseen_runs`, the `i64` order codes), the segmented `kscan .add` holds at each row its key's prefix sum
(`segScan_ok`), a row's bad word is `0` exactly when its step is `plus` (`badWord_spec`, `stepDen_add_iff`), and the
segmented `kscan .or` keeps a row exactly when no step of its key up to it failed: the left fold `⦇[0, plus]⦈` of
`sumsDen` over the key's values up to the row. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Rel.Rep
open scoped Rel.Core.Rel

/-- Flipping the top bit `b` of a word of `b + 1` bits adds `2^b` below it and takes `2^b` off above it. -/
theorem Nat.xor_top {b x : Nat} (hx : x < 2 ^ (b + 1)) :
    x ^^^ 2 ^ b = if x < 2 ^ b then x + 2 ^ b else x - 2 ^ b := by
  have hb : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
  have key : ∀ y < 2 ^ b, y ^^^ 2 ^ b = y + 2 ^ b := fun y hy => by
    rw [Nat.add_comm]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i b with hi | rfl | hi
    · rw [Nat.testBit_two_pow_add_gt hi, decide_eq_false (by omega : ¬ b = i)]; simp
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]; simp
    · have h1 : 2 ^ b + y < 2 ^ i := Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) hi)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right
        (by omega) (Nat.le_of_lt hi))), decide_eq_false (by omega : ¬ b = i)]; simp
  split
  · exact key x ‹_›
  · have e := key (x - 2 ^ b) (by omega)
    rw [show x - 2 ^ b + 2 ^ b = x by omega] at e
    have e' : x ^^^ 2 ^ b = (x - 2 ^ b ^^^ 2 ^ b) ^^^ 2 ^ b := by rw [e]
    rw [e', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]






/-- `kseen` read every column it was given: `ascCol` answers on each. -/
theorem kseen_codes {n : USize} {es : List (AscKey × Enc)} {r : Nat × Enc × Enc} (h : kseen n es = .ok r) :
    ∃ cs, es.mapM (ascCol n) = .ok cs := by
  unfold kseen at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i kss heq
  obtain ⟨hlen, hf⟩ := mapM_ok heq
  have hok : ∀ e ∈ es, ∃ c, ascCol n e = .ok c := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨b, hb⟩ : ∃ b, kss[i]? = some b :=
      ⟨kss[i]'(by rw [hlen, List.length_zipIdx]; exact hi), List.getElem?_eq_getElem _⟩
    have he' := hf i (es[i], i) b (by simp [hi]) hb
    cases hce : ascCol n es[i] with
    | error s => simp [hce, Functor.map, Except.map, Except.mapError] at he'
    | ok c => exact ⟨c, rfl⟩
  clear h heq hf hlen
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    obtain ⟨c, hc⟩ := hok e List.mem_cons_self
    obtain ⟨cs, hcs⟩ := ih fun e' he' => hok e' (List.mem_cons_of_mem _ he')
    exact ⟨c :: cs, by simp [List.mapM_cons, hc, hcs, bind, Except.bind, pure, Except.pure]⟩

/-- Key columns on which two rows agree leave `lexLe` to the columns after them. -/
theorem lexLe_append_of_eq : ∀ (ks ks2 : List (Array UInt64)) {i j : Nat},
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0) → lexLe (ks ++ ks2) i j = lexLe ks2 i j
  | [], _, _, _, _ => rfl
  | c :: cs, ks2, i, j, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [lexLe, h.1, lexLe_append_of_eq cs ks2 h.2]

namespace Lang

/-- The left fold of `xs ++ [x]` is one step from the left fold of `xs`. -/
theorem foldDen_snoc {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)) (xs : List E.El) (x : E.El) (w : V.El) :
    foldDen Te TS (xs ++ [x]) w ↔ ∃ u, foldDen Te TS xs u ∧ TS (u, x) w := by
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hs, rfl⟩
    simp only [List.length_append, List.length_singleton] at hy
    refine ⟨ys[xs.length]'(by omega), ⟨ys.take (xs.length + 1), by simp; omega, ⟨a, by simpa using ha⟩,
      fun t ht => ?_, by simp⟩, ?_⟩
    · have := hs t (by simp; omega)
      simpa [List.getElem_append_left ht, List.getElem_take] using this
    · have := hs xs.length (by simp)
      simpa using this
  · rintro ⟨u, ⟨ys, hy, ⟨a, ha⟩, hs, rfl⟩, hS⟩
    refine ⟨ys ++ [w], by simp [hy], ⟨a, by rw [List.getElem_append_left (by omega)]; exact ha⟩, fun t ht => ?_,
      by simp [hy]⟩
    simp only [List.length_append, List.length_singleton] at ht
    by_cases ht' : t < xs.length
    · have := hs t ht'
      simpa [List.getElem_append_left ht', List.getElem_append_left (show t < ys.length by omega),
        List.getElem_append_left (show t + 1 < ys.length by omega)] using this
    · obtain rfl : t = xs.length := by omega
      simpa [List.getElem_append_left (show xs.length < ys.length by omega), hy] using hS

/-- `dom(T) (𝟙 × ≥) dom(T)` pointwise. -/
theorem upToDen_iff {K V : Obj} {t : QAtomicType} (T : Core.Rel (Obj.El (.prod K (.atom t))) (Obj.El V)) (a b : (Obj.prod K (.atom t)).El) :
    upToDen T a b ↔ (∃ c, T a c) ∧ (∃ c, T b c) ∧ a.1 = b.1 ∧ leAt t b.2 a.2 := by
  simp only [upToDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, Core.Rel.graph]
  constructor
  · rintro ⟨a', ⟨rfl, c, hc, -⟩, b', ⟨⟨k, hk1, hk2⟩, s, rfl, s', hs, rfl⟩, rfl, c', -, hc'⟩
    exact ⟨⟨c, hc⟩, ⟨c', hc'⟩, hk1.symm.trans hk2, hs⟩
  · rintro ⟨⟨c, hc⟩, ⟨c', hc'⟩, h1, h2⟩
    exact ⟨a, ⟨rfl, c, hc, hc⟩, b, ⟨⟨a.1, rfl, h1⟩, a.2, rfl, b.2, h2, rfl⟩, rfl, c', hc', hc'⟩

/-- **A `plus` step from a non-null sum, read from its wrapped result**: `v` and `acc + v` not the null and no wrap
(`Tab.sum`'s bad word at `0`, `badWord_spec`) exactly when `stepDen Ew.add` takes `(acc, v)` to `acc + v`. -/
theorem stepDen_add_word {acc v : Int64} (ha : acc ≠ Alg.nul) :
    (v ≠ Alg.nul ∧ acc + v ≠ Alg.nul ∧ ¬((v < 0 ↔ acc < 0) ∧ ¬(v < 0 ↔ acc + v < 0))) ↔
      stepDen Ew.add (acc, v) (acc + v) := by
  rw [stepDen_add_iff, Int64.add_comm acc v]
  have e := Int64.add_exact_iff v acc
  constructor
  · rintro ⟨hv, hn, ho⟩; have := e.1 ⟨hn, ho⟩; exact ⟨ha, hv, by omega, by omega, rfl⟩
  · rintro ⟨-, hv, h1, h2, -⟩; obtain ⟨hn, ho⟩ := e.2 ⟨by omega, by omega⟩; exact ⟨hv, hn, ho⟩

/-- **One `plus` step read from the words**: from a non-null sum `acc = W - v`, the step takes `(acc, v)` to `w`
exactly when the row's bad word is `0` and `w` is the row's sum `W`. -/
theorem sums_step {acc : Int64} (ha : acc ≠ Alg.nul) {v W bad : UInt64} (hWv : (W - v).toInt64 = acc)
    (hbad : bad = 0 ↔ v.toInt64 ≠ Alg.nul ∧ W.toInt64 ≠ Alg.nul ∧
      ¬((v.toInt64 < 0 ↔ (W - v).toInt64 < 0) ∧ ¬(v.toInt64 < 0 ↔ W.toInt64 < 0))) (w : Int64) :
    stepDen Ew.add (acc, v.toInt64) w ↔ bad = 0 ∧ w = W.toInt64 := by
  have hW : W.toInt64 = acc + v.toInt64 := by
    rw [← hWv]; show W.toInt64 = (W - v + v).toInt64; rw [UInt64.sub_add_cancel]
  rw [hbad, hWv, hW, stepDen_add_word ha]
  constructor
  · intro h; obtain ⟨-, -, -, -, rfl⟩ := (stepDen_add_iff _ _ _).1 h; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact h

/-- **The left fold of a run one row longer**: if the fold of the rows `P` is their sum `A` exactly when no row of `P`
is bad, so is the fold of `P ++ [q]` with `q`'s sum `W q`, `W q - v q = A`. -/
theorem sums_snoc {v W bad : Nat → UInt64} {P : List Nat} {A : Int64} {q : Nat}
    (hfold : ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      (P.map fun p => (v p).toInt64) w ↔ (∀ p ∈ P, bad p = 0) ∧ w = A)
    (hA : (∀ p ∈ P, bad p = 0) → A ≠ Alg.nul) (hsub : (W q - v q).toInt64 = A)
    (hbq : bad q = 0 ↔ (v q).toInt64 ≠ Alg.nul ∧ (W q).toInt64 ≠ Alg.nul ∧
      ¬(((v q).toInt64 < 0 ↔ (W q - v q).toInt64 < 0) ∧ ¬((v q).toInt64 < 0 ↔ (W q).toInt64 < 0))) (w : Int64) :
    foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      ((P ++ [q]).map fun p => (v p).toInt64) w ↔ (∀ p ∈ P ++ [q], bad p = 0) ∧ w = (W q).toInt64 := by
  rw [List.map_append, List.map_singleton, foldDen_snoc]
  simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  constructor
  · rintro ⟨u, hu, hs⟩
    obtain ⟨hb, rfl⟩ := (hfold u).1 hu
    have := (sums_step (hA hb) hsub hbq w).1 hs
    exact ⟨⟨hb, this.1⟩, this.2⟩
  · rintro ⟨⟨hb, hq⟩, rfl⟩
    exact ⟨A, (hfold A).2 ⟨hb, rfl⟩, (sums_step (hA hb) hsub hbq _).2 ⟨hq, rfl⟩⟩

/-- The rows `≤ t + 1` of `t + 1`'s group: those of `t`'s group when `t` is in it (groups are runs), then `t + 1`. -/
theorem groupRows_succ {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) {t : Nat} (ht : t + 1 < m) :
    (List.range (t + 2)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m (t + 1)) =
      (if g t = g (t + 1) then (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t) else []) ++
        [t + 1] := by
  have hG := (firsts_spec g m).2.2.1
  rw [List.range_succ, List.filter_append]
  congr 1
  · split
    · rename_i h
      apply List.filter_congr; intro q hq; rw [List.mem_range] at hq
      rw [decide_eq_decide, hG q (by omega) (t + 1) ht, hG q (by omega) t (by omega), h]
    · rename_i h
      apply List.filter_eq_nil_iff.2; intro q hq; rw [List.mem_range] at hq
      simp only [decide_eq_true_eq]; rw [hG q (by omega) (t + 1) ht]; intro hq'
      exact h ((hrun q t (t + 1) (by omega) (by omega) ht hq').trans hq')
  · simp

/-- **The prefix sums of a key, as a left fold**: over the rows `≤ t` of `t`'s group, `⦇[0, plus]⦈` of their values
is `t`'s scanned sum `W t` exactly when none of their bad words is set (`segScan_ok`, `badWord_spec`). -/
theorem sums_fold {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) (v W bad : Nat → UInt64)
    (hW : ∀ t < m, W t =
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v).foldl (· + ·) 0)
    (hbad : ∀ t < m, (bad t = 0 ↔ (v t).toInt64 ≠ Alg.nul ∧ (W t).toInt64 ≠ Alg.nul ∧
        ¬(((v t).toInt64 < 0 ↔ (W t - v t).toInt64 < 0) ∧ ¬((v t).toInt64 < 0 ↔ (W t).toInt64 < 0)))) :
    ∀ t < m, ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map fun q => (v q).toInt64) w ↔
      (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t), bad q = 0) ∧
        w = (W t).toInt64 := by
  have h0 : ∀ q < m, ((List.range (q + 1)).filter fun p => Verify.groupOf g m p = Verify.groupOf g m q) = [] ++ [q] →
      ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
        (([] ++ [q]).map fun p => (v p).toInt64) w ↔ (∀ p ∈ [] ++ [q], bad p = 0) ∧ w = (W q).toInt64 :=
    fun q hq e => sums_snoc (A := 0) (fun w => by rw [List.map_nil, foldDen_nil]; simp) (fun _ => by decide)
      (by rw [hW q hq, e]; simp) (hbad q hq)
  intro t
  induction t with
  | zero => intro ht; have e : ((List.range 1).filter fun p => Verify.groupOf g m p = Verify.groupOf g m 0) = [] ++ [0] := by simp
            rw [e]; exact h0 0 ht e
  | succ t ih =>
    intro ht
    have e := groupRows_succ hrun ht
    rw [e]
    split
    · rename_i hg
      have hmem : t ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t) := by simp
      refine sums_snoc (ih (by omega)) (fun hb => ((hbad t (by omega)).1 (hb t hmem)).2.1) ?_ (hbad (t + 1) ht)
      rw [hW (t + 1) ht, hW t (by omega), e, if_pos hg, List.map_append, List.foldl_append]; simp
    · rename_i hg; rw [if_neg hg] at e; exact h0 (t + 1) ht e

/-- `kscan .fadd`'s step as a total function, the `fn` `segScan_ok` folds (`Op.eval .fadd` never fails). -/
abbrev faddW (a x : UInt64) : UInt64 := match Op.eval .fadd a x with | .ok r => r | .error _ => 0

/-- **A left fold one element longer, row by row** (`foldDen_snoc`): where the fold over the rows `P` is exactly `A` when
no `bad` word of `P` is set, and the step from `A` at row `q` is exactly `B` when `bad q` is not, the fold over
`P ++ [q]` is exactly `B` when no bad word of `P ++ [q]` is set. -/
theorem foldDen_snoc_iff {E V : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {v : Nat → E.El} {bad : Nat → UInt64} {P : List Nat} {A B : V.El} {q : Nat}
    (hfold : ∀ y, foldDen Te TS (P.map v) y ↔ (∀ p ∈ P, bad p = 0) ∧ y = A)
    (hq : ∀ y, TS (A, v q) y ↔ bad q = 0 ∧ y = B) (y : V.El) :
    foldDen Te TS ((P ++ [q]).map v) y ↔ (∀ p ∈ P ++ [q], bad p = 0) ∧ y = B := by
  rw [List.map_append, List.map_singleton, foldDen_snoc]
  simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  constructor
  · rintro ⟨a, ha, hs⟩
    obtain ⟨hb, rfl⟩ := (hfold a).1 ha
    obtain ⟨h1, h2⟩ := (hq y).1 hs
    exact ⟨⟨hb, h1⟩, h2⟩
  · rintro ⟨⟨hb, h1⟩, rfl⟩
    exact ⟨A, (hfold A).2 ⟨hb, rfl⟩, (hq _).2 ⟨h1, rfl⟩⟩

/-- **The float sum of a key's rows, as words** (`sums_fold` at a float atom): `X q` the `f64` word of the value `v q`
(`fval`), `Z` that of `u`'s `0`; `R t` is `fto u` of the `faddW` fold from `Z` of `X` over the rows `≤ t` of `t`'s
group, and `bad t` is set exactly where `R t` is `2^63` (a NaN). Then `fsumDen u` of those rows' values is `R t` read at
`u`, exactly when no bad word among them is set. Words only: no property of `Float` is used. -/
theorem fsum_fold {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) {u : QAtomicType}
    (v : Nat → (Obj.atom u).El) (X R bad : Nat → UInt64) (hX : ∀ q < m, fval u (v q) = some (X q)) {Z : UInt64}
    (hZ : fval u (QAtomicType.ofBits u 0) = some Z)
    (hR : ∀ t < m, R t = Op.ftoWord u
      ((((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map X).foldl faddW Z))
    (hbad : ∀ t < m, (bad t = 0 ↔ R t ≠ 0x8000000000000000)) :
    ∀ t < m, ∀ w, fsumDen u (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v)
      w ↔ (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t), bad q = 0) ∧
        w = QAtomicType.ofBits u (R t) := by
  obtain ⟨Te, TS, hD, hTe, hTS⟩ : ∃ (Te : Core.Rel (Obj.El (.prod (.atom .f64) (.atom u)))
      (Obj.El (.prod (.atom .f64) (.atom u))))
      (TS : Core.Rel (Obj.El (.prod (.prod (.atom .f64) (.atom u)) (.atom u))) (Obj.El (.prod (.atom .f64) (.atom u)))),
      (∀ xs w, fsumDen u xs w ↔ ∃ y, foldDen Te TS xs y ∧ w = y.2) ∧
      (∀ y, foldDen Te TS [] y ↔ y = (Z, QAtomicType.ofBits u 0)) ∧
      (∀ (A : UInt64) r x Xx, fval u x = some Xx → ∀ y, TS ((A, r), x) y ↔
        Op.ftoWord u (faddW A Xx) ≠ 0x8000000000000000 ∧
          y = (faddW A Xx, QAtomicType.ofBits u (Op.ftoWord u (faddW A Xx)))) := by
    refine ⟨(Core.Rel.graph fun _ => QAtomicType.ofBits u 0) ≫ Core.Rel.rpair (fwideDen u) (𝟙 _),
      Core.Rel.rpair (Core.Rel.graph fun p : Obj.El (.prod (.prod (.atom .f64) (.atom u)) (.atom u)) => p.1.1)
        (Core.Rel.graph Prod.snd ≫ fwideDen u) ≫ faddDen ≫ Core.Rel.rpair (𝟙 _) (froundDen u),
      fun _ _ => Iff.rfl, fun y => ⟨?_, ?_⟩, fun A r x Xx hx y => ?_⟩
    · rintro ⟨ys, hy, ⟨_, hs⟩, -, rfl⟩
      obtain ⟨h1, h2⟩ := (Lang.fsumDen_seed u _ _).1 hs
      rw [h1] at h2; replace h2 := (Lang.fwideDen_iff _ _ _).1 h2; have h3 : some Z = some _ := hZ.symm.trans h2
      exact Prod.ext (Option.some.inj h3).symm h1
    · rintro rfl
      exact ⟨[(Z, QAtomicType.ofBits u 0)], rfl, ⟨(Z, QAtomicType.ofBits u 0), (Lang.fsumDen_seed u _ _).2 ⟨rfl, (Lang.fwideDen_iff _ _ _).2 hZ⟩⟩,
        fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩
    · have hfa : ∀ a b, Op.fadd.eval a b = .ok (faddW a b) := fun _ _ => rfl
      obtain ⟨y1, y2⟩ := y
      simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, Core.Rel.corefl, froundDen, Core.Rel.recip_apply, exists_eq_left, hfa, Except.ok.injEq,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨p1, p2⟩, ⟨rfl, h2⟩, s, rfl, rfl, R', hR', _, ⟨rfl, hn⟩, rfl⟩
        have h2 := (Option.some.inj (h2.symm.trans hx)); simp only at h2; subst h2
        cases hR'
        exact ⟨hn, rfl, rfl⟩
      · rintro ⟨hn, rfl, rfl⟩
        exact ⟨(A, Xx), ⟨rfl, hx⟩, _, rfl, rfl, _, rfl, _, ⟨rfl, hn⟩, rfl⟩
  -- the fold over pairs: the carry `C t` and its rounding
  have hC : ∀ t < m, ∀ y, foldDen Te TS
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v) y ↔
      (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t), bad q = 0) ∧
        y = ((((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map X).foldl faddW Z,
          QAtomicType.ofBits u (R t)) := by
    have hq : ∀ q < m, ∀ (A : UInt64) r, (((List.range (q + 1)).filter fun p => Verify.groupOf g m p =
        Verify.groupOf g m q).map X).foldl faddW Z = faddW A (X q) → ∀ y, TS ((A, r), v q) y ↔ bad q = 0 ∧
        y = ((((List.range (q + 1)).filter fun p => Verify.groupOf g m p = Verify.groupOf g m q).map X).foldl faddW Z,
          QAtomicType.ofBits u (R q)) := fun q hq A r e y => by
      rw [hTS A r (v q) (X q) (hX q hq) y, hbad q hq, hR q hq, e]
    have h0 : ∀ q < m, ((List.range (q + 1)).filter fun p => Verify.groupOf g m p = Verify.groupOf g m q) = [] ++ [q] →
        ∀ y, foldDen Te TS (([] ++ [q]).map v) y ↔ (∀ p ∈ [] ++ [q], bad p = 0) ∧
          y = ((([] ++ [q]).map X).foldl faddW Z, QAtomicType.ofBits u (R q)) := fun q hq' e => by
      refine foldDen_snoc_iff (A := (Z, QAtomicType.ofBits u 0)) (fun y => by rw [List.map_nil, hTe]; simp) ?_
      have := hq q hq' Z (QAtomicType.ofBits u 0) (by rw [e]; rfl)
      rwa [e] at this
    intro t
    induction t with
    | zero => intro ht; have e : ((List.range 1).filter fun p => Verify.groupOf g m p = Verify.groupOf g m 0) = [] ++ [0] := by simp
              rw [e]; exact h0 0 ht e
    | succ t ih =>
      intro ht
      have e := groupRows_succ hrun ht
      rw [e]
      split
      · rename_i hg
        refine foldDen_snoc_iff (ih (by omega)) ?_
        have := hq (t + 1) ht _ (QAtomicType.ofBits u (R t)) (by rw [e, if_pos hg, List.map_append, List.foldl_append]; rfl)
        rwa [e, if_pos hg] at this
      · rename_i hg; rw [if_neg hg] at e; exact h0 (t + 1) ht e
  intro t ht w
  rw [hD]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hb, rfl⟩ := (hC t ht y).1 hy
    exact ⟨hb, rfl⟩
  · rintro ⟨hb, rfl⟩
    exact ⟨_, (hC t ht _).2 ⟨hb, rfl⟩, rfl⟩

/-- **canon's order on the atom `t` is the language's** (`ltAt`, `leAt`): what `sums` needs of its positions, which
canon sorts by their order codes (`Obj.lt`) while `sumsDen` reads them in `leAt t`. -/
def OrdAt (t : QAtomicType) : Prop :=
  (∀ a b, Obj.lt (.atom t) a b ↔ ltAt t a b) ∧ ∀ a b, leAt t a b ↔ ltAt t a b ∨ a = b

/-- An `i64` word holding `n` reads back as `n`. -/
theorem i64_word (n : Int) (h1 : -2 ^ 63 ≤ n) (h2 : n < 2 ^ 63) :
    (QAtomicType.word .i64 (QAtomicType.ofNum .i64 n)).toInt64.toInt = n := by
  have e := QAtomicType.ofBits_word (t := .i64) (Int64.ofInt n) rfl
  simp only [QAtomicType.ofBits, QAtomicType.ofNum] at e ⊢
  rw [e, Int64.toInt_ofInt_of_le (by omega) (by omega)]

/-- **An integer word widened to `i64`** (`castWord r .i64`): its value, q's null `-2^63` where it is the null. -/
theorem castWord_int {r : QAtomicType} {s : Bool} {b : Nat} (hr : r.storeFmt? = some (.int s b))
    (hlo : -2 ^ 63 ≤ (QAtomicType.NumFmt.int s b).lo - 1) (x : UInt64)
    (hn : (QAtomicType.NumFmt.int s b).lo - 1 ≤ r.num (QAtomicType.ofBits r x) ∧ r.num (QAtomicType.ofBits r x) < 2 ^ 63) :
    (QAtomicType.castWord r .i64 x).toInt64.toInt =
      if (QAtomicType.NumFmt.int s b).lo ≤ r.num (QAtomicType.ofBits r x) then r.num (QAtomicType.ofBits r x)
      else -2 ^ 63 := by
  simp only [QAtomicType.castWord, QAtomicType.embed, QAtomicType.value, hr]
  split
  · simp only [Option.bind_some, QAtomicType.ofValue, (show QAtomicType.i64.storeFmt? = some (.int true 64) from rfl), QAtomicType.intOf, QAtomicType.NumFmt.lo,
      QAtomicType.NumFmt.hi]
    simp only [Int.le_refl, ↓reduceIte, Int.toNat_zero, Int.pow_zero, Int.mul_one, Option.bind_some]
    rw [if_pos (by constructor <;> omega)]
    exact i64_word _ (by omega) (by omega)
  · rfl

/-- The code of a signed `w`-byte word: its low `8w` bits with the top one flipped. -/
theorem ordCode_signed {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (u : UInt64) :
    (ordCode w false true u).toNat = (u.toNat % 2 ^ (8 * w) + 2 ^ (8 * w - 1)) % 2 ^ (8 * w) := by
  have hm := Verify.toNat_and_mask h1 h8 u
  have ht : ((2 ^ (8 * w - 1)).toUInt64 : UInt64).toNat = 2 ^ (8 * w - 1) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
  have hx := Nat.mod_lt u.toNat (Nat.two_pow_pos (8 * w))
  have e : 8 * w = 8 * w - 1 + 1 := by omega
  simp only [ordCode, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_xor, hm, ht]
  rw [e] at hx ⊢
  rw [Nat.add_sub_cancel, Nat.xor_top hx]
  have hb : 2 ^ (8 * w - 1 + 1) = 2 * 2 ^ (8 * w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hb] at hx ⊢
  generalize u.toNat % (2 * 2 ^ (8 * w - 1)) = m at hx ⊢
  generalize 2 ^ (8 * w - 1) = d at hx ⊢
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The code of an unsigned `w`-byte word: its low `8w` bits. -/
theorem ordCode_unsigned {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (u : UInt64) :
    (ordCode w false false u).toNat = u.toNat % 2 ^ (8 * w) := by
  simp only [ordCode, Bool.false_eq_true, ↓reduceIte]; exact Verify.toNat_and_mask h1 h8 u

/-- What the order proofs read off an integer-stored atom `t`: its storage atom `r`, width `w` bytes and signedness
`s`, its layout, and the range of `num`. -/
theorem intOrd_shape {t : QAtomicType} (h : t.intOrd = true) : ∃ r w s, t.ordNum = some r ∧
    r.storeFmt? = some (.int s (8 * w)) ∧ t.storeFmt? = some (.int s (8 * w)) ∧ ascLayout t = some (w, false, s) ∧
    (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ (s = false → w = 1) ∧ (∀ x, r.num (QAtomicType.ofBits r x) = t.num (QAtomicType.ofBits t x)) ∧
    ∀ v : (Obj.atom t).El, if s then -2 ^ (8 * w - 1) ≤ t.num v ∧ t.num v < 2 ^ (8 * w - 1)
      else 0 ≤ t.num v ∧ t.num v < 2 ^ (8 * w) := by
  cases t <;> first | exact absurd h (by decide) | skip
  case u8 => exact ⟨.u8, 1, false, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := v.toNat_lt; simp [QAtomicType.num]; omega⟩
  case char => exact ⟨.u8, 1, false, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := v.toNat_lt; simp [QAtomicType.num]; omega⟩
  case i8 => exact ⟨.i8, 1, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int8.le_toInt v; have := Int8.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i16 => exact ⟨.i16, 2, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int16.le_toInt v; have := Int16.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i32 => exact ⟨.i32, 4, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int32.le_toInt v; have := Int32.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case date => exact ⟨.i32, 4, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int32.le_toInt v; have := Int32.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i64 => exact ⟨.i64, 8, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int64.le_toInt v; have := Int64.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case datetime => exact ⟨.i64, 8, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int64.le_toInt v; have := Int64.toInt_lt v; simp [QAtomicType.num]; omega⟩

/-- An integer-stored atom's key is its `num` moved up by half its range when signed. -/
theorem key_num {t : QAtomicType} (h : t.intOrd = true) : ∃ off : Int, ∀ v : (Obj.atom t).El,
    Obj.key (.atom t) v = [(t.num v + off).toNat] ∧ 0 ≤ t.num v + off := by
  obtain ⟨r, w, s, -, -, hst, hl, hw, -, -, hb⟩ := intOrd_shape h
  refine ⟨if s then 2 ^ (8 * w - 1) else 0, fun v => ?_⟩
  have hs : t.storeFmt?.isSome := by rw [hst]; rfl
  have hg : t ≠ .general := by rintro rfl; cases hst
  have k := Obj.key_ordCode hl hg (QAtomicType.word t v) (fun e => by subst e; cases hst)
  have ho : (Dep.Carrier.of? t (.atom (Column.atomOfBits t (QAtomicType.word t v) hg))).getD default =
      QAtomicType.ofBits t (QAtomicType.word t v) := by
    cases t <;> first | rfl | exact absurd hs (by decide)
  rw [ho, QAtomicType.ofBits_word v hs] at k
  have hv := hb v
  have hu : (QAtomicType.word t v).toNat = (t.num v % 2 ^ 64).toNat := by
    simp [QAtomicType.word, UInt64.ofInt]; omega
  refine ⟨?_, ?_⟩
  · rw [k, List.cons.injEq]; refine ⟨?_, rfl⟩
    cases s
    · rw [ordCode_unsigned (by omega) (by omega), hu]
      rcases hw with rfl | rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
    · rw [ordCode_signed (by omega) (by omega), hu]
      rcases hw with rfl | rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
  · cases s <;> simp at hv ⊢ <;> omega


/-- `iordAt`'s orders at an integer-stored atom are those of `num`. -/
theorem iord_num {t : QAtomicType} (h : t.intOrd = true) (a b : (Obj.atom t).El) :
    (iordAt .lt t a b ↔ t.num a < t.num b) ∧ (iordAt .le t a b ↔ t.num a ≤ t.num b) := by
  obtain ⟨r, w, s, hr, hrs, hst, -, hw, hsw, hx, hb⟩ := intOrd_shape h
  have hs : t.storeFmt?.isSome := by rw [hst]; rfl
  have cw : ∀ x, (QAtomicType.castWord r .i64 x).toInt64.toInt =
      if (QAtomicType.NumFmt.int s (8 * w)).lo ≤ t.num (QAtomicType.ofBits t x) then t.num (QAtomicType.ofBits t x)
      else -2 ^ 63 := fun x => by
    have hv := hb (QAtomicType.ofBits t x)
    rw [← hx x]; refine castWord_int hrs ?_ x ?_
    · rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp [QAtomicType.NumFmt.lo]
    · rw [hx x]; rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp [QAtomicType.NumFmt.lo] at hv hsw ⊢ <;> omega
  have hv := hb a; have hv' := hb b
  have key : ∀ x y, QAtomicType.ofBits t x = a → QAtomicType.ofBits t y = b →
      ((QAtomicType.castWord r .i64 x).toInt64 < (QAtomicType.castWord r .i64 y).toInt64 ↔ t.num a < t.num b) ∧
      ((QAtomicType.castWord r .i64 x).toInt64 ≤ (QAtomicType.castWord r .i64 y).toInt64 ↔ t.num a ≤ t.num b) := by
    intro x y hxa hyb
    rw [Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le, cw, cw, hxa, hyb]
    generalize t.num a = A at *; generalize t.num b = B at *
    rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp only [QAtomicType.NumFmt.lo] at hv hv' ⊢ <;>
      simp at hv hv' ⊢ <;> split <;> split <;> (constructor <;> constructor <;> intro <;> omega)
  have elt : ∀ p q : UInt64, Op.eval .lt p q = .ok 1 ↔ p.toInt64 < q.toInt64 := fun p q => by
    rw [show Op.eval .lt p q = .ok (if decide (p.toInt64 < q.toInt64) = true then 1 else 0) from rfl]
    by_cases hp : p.toInt64 < q.toInt64 <;> simp [hp]
  have ele : ∀ p q : UInt64, Op.eval .le p q = .ok 1 ↔ p.toInt64 ≤ q.toInt64 := fun p q => by
    rw [show Op.eval .le p q = .ok (if decide (p.toInt64 ≤ q.toInt64) = true then 1 else 0) from rfl]
    by_cases hp : p.toInt64 ≤ q.toInt64 <;> simp [hp]
  constructor <;> constructor
  · rintro ⟨r', x, y, hr', hxa, hyb, he⟩
    rw [hr] at hr'; cases hr'; exact (key x y hxa hyb).1.1 ((elt _ _).1 he)
  · intro hl; exact ⟨r, _, _, hr, QAtomicType.ofBits_word a hs, QAtomicType.ofBits_word b hs,
      (elt _ _).2 ((key _ _ (QAtomicType.ofBits_word a hs) (QAtomicType.ofBits_word b hs)).1.2 hl)⟩
  · rintro ⟨r', x, y, hr', hxa, hyb, he⟩
    rw [hr] at hr'; cases hr'; exact (key x y hxa hyb).2.1 ((ele _ _).1 he)
  · intro hl; exact ⟨r, _, _, hr, QAtomicType.ofBits_word a hs, QAtomicType.ofBits_word b hs,
      (ele _ _).2 ((key _ _ (QAtomicType.ofBits_word a hs) (QAtomicType.ofBits_word b hs)).2.2 hl)⟩

/-- The order of an integer-stored atom's values, three ways, each the order of `num`: canon's (`Obj.lt`), `ltAt`'s,
`leAt`'s; and `num` is one to one. -/
theorem num_order {t : QAtomicType} (h : t.intOrd = true) (a b : (Obj.atom t).El) :
    (Obj.lt (.atom t) a b ↔ t.num a < t.num b) ∧ (ltAt t a b ↔ t.num a < t.num b) ∧
      (leAt t a b ↔ t.num a ≤ t.num b) ∧ (t.num a = t.num b → a = b) := by
  have hs : t.storeFmt?.isSome := by
    obtain ⟨_, _, _, _, _, hst, _⟩ := intOrd_shape h; rw [hst]; rfl
  obtain ⟨off, hk⟩ := key_num h
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · obtain ⟨ka, ha⟩ := hk a; obtain ⟨kb, hb⟩ := hk b
    simp only [Obj.lt, ka, kb, List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false]
    omega
  · cases t <;> first | exact absurd h (by decide) | exact (iord_num h a b).1 | exact Int64.lt_iff_toInt_lt
  · cases t <;> first | exact absurd h (by decide) | exact (iord_num h a b).2 | exact Int64.le_iff_toInt_le
  · rw [← QAtomicType.ofBits_word a hs, ← QAtomicType.ofBits_word b hs]
    simp only [QAtomicType.word, e]

/-- **canon's order is the value order at every integer-stored atom** (`u8 i8 i16 i32 i64 char date datetime`). -/
theorem ordAt_int {t : QAtomicType} (h : t.intOrd = true) : OrdAt t :=
  ⟨fun a b => (num_order h a b).1.trans (num_order h a b).2.1.symm, fun a b => by
    obtain ⟨-, h2, h3, h4⟩ := num_order h a b
    rw [h2, h3]; constructor
    · intro hl; rcases Int.lt_or_eq_of_le hl with e | e
      · exact .inl e
      · exact .inr (h4 e)
    · rintro (e | rfl)
      · exact Int.le_of_lt e
      · exact Int.le_refl _⟩

-- floats are left out: `Obj.lt` orders bits by totalOrder (`-0.0 < 0.0`, NaN last) and `ltAt` is IEEE's (neither holds)
/-- **The row `lt` is the definition `Tm.ltDef`** at every integer-stored atom (`ordDen` is the row's meaning,
    `Tab.cmpPairs` its code, `Tab.cmpPairs_holds`): `ltAt t` is `Obj.lt` there (`ordAt_int`). -/
theorem Tm.lt_row_den (ρ : Val) {t : QAtomicType} (h : t.intOrd = true) :
    ordDen true (.atom t) = (Tm.ltDef (.atom t)).den ρ := by
  rw [Tm.lt_den]; funext p q; apply propext; rw [ordDen_iff]; simp only [if_true, (ordAt_int h).1]

/-- Only an atom with an order code (`ascOrd`) can have canon's order be `ltAt`: `u1`'s `false < true` has
no `ltAt`, and a `general` value is not `leAt` itself. -/
theorem OrdAt.ascOrd {t : QAtomicType} (h : OrdAt t) : ∃ f, ascOrd t = some f := by
  cases t
  case u1 => exact absurd ((h.1 false true).1 (by decide)) (by simp [ltAt, iordAt, QAtomicType.ordNum,
    QAtomicType.numFmt?])
  case general => exact absurd ((h.2 default default).2 (.inr rfl)) (by simp [leAt, iordAt, QAtomicType.ordNum,
    QAtomicType.numFmt?])
  all_goals exact ⟨_, rfl⟩

end Lang

/-- **`sumsDen` on a table of distinct keys whose groups `grp` (equal `κ`) ascend in `ν` with the row**: `(κ, ν)` to
the left fold over the values of the rows `≤ t` of `t`'s group, `t` the row of `(κ, ν)`. -/
theorem sumsDen_rows {K : Obj} {t u : QAtomicType} (hord : Lang.OrdAt t) (C : Tab (.prod K (.atom t)) (.atom u))
    (grp : Nat → Nat) (hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j)
    (hG : ∀ i j : Fin C.n.toNat, grp i = grp j ↔ (C.key.row i).1 = (C.key.row j).1)
    (hO : ∀ i j : Fin C.n.toNat, i.1 < j.1 → (C.key.row i).1 = (C.key.row j).1 →
      Obj.lt (.atom t) (C.key.row i).2 (C.key.row j).2) (a : (Obj.prod K (.atom t)).El) (w : (Obj.atom u).El) :
    Lang.sumsDen (rep C) a w ↔ ∃ t : Fin C.n.toNat, C.key.row t = a ∧
      Lang.sumDen u
        (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
          if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default) w := by
  have hR : ∀ b v, rep C b v ↔ ∃ i, C.key.row i = b ∧ C.val.row i = v := fun _ _ => Iff.rfl
  have hU : ∀ b c, Lang.upToDen (rep C) b c ↔ (∃ v, rep C b v) ∧ (∃ v, rep C c v) ∧ b.1 = c.1 ∧
      Lang.leAt t c.2 b.2 := fun b c => Lang.upToDen_iff _ b c
  have hle : ∀ y, Lang.leAt t y y := fun y => (hord.2 y y).2 (.inr rfl)
  have hP : ∀ t : Fin C.n.toNat, ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t),
      q < C.n.toNat ∧ q ≤ t.1 ∧ grp q = grp t := fun t q hq => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hq; exact ⟨by omega, by omega, hq.2⟩
  let kAt (t : Fin C.n.toNat) (q : Nat) : (Obj.prod K (.atom _)).El :=
    if hq : q < C.n.toNat then C.key.row ⟨q, hq⟩ else C.key.row t
  have hM : ∀ t : Fin C.n.toNat, ∀ b, b ∈ ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t) ↔
      (∃ v, rep C b v) ∧ (C.key.row t).1 = b.1 ∧ Lang.leAt _ b.2 (C.key.row t).2 := by
    intro t b
    rw [List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqn, hqt, hg⟩ := hP t q hq
      simp only [kAt, dif_pos hqn]
      refine ⟨⟨_, (hR _ _).2 ⟨⟨q, hqn⟩, rfl, rfl⟩⟩, ((hG ⟨q, hqn⟩ t).1 hg).symm, ?_⟩
      rcases Nat.lt_or_ge q t.1 with h | h
      · exact (hord.2 _ _).2 (.inl ((hord.1 _ _).1 (hO ⟨q, hqn⟩ t h ((hG ⟨q, hqn⟩ t).1 hg))))
      · obtain rfl : t = ⟨q, hqn⟩ := Fin.ext (show t.1 = q by omega); exact hle _
    · rintro ⟨⟨v, hv⟩, h1, h2⟩
      obtain ⟨q, rfl, -⟩ := (hR _ _).1 hv
      refine ⟨q.1, ?_, by simp only [kAt, dif_pos q.2]⟩
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨?_, (hG q t).2 h1.symm⟩
      apply Nat.lt_of_not_le; intro hc
      have := hO t q (by omega) h1
      rcases (hord.2 _ _).1 h2 with e | e
      · exact Obj.lt_asymm _ this ((hord.1 _ _).2 e)
      · rw [e] at this; exact Obj.lt_irrefl _ _ this
  have hS : ∀ t : Fin C.n.toNat,
      (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)).Pairwise (Obj.prod K (.atom _)).lt := by
    intro t
    rw [List.pairwise_map]
    refine ((List.pairwise_lt_range).filter _).imp_of_mem fun {q q'} hq hq' hlt => ?_
    obtain ⟨hqn, -, hg⟩ := hP t q hq; obtain ⟨hqn', -, hg'⟩ := hP t q' hq'
    simp only [kAt, dif_pos hqn, dif_pos hqn']
    have e := (hG ⟨q, hqn⟩ ⟨q', hqn'⟩).1 (hg.trans hg'.symm)
    exact (Obj.lt_prod _ _ _ _ _ _).2 (Or.inr ⟨congrArg _ e, hO ⟨q, hqn⟩ ⟨q', hqn'⟩ hlt e⟩)
  have hrow : ∀ i : Fin C.n.toNat, ∀ v, rep C (C.key.row i) v ↔ v = C.val.row i := fun i v => by
    rw [hR]; constructor
    · rintro ⟨j, hj, rfl⟩; rw [hD j i hj]
    · rintro rfl; exact ⟨i, rfl, rfl⟩
  -- the values at the rows of `t`'s run are what `mapDen` pairs with its keys
  have hV : ∀ t : Fin C.n.toNat, ∀ vs : List (Obj.atom u).El,
      Lang.mapDen (rep C) (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)) vs ↔
      vs = ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default := by
    intro t vs; rw [Lang.mapDen_iff]
    have hval : ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t), ∀ v,
        rep C (kAt t q) v ↔ v = if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default := fun q hq v => by
      have hqn := (hP t q hq).1
      simp only [kAt, dif_pos hqn]; exact hrow _ v
    constructor
    · rintro ⟨hlen, hvs⟩
      apply List.ext_getElem (by simpa using hlen)
      intro i hi hi'
      have := hvs i (by simpa [← hlen] using hi) hi
      simp only [List.getElem_map] at this ⊢
      exact (hval _ (List.getElem_mem _) _).1 this
    · rintro rfl
      refine ⟨by simp, fun i hi hi' => ?_⟩
      simp only [List.getElem_map]
      exact (hval _ (List.getElem_mem _) _).2 rfl
  simp only [Lang.sumsDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
  constructor
  · rintro ⟨a', ⟨rfl, b, hb, -⟩, ys, ⟨hys, hmem⟩, vs, hmap, hf⟩
    obtain ⟨⟨c, hc⟩, -⟩ := (hU _ _).1 hb
    obtain ⟨t, rfl, -⟩ := (hR _ _).1 hc
    have hy : ys = ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t) :=
      lt_sorted_unique hys (hS t) fun b => (hmem b).trans ((hU _ _).trans
        ⟨fun ⟨_, h⟩ => (hM t b).2 h, fun h => ⟨⟨_, (hR _ _).2 ⟨t, rfl, rfl⟩⟩, (hM t b).1 h⟩⟩)
    subst hy
    exact ⟨t, rfl, (hV t vs).1 hmap ▸ hf⟩
  · rintro ⟨t, rfl, hf⟩
    have hd : ∃ v, rep C (C.key.row t) v := ⟨_, (hR _ _).2 ⟨t, rfl, rfl⟩⟩
    exact ⟨_, ⟨rfl, _, (hU _ _).2 ⟨hd, hd, rfl, hle _⟩, (hU _ _).2 ⟨hd, hd, rfl, hle _⟩⟩, _,
      ⟨hS t, fun b => ((hM t b).trans ⟨fun h => ⟨hd, h⟩, fun ⟨_, h⟩ => h⟩).trans (hU _ _).symm⟩, _,
      (hV t _).2 rfl, hf⟩

namespace Tab

/-- **`canon` ascends in `ν` within a `κ`**: its rows are sorted by the codes of `κ`'s columns, then `ν`'s, then the
value's (`canon_sorted`), so two distinct rows of one `κ` ascend strictly in `ν`. -/
theorem canon_pos_lt {K : Obj} {t u : QAtomicType} {f : UInt64 → UInt64} (hf : ascOrd t = some f)
    {x C : Tab (.prod K (.atom t)) (.atom u)} (hC : x.canon = .ok C) (hw : x.WF)
    (hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j) (i j : Fin C.n.toNat) (hij : i.1 < j.1)
    (hk : (C.key.row i).1 = (C.key.row j).1) : Obj.lt (.atom t) (C.key.row i).2 (C.key.row j).2 := by
  obtain ⟨es, cs, hes, hcs⟩ := canon_codes hC
  obtain ⟨sel, hsel, hord⟩ := canon_sorted hC hes
  have hki : ∀ j, C.key.row j = x.key.row (sel j) := fun j => congrArg Prod.fst (hsel j)
  cases heK : ValsB.cols x.key.1 with
  | error s => simp [ValsB.cols, heK, bind, Except.bind] at hes
  | ok eK =>
  have hes' : es = eK ++ [(.atom t, Arr.enc x.key.2), (.atom u, Arr.enc (t := u) x.val)] := by
    simp only [ValsB.cols, heK, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hes; rw [← hes]; simp; exact ⟨rfl, rfl⟩
  rw [hes'] at hcs
  obtain ⟨csK, csP, hcsK, hcsP, -⟩ := mapM_append_ok hcs
  obtain ⟨cs1, -, hcs1, -, -⟩ := mapM_append_ok (l1 := [(AscKey.atom t, Arr.enc x.key.2)])
    (l2 := [(AscKey.atom u, Arr.enc (t := u) x.val)]) hcsP
  have hκ : x.key.1.row (sel i) = x.key.1.row (sel j) := by rw [hki, hki] at hk; exact hk
  have hcode := Vals.codes_of_row x.key.1 hw.1.1 heK hcsK (sel i) (sel j) hκ
  have hlex := (hord i j hij).1
  rw [hes', ascKeys_append, lexLe_append_of_eq _ _ hcode] at hlex
  have hg : t ≠ .general := by rintro rfl; simp [ascOrd, ascLayout, orderKind] at hf
  have hv := (Arr.eq_of_codes x.key.2 hcs1).1
  obtain ⟨a, ha, hua, hga⟩ := Arr.get_raw_atom x.key.2 hg (sel i)
  obtain ⟨b, hb, hub, hgb⟩ := Arr.get_raw_atom x.key.2 hg (sel j)
  simp only [ascKeys, ascKey, nulCodes, nulWords, Arr.plain, Bool.false_eq_true, ↓reduceIte, List.nil_append,
    List.cons_append, lexLe, Array.getElem?_map, ha, hb,
    Option.map_some, Option.getD_some, hf, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at hlex
  obtain ⟨⟨w, fl, sg⟩, hL⟩ : ∃ L, ascLayout t = some L := by
    cases hL : ascLayout t <;> simp [ascOrd, hL] at hf ⊢
  have hfL : f = ordCode w fl sg := by simp [ascOrd, hL] at hf; exact hf.symm
  rw [hki, hki]
  show Obj.lt (.atom t) (ValsB.row (A := .atom t) x.key.2 (sel i)) (ValsB.row (A := .atom t) x.key.2 (sel j))
  rw [Vals.row_atom, Vals.row_atom, hga, hgb]
  unfold Obj.lt
  rw [Obj.key_ordCode hL hg a hua, Obj.key_ordCode hL hg b hub, ← hfL]
  rcases hlex with h | ⟨h, -⟩
  · simp only [List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false]
    exact UInt64.lt_iff_toNat_lt.1 h
  · -- equal codes are one position, and two rows of one `κ` at one position are one row
    have e := (Verify.ascOrd_atom hf hg fun h => ⟨hua h, hub h⟩).1 h
    have hne : C.key.row i ≠ C.key.row j := fun e => absurd (hD i j e) (fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij)
    refine absurd (Prod.ext hk ?_) hne
    rw [hki, hki]
    show ValsB.row (A := .atom t) x.key.2 (sel i) = ValsB.row (A := .atom t) x.key.2 (sel j)
    rw [Vals.row_atom, Vals.row_atom, hga, hgb, e]

/-- **A word cut to the width of an atom of a sum reads as the word** (`ofBits` keeps the low `8w` bits). -/
theorem _root_.Rel.QAtomicType.ofBits_cut {u : QAtomicType} (hu : u = .i64 ∨ u = .f32 ∨ u = .f64) {w : Nat}
    (hw : u.width = some w) (x : UInt64) :
    QAtomicType.ofBits u (UInt64.ofNat (x.toNat % 2 ^ (8 * w))) = QAtomicType.ofBits u x := by
  rcases hu with rfl | rfl | rfl <;> cases hw
  · show (UInt64.ofNat (x.toNat % 2 ^ 64)).toInt64 = x.toInt64; rw [ofNat_toNat_mod64]
  · show (UInt64.ofNat (x.toNat % 2 ^ 32)).toUInt32 = x.toUInt32; apply UInt32.toNat_inj.mp; simp
  · exact ofNat_toNat_mod64 x

/-- An array of a sum's atom (`i64`, `f32`, `f64`) holds at `i` its whole word read at the atom (`Arr.get_word`, the
`foR` read cut to the atom's width, `raw_foR_cut`; `Arr.get_i64` at `i64`, where a column may be `pos`). -/
theorem _root_.Rel.Arr.get_ofBits {u : QAtomicType} (hu : u = .i64 ∨ u = .f32 ∨ u = .f64) {N : USize} (y : Arr u N)
    (i : Fin N.toNat) : y.get i = QAtomicType.ofBits u ((Enc.raw .i64 N y.enc)[i.1]?.getD 0) := by
  rcases hu with rfl | hu
  · exact Arr.get_i64 y i
  obtain ⟨w, hw⟩ : ∃ w, u.width = some w := by rcases hu with rfl | rfl <;> exact ⟨_, rfl⟩
  have hu1 : u ≠ .u1 := by rcases hu with rfl | rfl <;> decide
  have hw' := y.wf
  rw [Arr.get_word y (by rcases hu with rfl | rfl <;> decide) i]
  cases hc : y.enc with
  | foR M P =>
    rw [raw_foR_cut hw hu1 N rfl, Array.getElem?_map]
    cases (Enc.raw .i64 N (.foR M P))[i.1]? with
    | none => rfl
    | some x => exact QAtomicType.ofBits_cut (.inr hu) hw x
  | _ => rw [hc] at hw'; rcases hu with rfl | rfl <;> simp [Enc.WF] at hw'

/-- **The sum of no elements is `0`** at every atom of a sum. -/
theorem _root_.Rel.Lang.sumDen_nil {u : QAtomicType} (hu : u = .i64 ∨ u = .f32 ∨ u = .f64) (c : (Obj.atom u).El) :
    Lang.sumDen u [] c ↔ c = QAtomicType.ofBits u 0 := by
  rcases hu with rfl | hu
  · exact Lang.foldDen_nil _ _ _
  obtain ⟨X, hX⟩ : ∃ X, fval u (QAtomicType.ofBits u 0) = some X := by rcases hu with rfl | rfl <;> exact ⟨_, rfl⟩
  have hsd : Lang.sumDen u = Lang.fsumDen u := by rcases hu with rfl | rfl <;> rfl
  rw [hsd]
  constructor
  · rintro ⟨y, ⟨ys, hy, ⟨_, hs⟩, -, rfl⟩, rfl⟩; exact ((Lang.fsumDen_seed u _ _).1 hs).1
  · rintro rfl
    exact ⟨(X, _), ⟨[(X, QAtomicType.ofBits u 0)], rfl, ⟨(X, QAtomicType.ofBits u 0), (Lang.fsumDen_seed u _ _).2 ⟨rfl, (Lang.fwideDen_iff _ _ _).2 hX⟩⟩,
      fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩, rfl⟩

/-- **`sumTail`'s bad column holds no null**: at either type it is a `colMap .or` (`colMap_plain`). -/
theorem sumTail_plain {what : String} {u : QAtomicType} {n : USize} {seg v bad : Enc} {W : Arr u n}
    (h : Tab.sumTail what u n seg v = .ok (W, bad)) : hasNul bad = false := by
  cases u <;> simp only [Tab.sumTail, Tab.sumTailF, bind, Except.bind] at h
  all_goals (repeat' split at h)
  all_goals try cases h
  all_goals rename_i hb; exact (colMap_closed (by lockstep) hb).2.2

/-- **`sumTailF` is `Lang.fsumDen` of each run up to each row**: one segmented `kscan .fadd` (`runScanChain_ok`), each
word of `v` read at `u` and widened (`widen_fval`), the seed `u`'s `0` widened likewise, each row's carry rounded once by
`fto u`; read whole (`kscan_i64`) a row's word is `2^63` exactly at a NaN, which sets its bad word
(`Lang.fsum_fold`). -/
theorem sumTailF_fold {α : Type} [DecidableEq α] {u : QAtomicType} (hu : u = .f32 ∨ u = .f64) {n : USize}
    {Kk : Nat → α} (hruns : ∀ a b c, a ≤ b → b ≤ c → c < n.toNat → Kk a = Kk c → Kk b = Kk a) {seg z v bad : Enc}
    {W : Arr u n} (hsu : ∀ i < n.toNat, ((Enc.raw .u1 n seg)[i]?.getD 0 = 0 ↔ i ∉ firstsOf Kk n.toNat))
    (hz : colConst n 0 = .ok z) (h : Tab.sumTailF u n seg z v = .ok (W, bad)) :
    ∀ t (ht : t < n.toNat),
      ((Enc.raw .i64 n bad)[t]?.getD 0 = 0 ∨ (Enc.raw .i64 n bad)[t]?.getD 0 = 1) ∧ ∀ w : (Obj.atom u).El,
        Lang.sumDen u
          (((List.range (t + 1)).filter fun q => Verify.groupOf Kk n.toNat q = Verify.groupOf Kk n.toNat t).map
            fun q => QAtomicType.ofBits u ((Enc.raw u n v)[q]?.getD 0)) w ↔
        (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf Kk n.toNat q = Verify.groupOf Kk n.toNat t),
          (Enc.raw .i64 n bad)[q]?.getD 0 = 0) ∧ w = W.get ⟨t, ht⟩ := by
  simp only [Tab.sumTailF, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨W0, hW0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨r2, hk⟩ : ∃ r2, kscan .fadd false u u n seg [(n, z), (n, v)] (widen u) [(.fto u, 0)] = .ok (W0.enc, r2) := by
    unfold scanArr at hW0; split at hW0
    · rename_i r hr; cases hW0; exact ⟨r.2, hr⟩
    · cases hW0
  obtain ⟨w0, hw0, hw8⟩ : ∃ w0, u.width = some w0 ∧ w0 ≤ 8 := by rcases hu with rfl | rfl <;> exact ⟨_, rfl, by omega⟩
  have hu1 : u ≠ .u1 := by rcases hu with rfl | rfl <;> decide
  have hsd : Lang.sumDen u = Lang.fsumDen u := by rcases hu with rfl | rfl <;> rfl
  -- a word read at `u` through `widen u`, and its element's `f64` word
  obtain ⟨pw, hpw⟩ : ∃ pw : UInt64 → UInt64, ∀ a, chain (widen u) a = .ok (pw a) ∧
      fval u (QAtomicType.ofBits u a) = some (pw a) :=
    ⟨fun a => match chain (widen u) a with | .ok x => x | .error _ => 0, fun a => by
      obtain ⟨X, hX, hf⟩ := widen_fval hu a; constructor <;> simp only [hX, hf]⟩
  -- the seed: `colConst n 0` read at `u` is `0`
  have hz0 : ∀ i < n.toNat, pw ((Enc.raw u n z)[i]?.getD 0) = pw 0 := fun i hi => by
    obtain ⟨hfo, -⟩ := raw_scatter 0 .pos .pos n 0 z rfl hz
    rw [raw_foR_cut hw0 hu1 n hfo, colConst_raw hz, Array.getElem?_map, Array.getElem?_replicate, if_pos hi]
    rfl
  have hop : ∀ a x, Op.fadd.eval a x = .ok (Lang.faddW a x) := fun _ _ => rfl
  have hpost : ∀ a, chain [(.fto u, 0)] a = .ok (Op.ftoWord u a) := fun _ => rfl
  have hst : kscanStream .fadd [(n, z), (n, v)] (widen u) [(.fto u, 0)] = false := kscanStream_ne (by decide) _ _ _
  have hU := (runScanChain_ok hop (by decide) hw0 hruns (fun a => (hpw a).1) hpost hsu hz0 hst hk).2
  obtain ⟨r3, hk64⟩ := kscan_i64 hw0 hu1 hk
  have h64 := (runScanChain_ok (w := 8) hop (by decide) rfl hruns (fun a => (hpw a).1) hpost hsu hz0 hst hk64).2
  simp only [if_neg hu1, if_neg (show QAtomicType.i64 ≠ .u1 by decide)] at hU h64
  have h64' : ∀ q < n.toNat, (Enc.raw .i64 n W0.enc)[q]?.getD 0 = Op.ftoWord u
      ((((List.range (q + 1)).filter fun p => Verify.groupOf Kk n.toNat p = Verify.groupOf Kk n.toNat q).map
        fun p => pw ((Enc.raw u n v)[p]?.getD 0)).foldl Lang.faddW (pw 0)) := fun q hq => by
    rw [h64 q hq]; exact ofNat_toNat_mod64 _
  have hB : ∀ q < n.toNat, (Enc.raw .i64 n b)[q]?.getD 0 =
      if (0x8000000000000000 : UInt64) = (Enc.raw .i64 n W0.enc)[q]?.getD 0 then 1 else 0 :=
    fun q hq => eval_eq_word ((colMap_post hb).2 q hq)
  have hF := Lang.fsum_fold hruns (fun q => QAtomicType.ofBits u ((Enc.raw u n v)[q]?.getD 0))
    (fun q => pw ((Enc.raw u n v)[q]?.getD 0)) (fun q => (Enc.raw .i64 n W0.enc)[q]?.getD 0)
    (fun q => (Enc.raw .i64 n b)[q]?.getD 0) (fun q _ => (hpw _).2) (hpw 0).2 h64'
    (fun q hq => by
      simp only [hB q hq]
      by_cases e : (Enc.raw .i64 n W0.enc)[q]?.getD 0 = 0x8000000000000000
      · simp [e]
      · simp [e, Ne.symm e])
  intro t ht
  refine ⟨by rw [hB t ht]; split <;> simp, fun w => ?_⟩
  rw [hsd, hF t ht w, Arr.get_word W0 (by rcases hu with rfl | rfl <;> decide), hU t ht,
    QAtomicType.ofBits_cut (.inr hu) hw0, ← h64' t ht]

/-- **`sumTail` is the left fold `⦇[0, plus]⦈` of each run up to each row** (`sums` per key, `sum` per cell): `Kk`
names the runs and `seg` marks their first rows (`runScan_ok`); row `t` of `W` is the fold of `stepAt u add` from `0`
over `v` at the rows `≤ t` of `t`'s run exactly when no bad word among them is set. At `i64` the bad word is a step that
wrapped or met the null (`badWord_spec`, `Lang.sums_fold`); at a float atom one whose rounding is `2^63` (`sumTailF_fold`). -/
theorem sumTail_fold {α : Type} [DecidableEq α] {what : String} {u : QAtomicType} {n : USize} {Kk : Nat → α}
    (hruns : ∀ a b c, a ≤ b → b ≤ c → c < n.toNat → Kk a = Kk c → Kk b = Kk a) {seg v bad : Enc} {W : Arr u n}
    (hsu : ∀ i < n.toNat, ((Enc.raw .u1 n seg)[i]?.getD 0 = 0 ↔ i ∉ firstsOf Kk n.toNat))
    (h : Tab.sumTail what u n seg v = .ok (W, bad)) :
    (u = .i64 ∨ u = .f32 ∨ u = .f64) ∧ ∀ t (ht : t < n.toNat),
      ((Enc.raw .i64 n bad)[t]?.getD 0 = 0 ∨ (Enc.raw .i64 n bad)[t]?.getD 0 = 1) ∧ ∀ w : (Obj.atom u).El,
        Lang.sumDen u
          (((List.range (t + 1)).filter fun q => Verify.groupOf Kk n.toNat q = Verify.groupOf Kk n.toNat t).map
            fun q => QAtomicType.ofBits u ((Enc.raw u n v)[q]?.getD 0)) w ↔
        (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf Kk n.toNat q = Verify.groupOf Kk n.toNat t),
          (Enc.raw .i64 n bad)[q]?.getD 0 = 0) ∧ w = W.get ⟨t, ht⟩ := by
  cases u
  case i64 =>
    simp only [Tab.sumTail, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Ws, W2⟩, hr, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sv, hsv, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨d, hd, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sd, hsd, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨q1, hq1, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sw, hsw, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨q2, hq2, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ovf, hovf, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨eW, heW, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ev, hev, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨o1, ho1, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨bad', hbad, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨Wa, hWa, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hbw := badWord_spec hsv hd hsd hq1 hsw hq2 hovf heW hev ho1 hbad
    have hW := (runScan_ok (op := .add) (fn := (· + ·)) (fun _ _ => rfl) (by decide) hruns hsu hz (kscanStream_ne (by decide) _ _ _) hr).2
    have hF := Lang.sums_fold hruns (fun q => (Enc.raw .i64 n v)[q]?.getD 0) (fun q => (Enc.raw .i64 n Ws)[q]?.getD 0)
      (fun q => (Enc.raw .i64 n bad')[q]?.getD 0) hW (fun t ht => (hbw t ht).2)
    refine ⟨.inl rfl, fun t ht => ⟨(hbw t ht).1, fun w => ?_⟩⟩
    have e := (colMap_raw (colArr_ok hWa)).2.2.2 t ht
    rw [colConst_raw hz, Array.getElem?_replicate, if_pos ht, Option.getD_some] at e
    simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at e
    rw [Arr.get_i64, ← e]
    exact hF t ht w
  case f32 =>
    simp only [Tab.sumTail, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    exact ⟨.inr (.inl rfl), sumTailF_fold (.inl rfl) hruns hsu hz h⟩
  case f64 =>
    simp only [Tab.sumTail, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    exact ⟨.inr (.inr rfl), sumTailF_fold (.inr rfl) hruns hsu hz h⟩
  all_goals
    simp only [Tab.sumTail, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; cases h

/-- **`sums x` denotes `sumsDen`** (`Rel/Lang/Den.lean`): `x` simple (one value per `(κ, ν)`, else the error), `sumTail`
holds each row's left fold over its `κ`'s rows ascending in `ν` (`sumTail_fold`), and the segmented `kscan .or` of the
bad words keeps a row exactly when no step of its key up to it was bad. -/
theorem sums_holds {K : Obj} {t u : QAtomicType} (hord : Lang.OrdAt t) {x T : Tab (.prod K (.atom t)) (.atom u)}
    (h : Tab.sumsOn x = .ok T) (hw : x.WF) : rep T = Lang.sumsDen (rep x) := by
  obtain ⟨f, hf⟩ := hord.ascOrd
  dsimp only [Tab.sumsOn] at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e1, he1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨m, g1, f1⟩, hk1, h⟩ := h
  split at h
  · iterate 4 (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h)
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, h, -⟩ := h; cases h
  rename_i hmn; simp only [ne_eq, Decidable.not_not] at hmn
  rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e2, he2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨gk, g2, fk⟩, hk2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨seg, hseg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Wa, bad⟩, hst, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨R, R2⟩, hr2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nb, hnb, h⟩ := h
  -- distinct keys: `kseen` over the whole key found `n` runs, so every row is the first of its run
  obtain ⟨cs1, hcs1⟩ := kseen_codes hk1
  obtain ⟨cs2, hcs2⟩ := kseen_codes hk2
  have hfs1 := firsts_spec (seenKey C.n e1) C.n.toNat
  have hall : firstsOf (seenKey C.n e1) C.n.toNat = List.range C.n.toNat :=
    List.filter_sublist.eq_of_length (by rw [List.length_range]; exact (kseen_ok hk1).1.symm.trans hmn)
  have hfirst : ∀ i j : Fin C.n.toNat, i.1 < j.1 → C.key.row i ≠ C.key.row j := fun i j h e =>
    ((hfs1.2.1 j).1 (by rw [hall]; exact List.mem_range.2 j.2)).2 i h (Vals.codes_of_row C.key (canon_wf hC hw).1 he1 hcs1 i j e)
  have hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j := fun i j e => by
    rcases Nat.lt_trichotomy i.1 j.1 with h' | h' | h'
    · exact absurd e (hfirst i j h')
    · exact Fin.ext h'
    · exact absurd e.symm (hfirst j i h')
  have hG : ∀ i j : Fin C.n.toNat, Verify.groupOf (seenKey C.n e2) C.n.toNat i =
      Verify.groupOf (seenKey C.n e2) C.n.toNat j ↔ (C.key.row i).1 = (C.key.row j).1 := fun i j =>
    ((firsts_spec (seenKey C.n e2) C.n.toNat).2.2.1 i i.2 j j.2).trans
      ⟨Vals.row_of_codes C.key.1 (canon_wf hC hw).1.1 he2 hcs2 i j, Vals.codes_of_row C.key.1 (canon_wf hC hw).1.1 he2 hcs2 i j⟩
  -- the left fold per key up to each row, and the prefix `|` of the bad words
  have hsu := seenSeg_ok hk2 hseg
  obtain ⟨hu, hF⟩ := sumTail_fold (kseen_runs hk2) hsu hst
  have hB := (runScan_ok (op := .or) (fn := (· ||| ·)) (fun _ _ => rfl) (by decide) (kseen_runs hk2) hsu hz (kscanStream_ne (by decide) _ _ _) hr2).2
  have hBR : ∀ t < C.n.toNat, ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ∨ (Enc.raw .i64 C.n R)[t]?.getD 0 = 1) ∧
      ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ↔ ∀ q ∈ (List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t),
        (Enc.raw .i64 C.n bad)[q]?.getD 0 = 0) := fun t ht => by
    rw [hB t ht]
    have := foldl_or01 (((List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t)).map
        ((Enc.raw .i64 C.n bad)[·]?.getD 0)) 0 (Or.inl rfl) (fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      simp only [List.mem_filter, List.mem_range] at hq
      exact (hF q (by omega)).1)
    exact ⟨this.1, this.2.trans ((and_iff_right rfl).trans List.forall_mem_map)⟩
  have hNB : ∀ t < C.n.toNat, (Enc.raw .i64 C.n nb)[t]?.getD 0 = (Enc.raw .i64 C.n R)[t]?.getD 0 ^^^ 1 :=
    fun t ht => by
      have := (colMap_raw hnb).2.2.2 t ht
      simp only [Op.eval, Except.ok.injEq] at this; exact this.symm
  have hx : rep x = rep C := funext fun a => funext fun c => propext (canon_holds hC hw a c).symm
  rw [hx]
  funext a c
  apply propext
  rw [sumsDen_rows hord C (Verify.groupOf (seenKey C.n e2) C.n.toNat) hD hG (canon_pos_lt hf hC hw hD) a c]
  show T.Holds a c ↔ _
  rw [keep_holds h (fun i hi => by
    rw [hNB i hi]; rcases (hBR i hi).1 with e | e <;> rw [e] <;> decide) a c]
  apply exists_congr; intro t
  have hmap : ∀ d, (((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
      Verify.groupOf (seenKey C.n e2) C.n.toNat t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else d) =
      ((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
        Verify.groupOf (seenKey C.n e2) C.n.toNat t).map
        fun q => QAtomicType.ofBits u ((Enc.raw u C.n (Arr.enc (t := u) C.val))[q]?.getD 0) := by
    intro d; apply List.map_congr_left; intro q hq
    simp only [List.mem_filter, List.mem_range] at hq
    rw [dif_pos (by omega), Vals.row_atom, Arr.get_word _ (by rcases hu with rfl | rfl | rfl <;> decide)]
  rw [hmap, (hF t t.2).2 c, hNB t t.2]
  have hb := hBR t t.2
  have hx1 : (Enc.raw .i64 C.n R)[t.1]?.getD 0 ^^^ 1 ≠ 0 ↔ (Enc.raw .i64 C.n R)[t.1]?.getD 0 = 0 := by
    rcases hb.1 with e | e <;> rw [e] <;> decide
  rw [hx1, hb.2]
  show _ ∧ _ ∧ ValsB.row (o := false) (A := .atom u) Wa t = c ↔ _
  rw [Vals.row_atom]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3.symm⟩

/-- **`sums x` at any position object denotes `sumsAt`**: it runs only at an integer-stored atom (`intOrd`), where
`ordAt_int` gives `sums_holds` its order. -/
theorem sums_den {K P V : Obj} {x T : Tab (.prod K P) V} (h : Tab.sums x = .ok T) (hx : x.WF) :
    rep T = Lang.sumsAt K P V (rep x) := by
  cases P with
  | atom t =>
    cases V with
    | atom u =>
      cases u <;> simp only [Tab.sums] at h <;> try cases h
      all_goals
        split at h
        · exact sums_holds (Lang.ordAt_int ‹_›) h hx
        · cases h
    | _ => cases h
  | _ => cases h

/-- **`sums` keeps `Tab.WF`**: its table is `keep` of `canon x`'s key beside atom sums (`canon_wf`, `keep_wf`). -/
theorem sums_wf {K P V : Obj} {x T : Tab (.prod K P) V} (h : Tab.sums x = .ok T) (hx : x.WF) : T.WF := by
  have on : ∀ {t u : QAtomicType} {x T : Tab (.prod K (.atom t)) (.atom u)}, Tab.sumsOn x = .ok T → x.WF → T.WF := by
    intro t u x T h hx
    dsimp only [Tab.sumsOn] at h
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨_, _, _⟩, -, h⟩ := h
    split at h
    · iterate 4 (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h)
      rw [Except.bind_eq_ok'] at h; obtain ⟨_, h, -⟩ := h; cases h
    iterate 8 (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h)
    exact Tab.keep_wf h ⟨(Tab.canon_wf hC hx).1, trivial⟩
  cases P with
  | atom t =>
    cases V with
    | atom u =>
      cases u <;> simp only [Tab.sums] at h <;> try cases h
      all_goals
        split at h
        · exact on h hx
        · cases h
    | _ => cases h
  | _ => cases h


/-- **`sum X` denotes `sumAt`, the left fold `⦇[0, plus]⦈` of each cell** (`rowDens`' `sum`) at an `i64` or `f64`
atom: EXPAND lays each cell `g` out as the run `[off g, off g + w g)` of rows, whose first row (offset `0`) opens a
segment, so `sumTail_fold` gives the run's last row the fold of the whole cell; a cell is kept with that row's word
(`kscatter .last`, `0` for an empty cell) exactly when none of its rows' bad words is set (`kscatter .or`). -/
theorem sum_holds {V : Obj} {n : USize} {X : Vals (.arr V) n} {T : Tab (.arr V) V} (h : Tab.sum X = .ok T)
    (hX : Vals.WF X)
    (xs : List V.El) (c : V.El) : T.Holds xs c ↔ (∃ i, X.row i = xs) ∧ Lang.sumAt V xs c := by
  cases V
  all_goals first | (simp only [Tab.sum, throw, throwThe, MonadExceptOf.throw] at h; cases h) | skip
  rename_i u
  obtain ⟨m, lo, up, f⟩ := X
  simp only [Tab.sum, Tab.sumOn] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T', G, i⟩, hTGu, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g1, hg1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a1, ha1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v, hv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨seg, hseg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨W, bad⟩, hst, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨badC, hbadC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨L, hL, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨tot, htot, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kp, hkp, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  dsimp only at hw hTGu hg1 ha1 hv hseg hst hbadC hL htot hkp hK
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  -- the cells `[SN g, EN g)`, their widths `EN g - SN g` at `w`, laid out by EXPAND at the offsets `off g`
  obtain ⟨SN, EN, hw1, hb1, hrow⟩ := cellSpan_spec (fun i => hX.2.2.1 i trivial) hm63 f
  have hwv : ∀ g < n.toNat, (Enc.raw .i64 n w)[g]?.getD 0 = (EN g - SN g).toUInt64 := fun g hg => by
    have es := (colMap_raw hw).2.2.2 g hg
    rw [(hw1 g hg).2, (hw1 g hg).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← toUInt64_sub (hb1 g).1]
  have hwm : ∀ g, EN g - SN g ≤ m.toNat := fun g => by rcases (hb1 g).2.2 with h | h <;> omega
  have hsum : ∀ k, ((List.range k).map fun g => EN g - SN g).sum ≤ k * m.toNat := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [List.range_succ, List.map_append]; simp [Nat.succ_mul]; have := hwm k; omega
  have hnm := hsum n.toNat
  have hnm' : n.toNat * m.toNat < 2 ^ 63 := by omega
  obtain ⟨hT, hrun⟩ := expand_spec hTGu (fun g => EN g - SN g) hwv (by omega) hn63
  have hfilt : ∀ g < n.toNat, (List.range T'.toNat).filter (fun k => ((Enc.raw .i64 T' G)[k]?.getD 0).toNat = g) =
      List.range' ((List.range g).map fun g => EN g - SN g).sum (EN g - SN g) :=
    expand_group_run hTGu (fun g => EN g - SN g) hwv (by omega) hn63
  obtain ⟨off, hoff⟩ : ∃ F : Nat → Nat, ∀ g, F g = ((List.range g).map fun g => EN g - SN g).sum := ⟨_, fun _ => rfl⟩
  simp only [← hoff] at hT hrun hfilt
  have hle : ∀ g < n.toNat, off g + (EN g - SN g) ≤ T'.toNat := fun g hg => by
    have := sum_range_mono (fun g => EN g - SN g) (show g + 1 ≤ n.toNat by omega)
    rw [List.range_succ, List.map_append] at this; simp at this
    rw [hT, hoff, hoff]; omega
  have hGt := kgather_word hg1 lo.plain
  have hA := (colMap_raw ha1).2.2.2
  have hVt := kgather_word hv (Arr.plain (t := u) f)
  have hG2 : ∀ g < n.toNat, ∀ k < EN g - SN g, (Enc.raw .i64 T' G)[off g + k]?.getD 0 = g.toUInt64 ∧
      (Enc.raw .i64 T' i)[off g + k]?.getD 0 = k.toUInt64 := fun g hg k hk => by
    have := hrun g hg (off g + k) (by omega) (by omega); simpa using this
  -- every row `t` lies in the run of the cell its `G` word names
  have hpos : ∀ t < T'.toNat, ((Enc.raw .i64 T' G)[t]?.getD 0).toNat < n.toNat ∧
      off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat ≤ t ∧
      t < off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat + (EN ((Enc.raw .i64 T' G)[t]?.getD 0).toNat -
        SN ((Enc.raw .i64 T' G)[t]?.getD 0).toNat) := fun t ht => by
    have hg := (hGt t ht).1
    have hm : t ∈ (List.range T'.toNat).filter (fun k => ((Enc.raw .i64 T' G)[k]?.getD 0).toNat =
        ((Enc.raw .i64 T' G)[t]?.getD 0).toNat) := by simp [ht]
    rw [hfilt _ hg, List.mem_range'_1] at hm
    exact ⟨hg, hm⟩
  have hin : ∀ g < n.toNat, ∀ t, off g ≤ t → t < off g + (EN g - SN g) → ((Enc.raw .i64 T' G)[t]?.getD 0).toNat = g :=
    fun g hg t h1 h2 => by
      have := (hG2 g hg (t - off g) (by omega)).1
      rw [show off g + (t - off g) = t by omega] at this
      rw [this, toNat_toUInt64 (by omega)]
  have hruns : ∀ a b c, a ≤ b → b ≤ c → c < T'.toNat → (Enc.raw .i64 T' G)[a]?.getD 0 = (Enc.raw .i64 T' G)[c]?.getD 0 →
      (Enc.raw .i64 T' G)[b]?.getD 0 = (Enc.raw .i64 T' G)[a]?.getD 0 := fun a b c hab hbc hc e => by
    obtain ⟨hg, ha1, -⟩ := hpos a (by omega)
    obtain ⟨-, -, hc2⟩ := hpos c hc
    rw [← e] at hc2
    exact UInt64.toNat_inj.1 (hin _ hg b (by omega) (by omega))
  -- the segment marks: `1` exactly where the offset in the cell is `0`, the cell's first row
  have hsf : ∃ md pk, seg = .foR md pk := by
    unfold colMap at hseg; simp only [bind, Except.bind] at hseg; split at hseg; · cases hseg
    rename_i q hq; simp only [pure, Except.pure, Except.ok.injEq] at hseg; subst hseg; exact kscan_foR hq
  have hT63 : T'.toNat < 2 ^ 63 := by rw [hT, hoff]; omega
  have hsu : ∀ t < T'.toNat, ((Enc.raw .u1 T' seg)[t]?.getD 0 = 0 ↔
      t ∉ firstsOf (fun t => (Enc.raw .i64 T' G)[t]?.getD 0) T'.toNat) := fun t ht => by
    obtain ⟨hg, h1, h2⟩ := hpos t ht
    have hl := eval_eq_word ((colMap_post hseg).2 t ht)
    simp only [eq_comm (a := (0 : UInt64))] at hl
    have hit := (hG2 _ hg (t - off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat) (by omega)).2
    rw [show off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat + (t - off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat) = t by omega] at hit
    rw [hit] at hl
    have hlsz := (colMap_post hseg).1
    obtain ⟨md, pk, hfo⟩ := hsf
    rw [hfo] at hl hlsz ⊢
    rw [raw_u1_foR, Array.getElem?_map, Array.getElem?_eq_getElem (by omega)]
    rw [Array.getElem?_eq_getElem (by omega), Option.getD_some] at hl
    simp only [Option.map_some, Option.getD_some, hl]
    rw [(firsts_spec _ _).2.1 t]
    have e0 : (t - off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat).toUInt64 = 0 ↔ t = off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat :=
      ⟨fun e => by have := congrArg UInt64.toNat e; rw [toNat_toUInt64 (by omega)] at this; simp at this; omega,
       fun e => by rw [← e, Nat.sub_self]; rfl⟩
    by_cases h0 : t = off ((Enc.raw .i64 T' G)[t]?.getD 0).toNat
    · rw [if_pos (e0.2 h0)]
      refine ⟨fun e => absurd e (by decide), fun hn => absurd ⟨ht, fun q hq e => ?_⟩ hn⟩
      obtain ⟨-, hq1, -⟩ := hpos q (by omega)
      rw [e] at hq1; omega
    · rw [if_neg (fun e => h0 (e0.1 e))]
      refine ⟨fun _ ⟨_, hne⟩ => hne (t - 1) (by omega) (UInt64.toNat_inj.1 ?_), fun _ => by decide⟩
      rw [hin _ hg (t - 1) (by omega) (by omega)]
  obtain ⟨hu, hF⟩ := sumTail_fold hruns hsu hst
  -- the gathered values are a `foR` column, read at `u` as its whole words cut to `u`'s width
  have hvr : ∀ j, QAtomicType.ofBits u ((Enc.raw u T' v)[j]?.getD 0) =
      QAtomicType.ofBits u ((Enc.raw .i64 T' v)[j]?.getD 0) := fun j => by
    obtain ⟨w0, hw0⟩ : ∃ w, u.width = some w := by rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    rw [raw_foR_cut hw0 (by rcases hu with rfl | rfl | rfl <;> decide) T'
      (by rw [kgather_plain hv (Arr.plain (t := u) f)]; rfl), Array.getElem?_map]
    cases (Enc.raw .i64 T' v)[j]? with
    | none => rfl
    | some x => exact QAtomicType.ofBits_cut hu hw0 x
  have hxl : ∀ g (hg : g < n.toNat), (ValsB.row (A := .arr (.atom u)) ⟨m, lo, up, f⟩ ⟨g, hg⟩).length = EN g - SN g :=
    fun g hg => by rw [hrow]; simp
  have hvx : ∀ g (hg : g < n.toNat) k (hk : k < EN g - SN g), QAtomicType.ofBits u ((Enc.raw u T' v)[off g + k]?.getD 0) =
      (ValsB.row (A := .arr (.atom u)) ⟨m, lo, up, f⟩ ⟨g, hg⟩)[k]'(by rw [hxl]; exact hk) := by
    intro g hg k hk
    rw [hvr]
    have ht : off g + k < T'.toNat := by have := hle g hg; omega
    obtain ⟨hGk, hUk⟩ := hG2 g hg k hk
    obtain ⟨-, hg1t⟩ := hGt _ ht
    have ha := hA _ ht; simp only [Op.eval, Except.ok.injEq] at ha
    obtain ⟨-, hvt⟩ := hVt _ ht
    rw [hGk, toNat_toUInt64 (by omega), (hw1 g hg).1] at hg1t
    rw [hg1t, hUk] at ha
    have hkm : SN g + k < m.toNat := by rcases (hb1 g).2.2 with h | h <;> omega
    have han : ((SN g).toUInt64 + k.toUInt64).toNat = SN g + k := by
      rw [UInt64.toNat_add, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]; omega
    rw [hvt, ← ha, han]
    simp only [hrow ⟨g, hg⟩, List.getElem_map, List.getElem_range', Nat.one_mul, hkm, dif_pos, Vals.row_atom,
      Arr.get_ofBits hu]
  -- per cell: its bad words `|`-ed, its run's last scanned word, the total
  obtain ⟨hGs, -, hbw⟩ := kscatter_words hbadC (sumTail_plain hst)
  obtain ⟨-, hbadCf⟩ := scatterWords_fold (f := (· ||| ·)) (fun _ _ => rfl) hbw
  obtain ⟨-, -, hLw⟩ := kscatter_words hL (Arr.plain W)
  obtain ⟨-, hLf⟩ := scatterWords_fold (f := fun _ y => y) (fun _ _ => rfl) hLw
  rw [hGs] at hbadCf hLf
  have hbadCg : ∀ g (hg : g < n.toNat), ((Enc.raw .i64 n badC)[g]?.getD 0 = 0 ∨ (Enc.raw .i64 n badC)[g]?.getD 0 = 1) ∧
      ((Enc.raw .i64 n badC)[g]?.getD 0 = 0 ↔ ∀ q ∈ List.range' (off g) (EN g - SN g), (Enc.raw .i64 T' bad)[q]?.getD 0 = 0) := by
    intro g hg
    rw [hbadCf g hg, hfilt g hg]
    obtain ⟨h1, h2⟩ := foldl_or01 ((List.range' (off g) (EN g - SN g)).map ((Enc.raw .i64 T' bad)[·]?.getD 0)) 0
      (Or.inl rfl) (fun y hy => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy; rw [List.mem_range'_1] at ht
        exact (hF t (by have := hle g hg; omega)).1)
    exact ⟨h1, h2.trans ((and_iff_right rfl).trans List.forall_mem_map)⟩
  have htot : ∀ g (hg : g < n.toNat), tot.get ⟨g, hg⟩ = QAtomicType.ofBits u
      (((List.range' (off g) (EN g - SN g)).map ((Enc.raw .i64 T' W.enc)[·]?.getD 0)).foldl (fun _ y => y) 0) := by
    intro g hg
    obtain ⟨v0, hv0, hwi⟩ := (colMap_get (colArr_ok htot)).2 g hg
    simp only [Op.eval, Except.ok.injEq, UInt64.or_self] at hv0
    rw [Arr.get_ofBits hu, hwi, if_neg (by rcases hu with rfl | rfl | rfl <;> decide), Option.getD_some, ← hv0, hLf g hg,
      hfilt g hg]
  -- the cell's elements are its run's values, and its run is the last row's prefix
  have hcell : ∀ g (hg : g < n.toNat) c, Lang.sumAt (.atom u) (ValsB.row (A := .arr (.atom u)) ⟨m, lo, up, f⟩ ⟨g, hg⟩) c ↔
      (Enc.raw .i64 n badC)[g]?.getD 0 = 0 ∧ c = tot.get ⟨g, hg⟩ := by
    intro g hg c
    rw [(hbadCg g hg).2, htot g hg]
    rcases Nat.eq_zero_or_pos (EN g - SN g) with h0 | h0
    · rw [List.eq_nil_of_length_eq_zero ((hxl g hg).trans h0), h0]
      simp only [Lang.sumAt]; simp; exact Lang.sumDen_nil hu c
    · have ht : off g + (EN g - SN g) - 1 < T'.toNat := by have := hle g hg; omega
      have hrows : ((List.range (off g + (EN g - SN g) - 1 + 1)).filter fun q =>
          Verify.groupOf (fun t => (Enc.raw .i64 T' G)[t]?.getD 0) T'.toNat q =
            Verify.groupOf (fun t => (Enc.raw .i64 T' G)[t]?.getD 0) T'.toNat (off g + (EN g - SN g) - 1)) =
          List.range' (off g) (EN g - SN g) := by
        rw [show off g + (EN g - SN g) - 1 + 1 = 0 + off g + (EN g - SN g) by omega, List.range_eq_range',
          ← List.range'_append_1, List.filter_append]
        have hlg := hin g hg (off g + (EN g - SN g) - 1) (by omega) (by omega)
        rw [List.filter_eq_nil_iff.2, List.filter_eq_self.2, List.nil_append]
        · simp
        · intro q hq
          rw [List.mem_range'_1] at hq
          rw [decide_eq_true_eq, (firsts_spec _ _).2.2.1 q (by omega) _ ht]
          exact UInt64.toNat_inj.1 (by rw [hlg, hin g hg q (by omega) (by omega)])
        · intro q hq e
          rw [List.mem_range'_1] at hq
          rw [decide_eq_true_eq, (firsts_spec _ _).2.2.1 q (by omega) _ ht] at e
          obtain ⟨-, h1, -⟩ := hpos q (by omega)
          rw [e, hlg] at h1; omega
      have hmap : (List.range' (off g) (EN g - SN g)).map (fun q => QAtomicType.ofBits u ((Enc.raw u T' v)[q]?.getD 0)) =
          ValsB.row (A := .arr (.atom u)) ⟨m, lo, up, f⟩ ⟨g, hg⟩ := by
        apply List.ext_getElem (by simp [hxl])
        intro k h1 h2
        simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
        exact hvx g hg k (by simpa using h1)
      have hF' := (hF _ ht).2 c
      rw [hrows, hmap] at hF'
      refine hF'.trans (and_congr Iff.rfl ?_)
      have hL1 : ((List.range' (off g) (EN g - SN g)).map ((Enc.raw .i64 T' W.enc)[·]?.getD 0)).foldl
          (fun _ y => y) 0 = (Enc.raw .i64 T' W.enc)[off g + (EN g - SN g) - 1]?.getD 0 := by
        obtain ⟨k, hk⟩ : ∃ k, EN g - SN g = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
        rw [hk, ← List.range'_append_1, List.map_append, List.foldl_append,
          show off g + (k + 1) - 1 = off g + k by omega]
        rfl
      rw [Arr.get_ofBits hu, hL1]
  have hkpg : ∀ g < n.toNat, (Enc.raw .i64 n kp)[g]?.getD 0 = (Enc.raw .i64 n badC)[g]?.getD 0 ^^^ 1 := fun g hg => by
    have := (colMap_raw hkp).2.2.2 g hg; simp only [Op.eval, Except.ok.injEq] at this; exact this.symm
  have hkp2 : ∀ g < n.toNat, (Enc.raw .i64 n kp)[g]?.getD 0 < 2 := fun g hg => by
    rw [hkpg g hg]; rcases (hbadCg g hg).1 with h | h <;> rw [h] <;> decide
  have hgood : ∀ g < n.toNat, (Enc.raw .i64 n kp)[g]?.getD 0 ≠ 0 ↔ (Enc.raw .i64 n badC)[g]?.getD 0 = 0 := fun g hg => by
    rw [hkpg g hg]; rcases (hbadCg g hg).1 with h | h <;> rw [h] <;> decide
  rw [canon_holds h (keep_wf hK ⟨hX, trivial⟩), keep_holds hK hkp2]
  constructor
  · rintro ⟨⟨g, hg⟩, hk, rfl, rfl⟩
    exact ⟨⟨_, rfl⟩, (hcell g hg _).2 ⟨(hgood g hg).1 hk, by rw [Vals.row_atom]⟩⟩
  · rintro ⟨⟨⟨g, hg⟩, rfl⟩, hs⟩
    obtain ⟨h0, rfl⟩ := (hcell g hg c).1 hs
    exact ⟨⟨g, hg⟩, (hgood g hg).2 h0, rfl, by rw [Vals.row_atom]⟩
end Tab

end Rel
