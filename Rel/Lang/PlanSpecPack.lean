module

public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecSelect
public import Rel.Lang.PlanSpecCross

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `packB` builds: one array column over atom columns

`cellsBoundB` is the size-register test of `ValsB.pack`'s `2^63` check, built from `USize` kernel calls and `ite`s,
then `guard`. The widths are `hi - lo` (at `o`, both bounds `max`ed with `0` first), the cut bounds `cellsLayB`, the
`wide` test `m / k < T`. As in `PlanSpecPrefix`, the kernel answers are premises. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel

/-! ### `Grows`, `Typed` -/

theorem Grows.ite1 {c : Nat} {t e : Bld Nat} (ht : Grows t) (he : Grows e) : Grows (Plan.ite1 c t e) := by
  unfold Plan.ite1
  exact (Grows.ite (ht.bind fun _ => Grows.pure _) (he.bind fun _ => Grows.pure _)).bind fun _ => Grows.nth _ _ _

theorem Grows.andB {c : Nat} {d : Bld Nat} (hd : Grows d) : Grows (Plan.andB c d) :=
  Grows.ite1 hd (Grows.lit _)

theorem Typed.ite1 {m c : Nat} {t e : Bld Nat} (hc : m ≤ c) (ht : Typed m (fun r => m ≤ r) t)
    (he : Typed m (fun r => m ≤ r) e) : Typed m (fun r => m ≤ r) (Plan.ite1 c t e) := by
  unfold Plan.ite1
  refine (Typed.ite hc (ht.bind fun x hx => Typed.pure fun a ha => ?_)
    (he.bind fun x hx => Typed.pure fun a ha => ?_)).bind fun r hr => Typed.nth hr 0 _
  all_goals simp at ha; omega

theorem Typed.andB {m c : Nat} {d : Bld Nat} (hc : m ≤ c) (hd : Typed m (fun r => m ≤ r) d) :
    Typed m (fun r => m ≤ r) (Plan.andB c d) :=
  Typed.ite1 hc hd (Typed.lit _)


theorem Grows.cellsBoundB (what : String) (n m : Nat) : Grows (Plan.cellsBoundB what n m) := by
  unfold Plan.cellsBoundB
  repeat' first
    | with_reducible exact Grows.pure _ | with_reducible exact Grows.lit _ | with_reducible exact Grows.call1 _ _
    | with_reducible exact Grows.guard _ _ _ | (with_reducible refine Grows.bind ?_ (fun _ => ?_))
    | refine Grows.andB ?_ | refine Grows.ite1 ?_ ?_ | dsimp only

theorem Typed.cellsBoundB {lv : Nat} {what : String} {n m : Nat} (hn : lv ≤ n) (hm : lv ≤ m) :
    Typed lv (fun _ => True) (Plan.cellsBoundB what n m) := by
  unfold Plan.cellsBoundB
  repeat' first
    | exact Typed.lit _ | refine Typed.call1 ?_ | refine Typed.pure ?_ | (with_reducible apply Typed.bind (hf := fun _ _ => ?_))
    | refine Typed.andB ?_ ?_ | refine Typed.ite1 ?_ ?_ ?_ | dsimp only

  all_goals first
    | assumption
    | (intro a ha; simp at ha; omega)
    | exact Typed.guard (by assumption) (by intro a ha; simp at ha; omega)

/-- **`ite1` builds the branch the bit `bt` picks**: the branches' one register each, `nth` of the `if`'s result. -/
theorem ite1_builds {fg : Array Fun × Array Fun} {rs : Array Val} {c : Nat} {bt : Bool} {t e : Bld Nat}
    {vt ve : Val} (hc : rs[c]? = some (.bit bt)) (ht : Builds abiOf fg fg (do let r ← t; Pure.pure #[r]) rs #[vt])
    (he : Builds abiOf fg fg (do let r ← e; Pure.pure #[r]) rs #[ve]) :
    Builds abiOf fg fg (do let r ← ite1 c t e; Pure.pure #[r]) rs #[if bt then vt else ve] := by
  unfold ite1
  simp only [bind_assoc]
  refine Builds.bindG (Builds.ite hc ht he rfl) fun a R h m => ?_
  cases bt <;> simp only [Bool.false_eq_true, if_false, if_true] at h ⊢ <;>
  · obtain ⟨p, hp, hpR⟩ := holds_at h (i := 0) rfl
    rw [nth_of (by simpa using hp), pure_bind]
    exact Builds.pure fun who => by simp [reg, hpR]; rfl

/-- **`andB` of a set bit builds its second operand's register.** -/
theorem andB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {c : Nat} {d : Bld Nat} {vd : Val}
    (hc : rs[c]? = some (.bit true)) (hd : Builds abiOf fg fg (do let r ← d; Pure.pure #[r]) rs #[vd]) :
    Builds abiOf fg fg (do let r ← andB c d; Pure.pure #[r]) rs #[vd] :=
  ite1_builds hc hd (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)

theorem out_decLt {a b : USize} (h : a < b) : Out.out (a.decLt b) = .ok #[Val.bit true] := by
  rw [Subsingleton.elim (a.decLt b) (isTrue h)]
  rfl

theorem out_decLt_not {a b : USize} (h : ¬ a < b) : Out.out (a.decLt b) = .ok #[Val.bit false] := by
  rw [Subsingleton.elim (a.decLt b) (isFalse h)]
  rfl

/-- **`cellsBoundB` passes where `ValsB.pack`'s check does**: the registers hold the counts `nv`, `mv`, and the three
    `USize` tests it builds hold (`nv < 2^63`, `mv < 2^63`, not `2^63 / (mv + 1) < nv + 1`, each as the kernel
    `USize.decLt`, `div`, `add` read them); `k` then runs on the registers it pushed. -/
theorem cellsBoundB_builds {fg fg' : Array Fun × Array Fun} {rs : Array Val} {n m : Nat} {nv mv : USize} {what : String}
    {k : Bld (Array Nat)} {out : Array Val} (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv))
    (h1 : nv < 2 ^ 63) (h2 : mv < 2 ^ 63) (h3 : ¬ 2 ^ 63 / (mv + 1) < nv + 1)
    (hk : ∀ R, Extends rs R → Builds abiOf fg fg' k R out) :
    Builds abiOf fg fg' (cellsBoundB what n m >>= fun _ => k) rs out := by
  unfold cellsBoundB
  simp only [bind_assoc]
  refine Builds.litG fun c R1 hc1 m1 => ?_
  up m1 [hn hm]
  refine Builds.litG fun one R2 ho2 m2 => ?_
  up m2 [hn hm hc1]
  refine Builds.call1G (vs := #[.size nv, .size (2 ^ 63)]) (v := .bit true) (by abiK) (by rop) ?_ ?_ rfl
    fun a R3 ha3 m3 => ?_
  · rw [List.mapM_toArray]
    simp [reg, hn, hc1]
    rfl
  · simp [arg]
    exact out_decLt h1
  up m3 [hn hm hc1 ho2]
  refine Builds.bind1G (o := Val.bit true) (andB_builds ha3 ?_) fun ok R4 hok4 m4 => ?_
  · simp only [bind_assoc]
    refine Builds.call1G (vs := #[.size mv, .size (2 ^ 63)]) (v := .bit true) (by abiK) (by rop) ?_ ?_ rfl
      fun b R5 hb5 m5 => ?_
    · rw [List.mapM_toArray]
      simp [reg, hm, hc1]
      rfl
    · simp [arg]
      exact out_decLt h2
    up m5 [hn hm hc1 ho2]
    refine andB_builds hb5 ?_
    simp only [bind_assoc]
    refine Builds.call1G (vs := #[.size mv, .size 1]) (v := .size (mv + 1)) (by abiK) (by rop) ?_ ?_ rfl
      fun t1 R6 ht6 m6 => ?_
    · rw [List.mapM_toArray]
      simp [reg, hm, ho2]
      rfl
    · simp [arg]
      rfl
    up m6 [hn hc1 ho2]
    refine Builds.call1G (vs := #[.size (2 ^ 63), .size (mv + 1)]) (v := .size (2 ^ 63 / (mv + 1))) (by abiK)
      (by rop) ?_ ?_ rfl fun q R7 hq7 m7 => ?_
    · rw [List.mapM_toArray]
      simp [reg, hc1, ht6]
      rfl
    · simp [arg]
      rfl
    up m7 [hn ho2]
    refine Builds.call1G (vs := #[.size nv, .size 1]) (v := .size (nv + 1)) (by abiK) (by rop) ?_ ?_ rfl
      fun t2 R8 ht8 m8 => ?_
    · rw [List.mapM_toArray]
      simp [reg, hn, ho2]
      rfl
    · simp [arg]
      rfl
    up m8 [hq7]
    refine Builds.call1G (vs := #[.size (2 ^ 63 / (mv + 1)), .size (nv + 1)]) (v := .bit false) (by abiK)
      (by rop) ?_ ?_ rfl fun t3 R9 ht9 m9 => ?_
    · rw [List.mapM_toArray]
      simp [reg, hq7, ht8]
      rfl
    · simp [arg]
      exact out_decLt_not h3
    exact ite1_builds (bt := false) (vt := .bit false) (ve := .bit true) ht9
      (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)
      (Builds.litG fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl)
  · exact Builds.guard hok4 (hk R4 fun h => m4 (m3 (m2 (m1 h))))

theorem out_decLt' (a b : USize) : Out.out (a.decLt b) = .ok #[Val.bit (decide (a < b))] := by
  by_cases h : a < b
  · simp only [h, decide_true]; exact out_decLt h
  · simp only [h, decide_false]; exact out_decLt_not h

theorem out_decEq (a b : USize) : Out.out (a.decEq b) = .ok #[Val.bit (decide (a = b))] := by
  by_cases h : a = b
  · rw [Subsingleton.elim (a.decEq b) (isTrue h)]; simp only [h, decide_true]; rfl
  · rw [Subsingleton.elim (a.decEq b) (isFalse h)]; simp only [h, decide_false]; rfl

/-- **The `wide` test of `packB`** (`packWideB`): `k ≠ 0` and `m / k < T` on the size registers `m`, `T`, as
    `USize.div` and `USize.decLt` read them; `k = 0` is the literal `false`. -/
theorem packWideB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {m T k : Nat} {mv Tv : USize}
    (hm : rs[m]? = some (.size mv)) (hT : rs[T]? = some (.size Tv)) :
    Builds abiOf fg fg (do let r ← packWideB k m T; Pure.pure #[r]) rs
      #[Val.bit (decide (k ≠ 0 ∧ mv / k.toUSize < Tv))] := by
  unfold packWideB
  split
  next hk =>
    subst hk
    exact Builds.litG fun r R hr _ => Builds.pure fun who => by simp [reg, hr]; rfl
  rename_i hk
  rw [show decide (k ≠ 0 ∧ mv / k.toUSize < Tv) = decide (mv / k.toUSize < Tv) by simp [hk]]
  simp only [bind_assoc]
  refine Builds.litG fun c R1 hc1 m1 => ?_
  up m1 [hm hT]
  refine Builds.call1G (vs := #[.size mv, .size k.toUSize]) (v := .size (mv / k.toUSize)) (by abiK) (by rop) ?_ ?_ rfl
    fun q R2 hq2 m2 => ?_
  · rw [List.mapM_toArray]; simp [reg, hm, hc1]; rfl
  · simp [arg]; rfl
  up m2 [hT]
  refine Builds.call1G (vs := #[.size (mv / k.toUSize), .size Tv]) (v := Val.bit (decide (mv / k.toUSize < Tv)))
    (by abiK) (by rop) ?_ ?_ rfl fun b R3 hb3 m3 => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]; simp [reg, hT, hq2]; rfl
  · simp [arg]; exact out_decLt' _ _
  · simp [reg, hb3]; rfl

theorem Free.mapM_srcB (n : Nat) : ∀ es : List Nat, Free (es.mapM (Plan.srcB n))
  | [] => Free.pure _
  | e :: es => by
    rw [List.mapM_cons]
    exact Free.bind (Free.ctorB _ _ _) fun _ => Free.bind (Free.mapM_srcB n es) fun _ => Free.pure _

theorem Free.scanB (op : Kernel.Op) (t : QAtomicType) (n : Nat) (seg : Option Nat) (es : List Nat) :
    Free (Plan.scanB op t n seg es) := by
  unfold Plan.scanB
  cases seg <;> dsimp only <;>
    repeat (first | with_reducible apply Free.listB | apply Free.mapM_srcB | apply Free.bind | apply Free.ctorB | apply Free.lit | apply Free.callK | intro _)

theorem Free.cellsLayB (n w P : Nat) : Free (Plan.cellsLayB n w P) := by
  unfold Plan.cellsLayB
  exact Free.bind (Free.mapB _ _ _ _ _ _ _ _) fun _ => Free.bind (Free.scanB _ _ _ _ _) fun _ =>
    Free.bind (Free.nth _ _ _) fun _ => Free.pure _

/-- **`cellsLayB` builds `Vals.cells`' bounds**: `n` holding the count `nv`, `w` the widths `wc`, `P` their prefix sum
    `pc`; `lo = P - w` is the `kscan .sub` `oc`, `hi` the `kscan .first` of `P` (`r`). -/
theorem cellsLayB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n w P : Nat} {nv : USize} {wc pc oc : Enc}
    {f1 : Option UInt64} {r : Enc × Option UInt64} (hn : rs[n]? = some (.size nv)) (hw : rs[w]? = some (Reg.put wc))
    (hP : rs[P]? = some (Reg.put pc)) (ho : kscan .sub false .i64 .i64 nv none [(nv, pc), (nv, wc)] [] [] = .ok (oc, f1))
    (hh : kscan .first false .i64 .i64 nv none [(nv, pc)] [] [] = .ok r) :
    Builds abiOf fg fg (do let (a, b) ← cellsLayB n w P; Pure.pure #[a, b]) rs #[Reg.put oc, Reg.put r.1] := by
  unfold cellsLayB
  simp only [bind_assoc]
  refine Builds.bind1G (mapB_builds hn hP (enc_get_put _) hw (enc_get_put _) (by rop) (qtype_get_put _)
    (qtype_get_put _) (by rop) (by rop) ho) fun a R1 ha m1 => ?_
  refine Builds.bindG (scanB_builds (by rop) (by rw [m1 hn]; rfl) (seg := none) (sg := none) rfl (es := [P]) (xs := [pc])
    (by simp [m1 hP, enc_get_put]) hh) fun ps R2 hps m2 => ?_
  obtain ⟨p0, hp0, hpR⟩ := holds_at hps (i := 0) rfl
  rw [nth_of (by simpa using hp0)]
  simp only [pure_bind]
  exact Builds.pure fun who => by simp [reg, m2 ha, hpR]; rfl

theorem Free.packWidthsB (o : Bool) (n lo hi : Nat) : Free (Plan.packWidthsB o n lo hi) := by
  unfold Plan.packWidthsB
  split
  · exact Free.bind (Free.wordsB _ _) fun _ => Free.bind (Free.mapB _ _ _ _ _ _ _ _) fun _ =>
      Free.bind (Free.mapB _ _ _ _ _ _ _ _) fun _ => Free.bind (Free.mapB _ _ _ _ _ _ _ _) fun _ => Free.pure _
  · exact Free.bind (Free.mapB _ _ _ _ _ _ _ _) fun _ => Free.pure _

/-- **`packWidthsB` builds the starts `s` and widths `w = e - s`** (`hwb`): at `o` the bounds `max`ed with the zeros
    `z` (`sc`, `ec`), else `s`, `e` are `lo`, `hi` themselves (`hsc0`, `hec0`). -/
theorem packWidthsB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {o : Bool} {n lo hi : Nat} {nv : USize}
    {lc hcl z sc ec wc : Enc} {f4 : Option UInt64} (hn : rs[n]? = some (.size nv)) (hlo : rs[lo]? = some (Reg.put lc))
    (hhi : rs[hi]? = some (Reg.put hcl)) (hz : o = true → kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsm : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, lc), (nv, z)] [] [] = .ok (sc, f))
    (hem : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, hcl), (nv, z)] [] [] = .ok (ec, f))
    (hsc0 : o = false → sc = lc) (hec0 : o = false → ec = hcl)
    (hwb : kscan .sub false .i64 .i64 nv none [(nv, ec), (nv, sc)] [] [] = .ok (wc, f4)) :
    Builds abiOf fg fg (do let (a, b) ← packWidthsB o n lo hi; Pure.pure #[a, b]) rs #[Reg.put sc, Reg.put wc] := by
  unfold packWidthsB
  split
  next hot =>
    obtain ⟨_, hs1⟩ := hsm hot
    obtain ⟨_, he1⟩ := hem hot
    simp only [bind_assoc, pure_bind]
    refine Builds.bind1G (wordsB_builds hn (hz hot)) fun z' R1 hz1 m1 => ?_
    refine Builds.bind1G (mapB_builds (m1 hn) (m1 hlo) (enc_get_put _) hz1 (enc_get_put _) (by rop)
      (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hs1) fun s' R2 hs2 m2 => ?_
    refine Builds.bind1G (mapB_builds (m2 (m1 hn)) (m2 (m1 hhi)) (enc_get_put _) (m2 hz1) (enc_get_put _) (by rop)
      (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) he1) fun e' R3 he3 m3 => ?_
    refine Builds.bind1G (mapB_builds (m3 (m2 (m1 hn))) he3 (enc_get_put _) (m3 hs2) (enc_get_put _) (by rop)
      (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hwb) fun w' R4 hw4 m4 => ?_
    exact Builds.pure fun who => by simp [reg, m4 (m3 hs2), hw4]; rfl
  next hot =>
    obtain rfl := hsc0 (by simpa using hot)
    obtain rfl := hec0 (by simpa using hot)
    simp only [bind_assoc, pure_bind]
    refine Builds.bind1G (mapB_builds hn hhi (enc_get_put _) hlo (enc_get_put _) (by rop)
      (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hwb) fun w' R4 hw4 m4 => ?_
    exact Builds.pure fun who => by simp [reg, m4 hlo, hw4]; rfl

theorem exFun_trans {a b c : Array Fun} (h1 : ∃ d, b = a ++ d) (h2 : ∃ d, c = b ++ d) : ∃ d, c = a ++ d := by
  obtain ⟨d, rfl⟩ := h1
  obtain ⟨e, rfl⟩ := h2
  exact ⟨d ++ e, by simp [Array.append_assoc]⟩

/-- **`ite c t (ite d t e)` builds**, `t` (`keep`) twice and `e` (`cut`) once from every `fg0` that extends `fg`, then
    `k` on the registers the bits `bc`, `bd` pick: `packB`'s choice between keeping and cutting a payload. -/
theorem Builds.ite2E {fg : Array Fun × Array Fun} {c d : Nat} {bc bd : Bool} {t e : Bld (Array Nat)}
    {k : Array Nat → Bld (Array Nat)} {rs ot oe out : Array Val}
    (hc : rs[c]? = some (.bit bc)) (hd : rs[d]? = some (.bit bd)) (hs : ot.size = oe.size) (hfo : Ordered fg.1)
    (ht : ∀ fg0 : Array Fun × Array Fun, (∃ x, fg0.1 = fg.1 ++ x) → GExt fg.2 fg0.2 → Ordered fg0.1 →
      ∃ fg1, Builds abiOf fg0 fg1 t rs ot ∧ Ordered fg1.1)
    (he : ∀ fg0 : Array Fun × Array Fun, (∃ x, fg0.1 = fg.1 ++ x) → GExt fg.2 fg0.2 → Ordered fg0.1 →
      ∃ fg1, Builds abiOf fg0 fg1 e rs oe)
    (hk : ∀ (fg1 : Array Fun × Array Fun) (a : Array Nat) (R : Array Val), (∃ x, fg1.1 = fg.1 ++ x) →
      GExt fg.2 fg1.2 → a.toList.mapM (fun x => R[x]?) = some (if bc then ot else if bd then ot else oe).toList →
      Extends rs R → ∃ fg', Builds abiOf fg1 fg' (k a) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.ite c t (Plan.ite d t e) >>= k) rs out := by
  obtain ⟨f1, h1, o1⟩ := ht fg ⟨#[], by simp⟩ (GExt.refl _) hfo
  obtain ⟨f2, h2, o2⟩ := ht f1 h1.1 h1.2.1 o1
  obtain ⟨f3, h3⟩ := he f2 (exFun_trans h1.1 h2.1) (h1.2.1.trans h2.2.1) o2
  refine Builds.bindFG (Free.ite _ _ _) (Builds.ite hc h1 (Builds.ite hd h2 h3 hs) (by cases bd <;> simp [hs]))
    fun a R h hE => ?_
  exact hk f3 a R (exFun_trans (exFun_trans h1.1 h2.1) h3.1) ((h1.2.1.trans h2.2.1).trans h3.2.1) h hE


/-- **`packB`'s test of an empty payload**: `m = 0` on the size register `m`, as `USize.decEq` reads it. -/
theorem decEq0B_builds {fg : Array Fun × Array Fun} {rs : Array Val} {m : Nat} {mv : USize}
    (hm : rs[m]? = some (.size mv)) :
    Builds abiOf fg fg (do
      let r ← (do let c ← lit (.size 0); call1 (kernel% USize.decEq) #[m, c]); Pure.pure #[r]) rs
      #[Val.bit (decide (mv = 0))] := by
  simp only [bind_assoc]
  refine Builds.litG fun c R1 hc1 m1 => ?_
  up m1 [hm]
  refine Builds.call1G (vs := #[.size mv, .size 0]) (v := Val.bit (decide (mv = 0))) (by abiK) (by rop) ?_ ?_ rfl
    fun b R2 hb2 m2 => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]; simp [reg, hm, hc1]; rfl
  · simp [arg]; exact out_decEq _ _
  · simp [reg, hb2]; rfl

theorem Free.discard {α : Type} {b : Bld α} (hb : Free b) : Free (Functor.discard b) := by
  have e : Functor.discard b = (b >>= fun _ => Pure.pure PUnit.unit) := by simp [Functor.discard, Functor.mapConst, Functor.map]
  rw [e]; exact hb.bind fun _ => Free.pure _

macro "free''" : tactic => `(tactic| repeat (first
    | with_reducible apply Free.discard
    | with_reducible apply Free.ite
    | with_reducible apply Free.bind
    | with_reducible apply Free.pure
    | with_reducible apply Free.lit
    | with_reducible apply Free.nth
    | with_reducible apply Free.call1
    | with_reducible apply Free.emit
    | intro _))

theorem Free.cellsBoundB (what : String) (n m : Nat) : Free (Plan.cellsBoundB what n m) := by
  unfold Plan.cellsBoundB Plan.andB Plan.ite1 Plan.guard
  free''


/-- **The cut branch of `packB` builds**: the registers `n` (count `nv`), `m` (payload count `mv`), `lo`, `s`, `w`, `P` hold
    the head's values (`packLeafB_builds`), `expandB n w` the kernel answers `expandB_builds` names (`Tv` the cut payload's
    row count, `G0` the groups, `uc` the offsets), `gatherB` the source rows `gs = s[G]`, `mapB .add` the positions
    `ac = gs + u`, `gatherCols` (`ValsB.gather Tv ac x = .ok y`) the payload `f` cut to them, `cellsLayB` the new
    bounds `oc = P - w` and `hic0` the `kscan .first` of `P`. Where `o` holds the bounds are `min`ed with `big` (`bc`); else
    they are `oc`, `hic0`. The recursion on the cut payload is the premise `hrec`: its registers hold `Tv`, the new bounds
    `loc`, `hic`, and `y`'s values, and it builds `out`. -/
theorem packCutB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {o : Bool} {k n m lo hi s w P : Nat}
    {p : String} {f : Cols} {A : Obj} {ox : Bool} {nv mv Tv : USize} {x : ValsB ox A mv} {y : ValsB ox A Tv}
    {lc sc wc z0 oc z1 scx G0 g1 uc gs ac hic0 bc loc hic : Enc} {r0 r1 : Enc × Option UInt64}
    {of f2 f5 f6 : Option UInt64} {out : Array Val}
    (hA : ColsOf A f) (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv))
    (hlo : rs[lo]? = some (Reg.put lc)) (hs : rs[s]? = some (Reg.put sc)) (hw : rs[w]? = some (Reg.put wc))
    (hP : rs[P]? = some (Reg.put r0.1)) (hx : (Cols.regs f).mapM (fun i => rs[i]?) = some x.regVals)
    (hz0 : colConst nv 0 = .ok z0)
    (hk0 : kscan .add false .i64 .i64 nv (some z0) [(nv, z0), (nv, wc)] [] [] = .ok r0) (hr0 : nv ≠ 0 → r0.2.isSome)
    (hT : Tv = if nv = 0 then 0 else (r0.2.getD 0).toUSize + 0)
    (ho : kscan .sub false .i64 .i64 nv none [(nv, r0.1), (nv, wc)] [] [] = .ok (oc, of))
    (hsc : kscatter .max nv oc .pos (Tv + 1) 0 = .ok scx)
    (hz1 : colConst (Tv + 1) 0 = .ok z1)
    (hk1 : kscan .max false .i64 .i64 (Tv + 1) (some z1) [(Tv + 1, z1), (Tv + 1, scx)] [] [] = .ok r1)
    (hr1 : Tv + 1 ≠ 0 → r1.2.isSome) (hG : kgather Tv .pos (Tv + 1) r1.1 = .ok G0)
    (hg1 : kgather Tv G0 nv oc = .ok g1)
    (hu : kscan .sub false .i64 .i64 Tv none [(Tv, .pos), (Tv, g1)] [] [] = .ok (uc, f2))
    (hgs : kgather Tv G0 nv sc = .ok gs)
    (hac : kscan .add false .i64 .i64 Tv none [(Tv, gs), (Tv, uc)] [] [] = .ok (ac, f5))
    (hgy : ValsB.gather Tv ac x = .ok y)
    (hhi0 : kscan .first false .i64 .i64 nv none [(nv, r0.1)] [] [] = .ok (hic0, f6))
    (hbig : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, lc), (nv, lc)] [] [(.and, 0), (.or, 0x7fffffffffffffff)] =
      .ok (bc, f))
    (hloc : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, oc)] [] [] = .ok (loc, f))
    (hhic : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, hic0)] [] [] = .ok (hic, f))
    (hloc0 : o = false → loc = oc) (hhic0 : o = false → hic = hic0) (hfo : Ordered fg.1)
    (hrec : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (T' l2 h2 : Nat) (g' : Cols), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → R[T']? = some (.size Tv) → R[l2]? = some (Reg.put loc) →
      R[h2]? = some (Reg.put hic) → Cols.shape g' = Cols.shape f →
      (Cols.regs g').mapM (fun i => R[i]?) = some y.regVals →
      ∃ fg', Builds abiOf fg2 fg' (do
        let f' ← packB false k T' g'
        let L ← regsOf [.arr p T' l2 h2 f']
        Pure.pure L.toArray) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      let (T', G, u) ← expandB n w
      let g ← gatherCols T' (← mapB .add T' (← gatherB T' G n s) u) m f
      let (lo', hi') ← cellsLayB n w P
      let (lo'', hi'') ← if o then do
          let big ← mapB .max n lo lo .i64 .i64 [] [(.and, 0), (.or, 0x7fffffffffffffff)]
          pure (← mapB .min n big lo', ← mapB .min n big hi')
        else pure (lo', hi')
      if h : Col.sizes g ≤ Col.sizes f then pure (← regsOf [.arr p T' lo'' hi'' (← packB false k T' g)]).toArray
      else throw "pack: the gathered payload is larger than the payload") rs out := by
  refine expandB_builds hn hw hz0 hk0 hr0 hT ho hsc hz1 hk1 hr1 hG hg1 hu hfo ?_
  intro fg2 ys a b c he hf hfo2 hread
  obtain ⟨ha, hread⟩ := mapM_get_cons hread
  obtain ⟨hb, hread⟩ := mapM_get_cons hread
  obtain ⟨hc, -⟩ := mapM_get_cons hread
  have hE0 : Extends rs (rs ++ ys) := fun h => get_app h
  up hE0 [hn hm hlo hs hw hP]
  have hx0 := mapM_extends hE0 hx
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 ha hb hn hs hgs) fun gi R1 hgi hE1 => ?_
  up hE1 [ha hb hc hn hm hlo hs hw hP]
  replace hx0 := mapM_extends hE1 hx0
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds ha hgi (enc_get_put _) hc (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hac) fun ix R2 hix hE2 => ?_
  up hE2 [ha hb hc hn hm hlo hs hw hP]
  replace hx0 := mapM_extends hE2 hx0
  refine gatherCols_builds A (x := x) (y := y) hA hx0 ha hix hm hgy hfo2 ?_
  intro fg3 g' ys3 he3 hf3 hfo3 hsh hreg
  have hE3 : Extends R2 (R2 ++ ys3) := fun h => get_app h
  up hE3 [ha hn hm hlo hs hw hP]
  refine Builds.bind2F (Free.cellsLayB _ _ _) (cellsLayB_builds (r := (hic0, f6)) hn hw hP ho hhi0)
    fun l1 h1 R6 hl4 hh6 hE6 => ?_
  up hE6 [ha hn hm hlo hs hw hP]
  have hEx : Extends rs R6 := fun h => hE6 (hE3 (hE2 (hE1 (hE0 h))))
  obtain ⟨e1, he1⟩ := he
  obtain ⟨e3, he3⟩ := he3
  have hext : ∃ a, fg3.1 = fg.1 ++ a := ⟨e1 ++ e3, by rw [he3, he1, Array.append_assoc]⟩
  have hsz : Col.sizes g' ≤ Col.sizes f := by
    have := Col.sizes_shape g'
    rw [hsh, Col.sizes_shape] at this
    omega
  cases o
  · simp only [Bool.false_eq_true, if_false, pure_bind, dif_pos hsz]
    obtain rfl := hloc0 rfl
    obtain rfl := hhic0 rfl
    exact hrec fg3 R6 a l1 h1 g' hext (hf.trans hf3) hfo3 hEx ha hl4 hh6 hsh (mapM_extends hE6 hreg)
  · simp only [↓reduceIte, pure_bind, dif_pos hsz]
    obtain ⟨_, hb1⟩ := hbig rfl
    obtain ⟨_, hb2⟩ := hloc rfl
    obtain ⟨_, hb3⟩ := hhic rfl
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn hlo (enc_get_put _) hlo (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hb1) fun big R7 hbg hE7 => ?_
    up hE7 [ha hn hl4 hh6]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn hbg (enc_get_put _) hl4 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hb2) fun l2 R8 hl8 hE8 => ?_
    up hE8 [ha hn hbg hh6]
    refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn hbg (enc_get_put _) hh6 (enc_get_put _)
      (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hb3) fun h2 R9 hh9 hE9 => ?_
    up hE9 [ha hl8]
    exact hrec fg3 R9 a l2 h2 g' hext (hf.trans hf3) hfo3 (fun h => hE9 (hE8 (hE7 (hEx h)))) ha hl8 hh9 hsh
      (mapM_extends (fun h => hE9 (hE8 (hE7 (hE6 h)))) hreg)



theorem mapM_attach_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (l : List α)
    (F : {x // x ∈ l} → m α) (h : ∀ x, F x = Pure.pure x.1) : l.attach.mapM F = Pure.pure l := by
  have : F = fun x => Pure.pure x.1 := funext h
  subst this
  simp [List.mapM_pure]

/-- **`packB` leaves atom columns as they are**: no array to cut. -/
theorem packB_atoms (o : Bool) (k n : Nat) (cs : Cols) (h : ∀ c ∈ cs, ∃ q t e, c = Col.atom q t e) :
    packB o k n cs = Pure.pure cs := by
  unfold packB
  refine mapM_attach_pure _ _ ?_
  rintro ⟨c, hc⟩
  obtain ⟨q, t, e, rfl⟩ := h c hc
  rfl

/-- Columns of the same shape as atom columns are atom columns. -/
theorem atoms_of_shape : ∀ {f g : Cols}, Cols.shape g = Cols.shape f → (∀ c ∈ f, ∃ q t e, c = Col.atom q t e) →
    ∀ c ∈ g, ∃ q t e, c = Col.atom q t e
  | [], g, hs, _ => by cases g <;> simp [Cols.shape] at hs ⊢
  | d :: f, [], hs, _ => by simp [Cols.shape] at hs
  | d :: f, c :: g, hs, hat => by
    simp only [Cols.shape, List.cons.injEq] at hs
    obtain ⟨q, t, e, rfl⟩ := hat d (by simp)
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · cases c' <;> simp [Col.shape] at hs
      exact ⟨_, _, _, rfl⟩
    · exact atoms_of_shape hs.2 (fun c hc => hat c (by simp [hc])) c' hc'

theorem Free.packWideB (k m T : Nat) : Free (Plan.packWideB k m T) := by
  unfold Plan.packWideB; split <;> free''

theorem decEq0B_free (m : Nat) : Free (do
    let c ← lit (.size 0); call1 (kernel% USize.decEq) #[m, c]) := by free''




theorem omapM_length {R : Array Val} : ∀ {l : List Nat} {vs : List Val}, l.mapM (fun x => R[x]?) = some vs →
    l.length = vs.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    obtain ⟨v, vs, hx, hl, rfl⟩ := omapM_cons.mp h
    simp [omapM_length hl]

/-- **`packB` of one array column over atom columns builds**, branch by branch: the widths `w` (`hwb`, from the starts
    `s`: at `o` a null bound read as `0`, `max` with the zeros `z`, else `[lo, hi)` as is), `prefixB`, the bits
    `m = 0` (`decEq0B_builds`) and `m / k < T` (`wideB_builds`; `k = 0` the literal `false`), `Builds.ite2E` over
    `ite (m = 0) keep (ite wide keep cut)`. `keep` is the recursion `hrecK` on the registers it was given; `cut` is
    `packCutB_builds`, whose recursion on the cut payload is `hrecC`. Then `withRegs` hands the one column `c` back
    to `kk`, which reads, per branch, `Kl` (`m`, `lo`, `hi` and `xk`'s registers) or `Cl` (the count `Tv`, the
    new bounds `loc`, `hic`, and `yk`'s registers). The link to `ValsB.pack` (that `Tv` is its `lastCount`, that
    `T ≤ m / k` where `cut` runs) is not in this statement. -/
theorem packLeafB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {o : Bool} {k n m lo hi : Nat} {p : String}
    {f : Cols} {A : Obj} {ox : Bool} {nv mv Tv : USize} {x xk : ValsB ox A mv} {y yk : ValsB ox A Tv}
    {lc hcl z sc ec z0 wc oc z1 scx G0 g1 uc gs ac hic0 bc loc hic : Enc} {f4 f6 f7 f8 f9 : Option UInt64}
    {r0 r1 : Enc × Option UInt64} {kk : Cols → Bld (Array Nat)} {out : Array Val}
    (hA : ColsOf A f)
    (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv)) (hlo : rs[lo]? = some (Reg.put lc))
    (hhi : rs[hi]? = some (Reg.put hcl)) (hx : (Cols.regs f).mapM (fun i => rs[i]?) = some x.regVals)
    (h1 : nv < 2 ^ 63) (h2 : mv < 2 ^ 63) (h3 : ¬ 2 ^ 63 / (mv + 1) < nv + 1)
    (hz : o = true → kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsm : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, lc), (nv, z)] [] [] = .ok (sc, f))
    (hem : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, hcl), (nv, z)] [] [] = .ok (ec, f))
    (hsc0 : o = false → sc = lc) (hec0 : o = false → ec = hcl)
    (hwb : kscan .sub false .i64 .i64 nv none [(nv, ec), (nv, sc)] [] [] = .ok (wc, f4))
    (hz0 : colConst nv 0 = .ok z0)
    (hk0 : kscan .add false .i64 .i64 nv (some z0) [(nv, z0), (nv, wc)] [] [] = .ok r0) (hr0 : nv ≠ 0 → r0.2.isSome)
    (hT : Tv = if nv = 0 then 0 else (r0.2.getD 0).toUSize + 0)
    (ho : kscan .sub false .i64 .i64 nv none [(nv, r0.1), (nv, wc)] [] [] = .ok (oc, f7))
    (hsc : kscatter .max nv oc .pos (Tv + 1) 0 = .ok scx)
    (hz1 : colConst (Tv + 1) 0 = .ok z1)
    (hk1 : kscan .max false .i64 .i64 (Tv + 1) (some z1) [(Tv + 1, z1), (Tv + 1, scx)] [] [] = .ok r1)
    (hr1 : Tv + 1 ≠ 0 → r1.2.isSome) (hG : kgather Tv .pos (Tv + 1) r1.1 = .ok G0)
    (hg1 : kgather Tv G0 nv oc = .ok g1)
    (hu : kscan .sub false .i64 .i64 Tv none [(Tv, .pos), (Tv, g1)] [] [] = .ok (uc, f8))
    (hgs : kgather Tv G0 nv sc = .ok gs)
    (hac : kscan .add false .i64 .i64 Tv none [(Tv, gs), (Tv, uc)] [] [] = .ok (ac, f9))
    (hgy : ValsB.gather Tv ac x = .ok y)
    (hhi0 : kscan .first false .i64 .i64 nv none [(nv, r0.1)] [] [] = .ok (hic0, f6))
    (hbig : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, lc), (nv, lc)] [] [(.and, 0), (.or, 0x7fffffffffffffff)] =
      .ok (bc, f))
    (hloc : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, oc)] [] [] = .ok (loc, f))
    (hhic : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, hic0)] [] [] = .ok (hic, f))
    (hloc0 : o = false → loc = oc) (hhic0 : o = false → hic = hic0) (hfo : Ordered fg.1)
    (hrecK : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val), (∃ a, fg2.1 = fg.1 ++ a) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Extends rs R → R[m]? = some (.size mv) → R[lo]? = some (Reg.put lc) →
      R[hi]? = some (Reg.put hcl) → (Cols.regs f).mapM (fun i => R[i]?) = some x.regVals →
      ∃ fg', Builds abiOf fg2 fg' (do
        let f' ← packB false k m f
        let L ← regsOf [.arr p m lo hi f']
        Pure.pure L.toArray) R ([.size mv, Reg.put lc, Reg.put hcl] ++ xk.regVals).toArray ∧ Ordered fg'.1)
    (hrecC : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (T' l2 h2 : Nat) (g' : Cols), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → R[T']? = some (.size Tv) → R[l2]? = some (Reg.put loc) →
      R[h2]? = some (Reg.put hic) → Cols.shape g' = Cols.shape f →
      (Cols.regs g').mapM (fun i => R[i]?) = some y.regVals →
      ∃ fg', Builds abiOf fg2 fg' (do
        let f' ← packB false k T' g'
        let L ← regsOf [.arr p T' l2 h2 f']
        Pure.pure L.toArray) R ([.size Tv, Reg.put loc, Reg.put hic] ++ yk.regVals).toArray)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (c : Col), (∃ a, fg2.1 = fg.1 ++ a) → GExt fg.2 fg2.2 →
      Extends rs R → ColsOf (.arr A) [c] →
      (Cols.regs [c]).mapM (fun i => R[i]?) = some (if decide (mv = 0) then [.size mv, Reg.put lc, Reg.put hcl] ++ xk.regVals
        else if decide (k ≠ 0 ∧ mv / k.toUSize < Tv) then [.size mv, Reg.put lc, Reg.put hcl] ++ xk.regVals
        else [.size Tv, Reg.put loc, Reg.put hic] ++ yk.regVals) →
      ∃ fg', Builds abiOf fg2 fg' (kk [c]) R out) :
    ∃ fg', Builds abiOf fg fg' (packB o k n [.arr p m lo hi f] >>= kk) rs out := by
  unfold packB
  simp (config := { etaStruct := .none }) only [List.attach_cons, List.attach_nil, List.map_nil, List.mapM_cons,
    List.mapM_nil, bind_assoc, pure_bind]
  have key : ∀ X : Unit → Bld (Array Nat), (cellsBoundB "pack" n m >>= X) =
      ((cellsBoundB "pack" n m >>= fun _ => Pure.pure (#[] : Array Nat)) >>= fun _ => X ()) := fun X => by simp
  rw [key]
  refine Builds.bindF (Free.bind (Free.cellsBoundB _ _ _) fun _ => Free.pure _)
    (cellsBoundB_builds (out := (#[] : Array Val)) hn hm h1 h2 h3 fun R _ => Builds.pure fun who => by simp; rfl)
    fun r xs hr => ?_
  have hE0 : Extends rs (rs ++ xs) := fun h => get_app h
  have hx0 := mapM_extends hE0 hx
  up hE0 [hn hm hlo hhi]
  refine Builds.bind2F (Free.packWidthsB _ _ _ _) (packWidthsB_builds hn hlo hhi hz hsm hem hsc0 hec0 hwb)
    fun s w R hsR hwR hE => ?_
  up hE [hn hm hlo hhi]
  replace hx0 := mapM_extends hE hx0
  dsimp only
  simp (config := { etaStruct := .none }) only [bind_assoc]
  refine prefixB_builds (nv := nv) (av := wc) (z := z0) (r := r0) (by rop) hn hwR hz0 hk0 hr0 hfo ?_
  intro fg3 P Tr ys' he3 hf3 hfo3 hP hTr
  rw [← hT] at hTr
  have hE1 : Extends R (R ++ ys') := fun h => get_app h
  up hE1 [hn hm hlo hhi hsR hwR]
  replace hx0 := mapM_extends hE1 hx0
  refine Builds.bind1F (Free.packWideB _ _ _) (packWideB_builds hm hTr) fun xw R1 hxw hE2 => ?_
  up hE2 [hn hm hlo hhi hsR hwR hP hTr]
  replace hx0 := mapM_extends hE2 hx0
  rw [← bind_assoc (lit (.size 0)) (fun c => call1 (kernel% USize.decEq) #[m, c])]
  refine Builds.bind1F (decEq0B_free _) (decEq0B_builds hm) fun xz R2 hxz hE3 => ?_
  up hE3 [hn hm hlo hhi hsR hwR hP hTr hxw]
  replace hx0 := mapM_extends hE3 hx0
  have hlen := hA.regs_length xk
  have hlen' := hA.regs_length yk
  have hER2 : Extends rs R2 := fun h => hE3 (hE2 (hE1 (hE (hE0 h))))
  refine Builds.ite2E hxz hxw (by simp [← hlen, ← hlen']) hfo3
    (fun fg0 h0 g0 o0 => hrecK fg0 R2 (exFun_trans he3 h0) (hf3.trans g0) o0 hER2 hm hlo hhi hx0)
    (fun fg0 h0 g0 o0 => packCutB_builds (hi := hi) hA hn hm hlo hsR hwR hP hx0 hz0 hk0 hr0 hT ho hsc hz1 hk1 hr1
      hG hg1 hu hgs hac hgy hhi0 hbig hloc hhic hloc0 hhic0 o0 fun fg2' R' T' l2 h2' g' he hf hfo' hE' hT' hl2 hh2
      hsh hreg => hrecC fg2' R' T' l2 h2' g' (exFun_trans (exFun_trans he3 h0) he) ((hf3.trans g0).trans hf) hfo'
      (fun h => hE' (hER2 h)) hT' hl2 hh2 hsh hreg) ?_
  intro fgc a R3 hext hgext hread hE4
  have hEa : Extends rs R3 := fun h => hE4 (hER2 h)
  have hl : a.toList.length = (Cols.regs [Col.arr p m lo hi f]).length := by
    rw [omapM_length hread]; split <;> (try split) <;> simp [Cols.regs, Col.regs, ← hlen, ← hlen']
  obtain ⟨cs', hw, hcs', hreg, hlen1⟩ := withRegs_colsOf (.arr A) (cs := [Col.arr p m lo hi f])
    ⟨p, m, lo, hi, f, rfl, hA⟩ a.toList [] (by simpa using hl)
  rw [List.append_nil] at hw
  obtain ⟨c, rfl⟩ : ∃ c, cs' = [c] := by
    cases cs' with
    | nil => simp at hlen1
    | cons c t => cases t <;> simp at hlen1 ⊢
  simp only [hw, pure_bind]
  refine hkk fgc R3 c (exFun_trans he3 hext) (hf3.trans hgext) hEa hcs' ?_
  rw [hreg, hread]; congr 1
  split <;> (try split) <;> simp

end Rel.Lang.Plan
