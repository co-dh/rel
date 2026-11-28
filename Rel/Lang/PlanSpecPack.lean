module

public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecConcat
public import Rel.Lang.PlanSpecSelect
public import Rel.Lang.PlanSpecCross

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `spanB`, `cellsBoundB`: the builders `packB` opens each array column with

`spanB` is `funW` of four `kscan`s (`colMap`) and two `kscatter`s (`colConst`), the clamp `cellSpan`:
`s = max lo 0`, `e = max (min hi m) s`. `cellsBoundB` is the size-register test of `ValsB.pack`'s `2^63` check, built
from `USize` kernel calls and `ite`s, then `guard`. As in `PlanSpecPrefix`, the kernel answers are premises. -/

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

theorem Grows.spanB (n m lo hi : Nat) : Grows (Plan.spanB n m lo hi) := by
  unfold Plan.spanB
  refine (Grows.funW fun n ws => ?_).bind fun p => ?_
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.u64B _).bind
        fun _ => (Grows.constB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
        (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · dsimp only
    split
    · exact Grows.pure _
    · exact Grows.throw _

theorem Typed.spanB {lv n m lo hi : Nat} (hn : lv ≤ n) (hlo : lv ≤ lo) (hhi : lv ≤ hi) :
    Typed lv (fun r => lv ≤ r.1 ∧ lv ≤ r.2) (Plan.spanB n m lo hi) := by
  unfold Plan.spanB
  refine (Typed.funW hn (fun _ h => by simp at h; omega) fun n ws hn' hws => ?_).bind fun p hp => ?_
  · rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
    · exact Typed.throw _
    · exact Typed.throw _
    · have ha : lv ≤ a := hws a (by simp)
      have hb : lv ≤ b := hws b (by simp)
      exact Typed.wordsB.bind fun z hz => (Typed.mapB hn' ha hz).bind fun s hs => Typed.u64B.bind fun u hu =>
        Typed.constB.bind fun c hc => (Typed.mapB hn' hb hc).bind fun d hd => (Typed.mapB hn' hd hs).bind
        fun e he => Typed.pure ⟨hn', fun x hx => by simp at hx; omega⟩
    · exact Typed.throw _
  · obtain ⟨l, _ | ⟨s, _ | ⟨e, _ | ⟨_, _⟩⟩⟩⟩ := p
    · exact Typed.throw _
    · exact Typed.throw _
    · exact Typed.pure ⟨hp.2 s (by simp), hp.2 e (by simp)⟩
    · exact Typed.throw _

/-- **`spanB` builds the `cellSpan` clamp**: `n` holding the count `nv`, `m` the payload size `mv`, `lo`, `hi` the
    bounds `lc`, `hc`. `s = max lo 0` (`z` the zeros), `d = min hi mv` (`cm` the constant column of `mv`),
    `e = max d s`: the kernel answers are premises, as in `prefixB_builds`; `kk` continues with the registers of `s`
    and `e`. -/
theorem spanB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n m lo hi : Nat} {nv mv : USize}
    {lc hc z cm sc dc ec : Enc} {f1 f2 f3 : Option UInt64} {kk : Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv)) (hlo : rs[lo]? = some (Reg.put lc))
    (hhi : rs[hi]? = some (Reg.put hc))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hs : kscan .max false .i64 .i64 nv none [(nv, lc), (nv, z)] [] [] = .ok (sc, f1))
    (hcm : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv mv.toUInt64 = .ok cm)
    (hd : kscan .min false .i64 .i64 nv none [(nv, hc), (nv, cm)] [] [] = .ok (dc, f2))
    (he : kscan .max false .i64 .i64 nv none [(nv, dc), (nv, sc)] [] [] = .ok (ec, f3)) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (s e : Nat) (ys : Array Val), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → (rs ++ ys)[s]? = some (Reg.put sc) → (rs ++ ys)[e]? = some (Reg.put ec) →
      ∃ fg', Builds abiOf fg2 fg' (kk (s, e)) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (spanB n m lo hi >>= kk) rs out := by
  unfold spanB
  rw [bind_assoc]
  let pv : Array Val := #[Val.size nv, Reg.put lc, Reg.put hc]
  have hn' : (rs ++ pv)[rs.size]? = some (.size nv) := by simp [pv]
  have hlo' : (rs ++ pv)[rs.size + 1]? = some (Reg.put lc) := by simp [pv]
  have hhi' : (rs ++ pv)[rs.size + 2]? = some (Reg.put hc) := by simp [pv]
  have hm' : (rs ++ pv)[m]? = some (.size mv) := get_app hm
  refine funW_builds (k := 2) (pv := pv) (o := #[.size nv, Reg.put sc, Reg.put ec])
    (fun _ => reads_of (by simp [hn, hlo, hhi])) rfl ⟨fg, ?_⟩ ?_ (fun n ws => ?_) hfo ?_
  · rw [show List.range' (rs.size + 1) [lo, hi].length = [rs.size + 1, rs.size + 2] from rfl]
    dsimp only
    simp only [bind_assoc]
    refine Builds.bind1G (wordsB_builds hn' hz) fun z' R1 hz1 m1 => ?_
    up m1 [hn' hm' hlo' hhi']
    refine Builds.bind1G (mapB_builds hn' hlo' (enc_get_put _) hz1 (enc_get_put _) (by rop) (qtype_get_put _)
      (qtype_get_put _) (pre := []) (post := []) (by rop) (by rop) hs) fun s' R2 hs2 m2 => ?_
    up m2 [hn' hm' hhi']
    refine Builds.bind1G (u64B_builds hm') fun u R3 hu3 m3 => ?_
    up m3 [hn' hhi' hs2]
    refine Builds.bind1G (constB_builds hn' hu3 hcm) fun c' R4 hc4 m4 => ?_
    up m4 [hn' hhi' hs2]
    refine Builds.bind1G (mapB_builds hn' hhi' (enc_get_put _) hc4 (enc_get_put _) (by rop) (qtype_get_put _)
      (qtype_get_put _) (pre := []) (post := []) (by rop) (by rop) hd) fun d' R5 hd5 m5 => ?_
    up m5 [hn' hs2]
    refine Builds.bind1G (mapB_builds hn' hd5 (enc_get_put _) hs2 (enc_get_put _) (by rop) (qtype_get_put _)
      (qtype_get_put _) (pre := []) (post := []) (by rop) (by rop) he) fun e' R6 he6 m6 => ?_
    up m6 [hn' hs2]
    simp only [pure_bind]
    exact Builds.answerRegs ⟨rfl, [s', e'], rfl, rfl⟩ (tabsRegs_eq _) fun _ => reads_of (by
      simp [TabB.regs, Cols.regs, Col.regs, hn', hs2, he6])
  · rw [show List.range' (rs.size + 1) [lo, hi].length = [rs.size + 1, rs.size + 2] from rfl]
    dsimp only
    exact Typed.wordsB.bind fun z hz => (Typed.mapB (Nat.le_refl _) (Nat.le_succ _) hz).bind fun s hs =>
      Typed.u64B.bind fun u hu => Typed.constB.bind fun c hc => (Typed.mapB (Nat.le_refl _) (by omega) hc).bind
      fun d hd => (Typed.mapB (Nat.le_refl _) hd hs).bind fun e he => Typed.pure trivial
  · dsimp only
    split
    · exact (Grows.wordsB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.u64B _).bind
        fun _ => (Grows.constB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
        (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => Grows.pure _
    · exact Grows.throw _
  · intro fg2 mm es ys he' hf ho hl hread
    match es, hl with
    | [s, e], _ =>
      obtain ⟨-, hread⟩ := mapM_get_cons hread
      obtain ⟨hp, hread⟩ := mapM_get_cons hread
      obtain ⟨hq, -⟩ := mapM_get_cons hread
      simp only [pure_bind]
      exact hkk fg2 s e ys he' hf ho hp hq

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

/-- **The `wide` test of `packB`**: `m < T · k` on the size registers `m`, `T`, as `USize.mul` and `USize.decLt` read
    them. -/
theorem wideB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {m T k : Nat} {mv Tv : USize}
    (hm : rs[m]? = some (.size mv)) (hT : rs[T]? = some (.size Tv)) :
    Builds abiOf fg fg (do
      let r ← (do let c ← lit (.size k.toUSize); let q ← call1 (kernel% USize.mul) #[T, c]
                  call1 (kernel% USize.decLt) #[m, q])
      Pure.pure #[r]) rs #[Val.bit (decide (mv < Tv * k.toUSize))] := by
  simp only [bind_assoc]
  refine Builds.litG fun c R1 hc1 m1 => ?_
  up m1 [hm hT]
  refine Builds.call1G (vs := #[.size Tv, .size k.toUSize]) (v := .size (Tv * k.toUSize)) (by abiK) (by rop) ?_ ?_ rfl
    fun q R2 hq2 m2 => ?_
  · rw [List.mapM_toArray]; simp [reg, hT, hc1]; rfl
  · simp [arg]; rfl
  up m2 [hm]
  refine Builds.call1G (vs := #[.size mv, .size (Tv * k.toUSize)]) (v := Val.bit (decide (mv < Tv * k.toUSize)))
    (by abiK) (by rop) ?_ ?_ rfl fun b R3 hb3 m3 => Builds.pure fun who => ?_
  · rw [List.mapM_toArray]; simp [reg, hm, hq2]; rfl
  · simp [arg]; exact out_decLt' _ _
  · simp [reg, hb3]; rfl

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

/-- **The head of `packB`'s array case builds**: `cellsBoundB`, `spanB`, `mapB .sub n e s` (the widths `w`), `prefixB .add`
    (`P`, the last word `T`). Every step before `prefixB` reads nothing of its block (`Free`) or is `spanB`, so the
    continuation `kk` is stated on registers `R` extending `rs`; the kernel answers are premises, as in
    `expandB_builds`. -/
theorem packHeadB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n m lo hi : Nat} {nv mv Tv : USize}
    {what : String} {lc hc z cm sc dc ec z0 wc : Enc} {f1 f2 f3 f4 : Option UInt64} {r0 : Enc × Option UInt64}
    {α : Type} {kk : Nat → Nat → Nat → Nat → Nat → Bld α} {post : α → Bld (Array Nat)} {out : Array Val}
    (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv)) (hlo : rs[lo]? = some (Reg.put lc))
    (hhi : rs[hi]? = some (Reg.put hc)) (h1 : nv < 2 ^ 63) (h2 : mv < 2 ^ 63) (h3 : ¬ 2 ^ 63 / (mv + 1) < nv + 1)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hs : kscan .max false .i64 .i64 nv none [(nv, lc), (nv, z)] [] [] = .ok (sc, f1))
    (hcm : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv mv.toUInt64 = .ok cm)
    (hd : kscan .min false .i64 .i64 nv none [(nv, hc), (nv, cm)] [] [] = .ok (dc, f2))
    (he : kscan .max false .i64 .i64 nv none [(nv, dc), (nv, sc)] [] [] = .ok (ec, f3))
    (hw : kscan .sub false .i64 .i64 nv none [(nv, ec), (nv, sc)] [] [] = .ok (wc, f4))
    (hz0 : colConst nv 0 = .ok z0)
    (hk0 : kscan .add false .i64 .i64 nv (some z0) [(nv, z0), (nv, wc)] [] [] = .ok r0) (hr0 : nv ≠ 0 → r0.2.isSome)
    (hT : Tv = if nv = 0 then 0 else (r0.2.getD 0).toUSize + 0) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (s e w P T : Nat) (R : Array Val), (∃ a, fg2.1 = fg.1 ++ a) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → R[s]? = some (Reg.put sc) → R[e]? = some (Reg.put ec) →
      R[w]? = some (Reg.put wc) → R[P]? = some (Reg.put r0.1) → R[T]? = some (.size Tv) →
      ∃ fg', Builds abiOf fg2 fg' (kk s e w P T >>= post) R out) :
    ∃ fg', Builds abiOf fg fg' (do
      cellsBoundB what n m
      let x ← spanB n m lo hi
      let c ← (match x with
        | (s, e) => do
          let w ← mapB .sub n e s
          let (P, T) ← prefixB .add n w
          kk s e w P T)
      post c) rs out := by
  have key : ∀ X : Unit → Bld (Array Nat), (cellsBoundB what n m >>= X) =
      ((cellsBoundB what n m >>= fun _ => Pure.pure (#[] : Array Nat)) >>= fun _ => X ()) := fun X => by simp
  rw [key]
  refine Builds.bindF (Free.bind (Free.cellsBoundB _ _ _) fun _ => Free.pure _)
    (cellsBoundB_builds (out := (#[] : Array Val)) hn hm h1 h2 h3 fun R _ => Builds.pure fun who => by simp; rfl) fun r xs hr => ?_
  have hn1 := get_app (xs := xs) hn
  have hm1 := get_app (xs := xs) hm
  have hlo1 := get_app (xs := xs) hlo
  have hhi1 := get_app (xs := xs) hhi
  refine spanB_builds hn1 hm1 hlo1 hhi1 hz hs hcm hd he hfo ?_
  intro fg2 s e ys he1 hf hfo2 hsr her
  have hn2 := get_app (xs := ys) hn1
  dsimp only
  simp only [bind_assoc]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn2 her (enc_get_put _) hsr (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hw) fun w R hwR hE => ?_
  up hE [hn2 hsr her]
  refine prefixB_builds (nv := nv) (av := wc) (z := z0) (r := r0) (by rop) hn2 hwR hz0 hk0 hr0 hfo2 ?_
  intro fg3 P Tr ys' he3 hf3 hfo3 hP hTr
  rw [← hT] at hTr
  obtain ⟨a1, ha1⟩ := he1
  obtain ⟨a3, ha3⟩ := he3
  refine hkk fg3 s e w P Tr (R ++ ys') ⟨a1 ++ a3, by rw [ha3, ha1, Array.append_assoc]⟩ (hf.trans hf3) hfo3
    (fun h => get_app (hE (get_app (get_app h)))) (get_app hsr) (get_app her) (get_app hwR) hP hTr


/-- **The cut branch of `packB` builds**: the registers `n` (count `nv`), `m` (payload count `mv`), `lo`, `s`, `w`, `P` hold
    the head's values (`packHeadB_builds`), `expandB n w` the kernel answers `expandB_builds` names (`Tv` the cut payload's
    row count, `G0` the groups, `uc` the offsets), `gatherB` the source rows `gs = s[G]`, `mapB .add` the positions
    `ac = gs + u`, `gatherCols` (`ValsB.gather Tv ac x = .ok y`) the payload `f` cut to them, `mapB .sub`/`.add` the new
    bounds `oc = P - w` and `hic0 = P + 0` (`zc` the zeros). Where `o` holds the bounds are `min`ed with `big` (`bc`); else
    they are `oc`, `hic0`. The recursion on the cut payload is the premise `hrec`: its registers hold `Tv`, the new bounds
    `loc`, `hic`, and `y`'s values, and it builds `out`. -/
theorem packCutB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {o : Bool} {k n m lo hi s w P : Nat}
    {p : String} {f : Cols} {A : Obj} {ox : Bool} {nv mv Tv : USize} {x : ValsB ox A mv} {y : ValsB ox A Tv}
    {lc sc wc z0 oc z1 scx G0 g1 uc gs ac zc hic0 bc loc hic : Enc} {r0 r1 : Enc × Option UInt64}
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
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok zc)
    (hhi0 : kscan .add false .i64 .i64 nv none [(nv, r0.1), (nv, zc)] [] [] = .ok (hic0, f6))
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
      let lo' ← mapB .sub n P w
      let hi' ← mapB .add n P (← wordsB n 0)
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
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn hP (enc_get_put _) hw (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ho) fun l1 R4 hl4 hE4 => ?_
  up hE4 [ha hn hm hlo hs hw hP]
  refine Builds.bind1F (Free.wordsB _ _) (wordsB_builds hn hz) fun zr R5 hz5 hE5 => ?_
  up hE5 [ha hn hm hlo hs hw hP hl4]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn hP (enc_get_put _) hz5 (enc_get_put _) (by rop)
    (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hhi0) fun h1 R6 hh6 hE6 => ?_
  up hE6 [ha hn hm hlo hs hw hP hl4 hz5]
  have hEx : Extends rs R6 := fun h => hE6 (hE5 (hE4 (hE3 (hE2 (hE1 (hE0 h))))))
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
    exact hrec fg3 R6 a l1 h1 g' hext (hf.trans hf3) hfo3 hEx ha hl4 hh6 hsh (mapM_extends (fun h => hE6 (hE5 (hE4 h))) hreg)
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
      (mapM_extends (fun h => hE9 (hE8 (hE7 (hE6 (hE5 (hE4 h)))))) hreg)



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

theorem wideB_free (m T k : Nat) : Free (do
    let c ← lit (.size k.toUSize); let q ← call1 (kernel% USize.mul) #[T, c]
    call1 (kernel% USize.decLt) #[m, q]) := by free''

theorem decEq0B_free (m : Nat) : Free (do
    let c ← lit (.size 0); call1 (kernel% USize.decEq) #[m, c]) := by free''




theorem omapM_length {R : Array Val} : ∀ {l : List Nat} {vs : List Val}, l.mapM (fun x => R[x]?) = some vs →
    l.length = vs.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    obtain ⟨v, vs, hx, hl, rfl⟩ := omapM_cons.mp h
    simp [omapM_length hl]

/-- **`packB` of one array column over atom columns builds**, branch by branch: the head (`packHeadB_builds`), the bits
    `m = 0` (`decEq0B_builds`) and `m < T · k` (`wideB_builds`), `Builds.ite` over `ite (m = 0) keep (ite wide keep cut)`.
    `keep` reads back the registers it was given (an atom payload is `packB`-fixed, `packB_atoms`); `cut` is
    `packCutB_builds`, whose recursion on the cut payload is `pure` for atoms. Then `withRegs` hands the one column `c` back
    to `kk`, which reads, per branch, `Kl` (`m`, `lo`, `hi` and `x`'s registers as they were) or `Cl` (the count `Tv`, the
    new bounds `loc`, `hic`, and `y`'s registers). The link to `ValsB.pack` (that `Tv` is its `lastCount`, that `k · lastCount
    ≤ m` where `cut` runs, that `spanB`'s clamp is its `cellSpan`) is not in this statement. -/
theorem packLeafB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {o : Bool} {k n m lo hi : Nat} {p : String}
    {f : Cols} {A : Obj} {ox : Bool} {nv mv Tv : USize} {x : ValsB ox A mv} {y : ValsB ox A Tv}
    {lc hcl z cm sc dc ec z0 wc oc z1 scx G0 g1 uc gs ac hic0 bc loc hic : Enc} {f1 f2 f3 f4 f7 f8 f9 : Option UInt64}
    {r0 r1 : Enc × Option UInt64} {kk : Cols → Bld (Array Nat)} {out : Array Val}
    (hA : ColsOf A f) (hat : ∀ c ∈ f, ∃ q t e, c = Col.atom q t e)
    (hn : rs[n]? = some (.size nv)) (hm : rs[m]? = some (.size mv)) (hlo : rs[lo]? = some (Reg.put lc))
    (hhi : rs[hi]? = some (Reg.put hcl)) (hx : (Cols.regs f).mapM (fun i => rs[i]?) = some x.regVals)
    (h1 : nv < 2 ^ 63) (h2 : mv < 2 ^ 63) (h3 : ¬ 2 ^ 63 / (mv + 1) < nv + 1)
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsm : kscan .max false .i64 .i64 nv none [(nv, lc), (nv, z)] [] [] = .ok (sc, f1))
    (hcm : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv mv.toUInt64 = .ok cm)
    (hd : kscan .min false .i64 .i64 nv none [(nv, hcl), (nv, cm)] [] [] = .ok (dc, f2))
    (hem : kscan .max false .i64 .i64 nv none [(nv, dc), (nv, sc)] [] [] = .ok (ec, f3))
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
    (hhi0 : kscan .add false .i64 .i64 nv none [(nv, r0.1), (nv, z)] [] [] = .ok (hic0, f4))
    (hbig : o = true → ∃ f, kscan .max false .i64 .i64 nv none [(nv, lc), (nv, lc)] [] [(.and, 0), (.or, 0x7fffffffffffffff)] =
      .ok (bc, f))
    (hloc : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, oc)] [] [] = .ok (loc, f))
    (hhic : o = true → ∃ f, kscan .min false .i64 .i64 nv none [(nv, bc), (nv, hic0)] [] [] = .ok (hic, f))
    (hloc0 : o = false → loc = oc) (hhic0 : o = false → hic = hic0) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (c : Col), (∃ a, fg2.1 = fg.1 ++ a) → GExt fg.2 fg2.2 →
      Extends rs R → ColsOf (.arr A) [c] →
      (Cols.regs [c]).mapM (fun i => R[i]?) = some (if decide (mv = 0) then [.size mv, Reg.put lc, Reg.put hcl] ++ x.regVals
        else if decide (mv < Tv * k.toUSize) then [.size mv, Reg.put lc, Reg.put hcl] ++ x.regVals
        else [.size Tv, Reg.put loc, Reg.put hic] ++ y.regVals) →
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
  have hn1 := get_app (xs := xs) hn
  have hm1 := get_app (xs := xs) hm
  have hlo1 := get_app (xs := xs) hlo
  have hhi1 := get_app (xs := xs) hhi
  have hx1 := mapM_get_app (xs := xs) hx
  refine spanB_builds hn1 hm1 hlo1 hhi1 hz hsm hcm hd hem hfo ?_
  intro fg2 s e ys he1 hf hfo2 hsr her
  have hn2 := get_app (xs := ys) hn1
  dsimp only
  rw [bind_assoc]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hn2 her (enc_get_put _) hsr (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hwb) fun w R hwR hE => ?_
  replace hm1 := get_app (xs := ys) hm1
  replace hlo1 := get_app (xs := ys) hlo1
  replace hhi1 := get_app (xs := ys) hhi1
  replace hx1 := mapM_get_app (xs := ys) hx1
  up hE [hn2 hsr her hm1 hlo1 hhi1]
  replace hx1 := mapM_extends hE hx1
  rw [bind_assoc]
  refine prefixB_builds (nv := nv) (av := wc) (z := z0) (r := r0) (by rop) hn2 hwR hz0 hk0 hr0 hfo2 ?_
  intro fg3 P Tr ys' he3 hf3 hfo3 hP hTr
  rw [← hT] at hTr
  dsimp only
  simp (config := { etaStruct := .none }) only [bind_assoc]
  have b3 : ∀ {α β γ δ : Type} (a : Bld α) (f : α → Bld β) (g : β → Bld γ) (kx : γ → Bld δ),
      (a >>= fun x => f x >>= fun y => g y >>= kx) = ((a >>= fun x => f x >>= g) >>= kx) := fun a f g kx => by simp
  rw [b3]
  have hm2 := get_app (xs := ys') hm1
  have hn3 := get_app (xs := ys') hn2
  have hs3 := get_app (xs := ys') hsr
  have hw3 := get_app (xs := ys') hwR
  have hlo3 := get_app (xs := ys') hlo1
  have hhi3 := get_app (xs := ys') hhi1
  have hx3 := mapM_get_app (xs := ys') hx1
  refine Builds.bind1F (wideB_free _ _ _) (wideB_builds (k := k) hm2 hTr) fun xw R1 hxw hE1 => ?_
  rw [← bind_assoc]
  up hE1 [hm2 hn3 hs3 hw3 hlo3 hhi3 hP hTr]
  replace hx3 := mapM_extends hE1 hx3
  refine Builds.bind1F (decEq0B_free _) (decEq0B_builds hm2) fun xz R2 hxz hE2 => ?_
  up hE2 [hm2 hn3 hs3 hw3 hlo3 hhi3 hP hTr hxw]
  replace hx3 := mapM_extends hE2 hx3
  have hlen := hA.regs_length x
  have hlen' := hA.regs_length y
  have hkeep : ∀ fg0 : Array Fun × Array Fun, Builds abiOf fg0 fg0 (do
      let f' ← packB false k m f; let L ← regsOf [Col.arr p m lo hi f']; Pure.pure L.toArray) R2
      ([.size mv, Reg.put lc, Reg.put hcl] ++ x.regVals).toArray := fun fg0 => by
    rw [packB_atoms _ _ _ _ hat, pure_bind, regsOf_eq, pure_bind]
    exact Builds.pure fun who => reads_of (by simp [Cols.regs, Col.regs, hm2, hlo3, hhi3, hx3])
  have hcut : ∃ fg', Builds abiOf fg3 fg' (do
      let __discr ← expandB n w
      let __do_lift ← gatherB __discr.fst __discr.2.fst n s
      let __do_lift ← mapB Op.add __discr.fst __do_lift __discr.2.snd
      let g ← gatherCols __discr.fst __do_lift m f
      let lo' ← mapB Op.sub n P w
      let __do_lift ← wordsB n 0
      let hi' ← mapB Op.add n P __do_lift
      if o = true then do
          let big ← mapB Op.max n lo lo QAtomicType.i64 QAtomicType.i64 [] [(Op.and, 0), (Op.or, 9223372036854775807)]
          let __do_lift ← mapB Op.min n big lo'
          let __do_lift_1 ← mapB Op.min n big hi'
          if h : Col.sizes g ≤ Col.sizes f then do
              let __do_lift_2 ← packB false k __discr.fst g
              let __do_lift ← regsOf [Col.arr p __discr.fst __do_lift __do_lift_1 __do_lift_2]
              pure __do_lift.toArray
            else throw "pack: the gathered payload is larger than the payload"
        else
          if h : Col.sizes g ≤ Col.sizes f then do
            let __do_lift ← packB false k __discr.fst g
            let __do_lift ← regsOf [Col.arr p __discr.fst lo' hi' __do_lift]
            pure __do_lift.toArray
          else throw "pack: the gathered payload is larger than the payload") R2
      ([.size Tv, Reg.put loc, Reg.put hic] ++ y.regVals).toArray := by
    refine packCutB_builds (hi := hi) hA hn3 hm2 hlo3 hs3 hw3 hP hx3 hz0 hk0 hr0 hT ho hsc hz1 hk1 hr1 hG hg1 hu hgs hac hgy hz hhi0
      hbig hloc hhic hloc0 hhic0 hfo3 ?_
    intro fg2' R T' l2 h2 g' he hf hfo' hE hT' hl2 hh2 hsh hreg
    refine ⟨fg2', ?_⟩
    rw [packB_atoms _ _ _ _ (atoms_of_shape hsh hat), pure_bind, regsOf_eq, pure_bind]
    exact Builds.pure fun who => reads_of (by simp [Cols.regs, Col.regs, hT', hl2, hh2, hreg])
  obtain ⟨fgc, hcut⟩ := hcut
  have hsz : ([Val.size mv, Reg.put lc, Reg.put hcl] ++ x.regVals).toArray.size =
      ([Val.size Tv, Reg.put loc, Reg.put hic] ++ y.regVals).toArray.size := by simp [← hlen, ← hlen']
  refine Builds.bindFG (Free.ite _ _ _) (Builds.ite hxz (hkeep fg3) (Builds.ite hxw (hkeep fg3) hcut hsz)
    (by split <;> simp [← hlen, ← hlen'])) ?_
  intro a R3 hread hE3
  have hEa : Extends rs R3 := fun h => hE3 (hE2 (hE1 (get_app (hE (get_app (get_app h))))))
  have hl : a.toList.length = (Cols.regs [Col.arr p m lo hi f]).length := by
    rw [omapM_length hread]; split <;> (try split) <;> simp [Cols.regs, Col.regs, ← hlen, ← hlen']
  obtain ⟨cs', hw, hcs', hreg, hlen1⟩ := withRegs_colsOf (.arr A) (cs := [Col.arr p m lo hi f])
    ⟨p, m, lo, hi, f, rfl, hA⟩ a.toList [] (by simpa using hl)
  rw [List.append_nil] at hw
  obtain ⟨c, rfl⟩ : ∃ c, cs' = [c] := by
    cases cs' with
    | nil => simp at hlen1
    | cons c t => cases t <;> simp at hlen1 ⊢
  obtain ⟨a1, ha1⟩ := he1
  obtain ⟨a3, ha3⟩ := he3
  obtain ⟨ac, hac'⟩ := hcut.1
  simp only [hw, pure_bind]
  refine hkk fgc R3 c ⟨a1 ++ (a3 ++ ac), by simp [hac', ha3, ha1, Array.append_assoc]⟩
    (hf.trans (hf3.trans hcut.2.1)) hEa hcs' ?_
  rw [hreg]
  rw [hread]; congr 1
  split <;> (try split) <;> simp

end Rel.Lang.Plan
