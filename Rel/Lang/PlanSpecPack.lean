module

public import Rel.Lang.PlanSpecPrefix
public import Rel.Lang.PlanSpecConcat

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

end Rel.Lang.Plan
