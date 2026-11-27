module

public import Rel.Lang.PlanSpecSelect
public import Rel.Lang.PlanSpecNone

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `crossB` builds `Vals.cross`, `pairB` builds `Tab.pair`

`crossB n m xs ys` checks the pair count (`crossMax`, then `2^63`), writes the constant column of `m`, and gathers the two
sides at `pos / m` and `pos % m`: `crossIx`'s two `colMap .first … [(.rdiv, m)]` columns, which equal the `.div`, `.mod`
of `pos` by that column (`colMap_const_eq`). -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- `if c then t else e` with the bit in `c` clear: `t` is only built — its instructions never run, so it need not succeed
    (`crossB`'s over-the-bound branch is a `fail`) — and `e` builds and runs. -/
theorem Builds.ite_false {abi : String → Option Kernel} {fg fg1 fg2 : Array Fun × Array Fun} {c : Nat}
    {t e : Bld (Array Nat)} {rs oe : Array Val}
    {jt : Array Instr} {n' : Nat} {rt : Array Nat} (hc : rs[c]? = some (.bit false))
    (ht : t.run (#[], rs.size, fg) = .ok (rt, jt, n', fg1)) (he : Builds abi fg1 fg2 e rs oe) (hs : rt.size = oe.size)
    (h1 : (∃ a, fg1.1 = fg.1 ++ a) ∧ GExt fg.2 fg1.2) :
    Builds abi fg fg2 (Plan.ite c t e) rs oe := by
  obtain ⟨⟨a1, ha1⟩, hb1⟩ := h1
  obtain ⟨⟨a2, ha2⟩, hb2, he⟩ := he
  obtain ⟨je, xe, re, hre, hbe, hme⟩ := he #[]
  have se : oe.size = re.size := mapM_ok_size (hme "")
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, hb1.trans hb2,
    fun is => ⟨#[.ite c jt.toList rt je.toList re], oe, (List.range' rs.size re.size).toArray, ?_, fun fs gs hE ws => ?_,
    fun who => se ▸ mapM_reg_range rs _ who⟩⟩
  · have hrs : rt.size = re.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, ht, hre,
      ok_bind, pure_bind, bind_assoc]
    simp [hrs, emit_run]; omega
  · rw [show (#[Instr.ite c jt.toList rt je.toList re] : Array Instr).toList = [.ite c jt.toList rt je.toList re]
      from rfl, runB.eq_2]
    simp [runI, reg_of hc, hbe fs gs hE, hme, runB.eq_1, ok_bind, Functor.map, Except.map]

/-- `b`, `Free` of its block, then `k` on its registers, holding `o`, in registers extending `rs` (`Builds.bindG` whose rest
    may add functions). -/
theorem Builds.bindFG {fg fg1 : Array Fun × Array Fun} {b : Bld (Array Nat)} {k : Array Nat → Bld (Array Nat)}
    {rs o out : Array Val} (hF : Free b) (hb : Builds abiOf fg fg1 b rs o)
    (hk : ∀ a R, a.toList.mapM (fun x => R[x]?) = some o.toList → Extends rs R →
      ∃ fg', Builds abiOf fg1 fg' (k a) R out) : ∃ fg', Builds abiOf fg fg' (b >>= k) rs out :=
  Builds.bindF hF hb fun a _ h => hk a _ (holds_of_reg (h "")) fun h => get_app h

/-- `lit x`, then `k` on a register holding `x`. -/
theorem litE {fg : Array Fun × Array Fun} {rs out : Array Val} {x : Val} {k : Nat → Bld (Array Nat)}
    (hk : ∀ r R, R[r]? = some x → Extends rs R → ∃ fg', Builds abiOf fg fg' (k r) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.lit x >>= k) rs out :=
  Builds.bind1F (Free.lit x) (Builds.litG fun r R hr _ => Builds.pure fun _ => reads_of (l := [r]) (vs := [x])
    (by simp [hr])) hk

/-- `call1 kn as`, then `c` on a register holding its one value `v`. -/
theorem call1E {fg : Array Fun × Array Fun} {rs out vs : Array Val} {kn : Kernel}
    {f : Array Val → Except String (Array Val)} {as : Array Nat} {v : Val} {c : Nat → Bld (Array Nat)}
    (hk : abiOf kn.sym = some kn) (hf : kn.run = .inl f) (ha : as.mapM (reg rs kn.sym) = .ok vs)
    (ho : f vs = .ok #[v]) (hs : kn.res.size = 1)
    (hc : ∀ r R, R[r]? = some v → Extends rs R → ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.call1 kn as >>= c) rs out :=
  Builds.bind1F (Free.call1 kn as) (Builds.call1G hk hf ha ho hs fun r R hr _ => Builds.pure fun _ =>
    reads_of (l := [r]) (vs := [v]) (by simp [hr])) hc

/-- `guard c` with the bit in `c` set builds nothing: `k` follows. -/
theorem Builds.guardE {fg : Array Fun × Array Fun} {c : Nat} {msg : String} {as : Array Nat} {k : Bld (Array Nat)}
    {rs out : Array Val} (hc : rs[c]? = some (.bit true)) (hk : ∃ fg', Builds abiOf fg fg' k rs out) :
    ∃ fg', Builds abiOf fg fg' (Plan.guard c msg as >>= fun _ => k) rs out :=
  let ⟨fg', h⟩ := hk
  ⟨fg', Builds.guard hc h⟩

theorem discard_eq {α : Type} (x : Bld α) : discard x = (x >>= fun _ => Pure.pure PUnit.unit) := rfl

theorem ext_trans {R R1 R2 : Array Val} (h1 : ∀ (i : Nat) (v : Val), R[i]? = some v → R1[i]? = some v) (h2 : Extends R1 R2) :
    ∀ (i : Nat) (v : Val), R[i]? = some v → R2[i]? = some v := fun _ _ h => h2 (h1 _ _ h)

set_option hygiene false in
/-- `up`, and the column-register facts `hx`, `hy` and the extension `hext` of the first registers with it. -/
local macro "upx " m:ident " [" hs:ident* "]" : tactic => do
  let rs ← hs.mapM fun h => `(tactic| replace $h:ident := $m:ident $h:ident)
  `(tactic| ($[$rs];*; replace hx := mapM_extends $m hx; replace hy := mapM_extends $m hy; replace hext := ext_trans hext $m))

/-- **`Vals.cross`'s checks and gathers, from the kernel answers of `crossB`**: `kscan .div`/`.mod` of the positions by the
constant column `colConst T m` answer the columns `crossIx` writes (`colMap_const_eq`), so the gathers are `Vals.cross`'s. -/
theorem cross_kernels {A B : Obj} {nv mv Tv : USize} {x : Vals A nv} {y : Vals B mv} {x' : Vals A Tv} {y' : Vals B Tv}
    {k d r : Enc} {f1 f2 : Option UInt64} (h : Vals.cross x y = .ok ⟨Tv, x', y'⟩)
    (hk : colConst Tv mv.toUInt64 = .ok k)
    (hd : kscan .div false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (d, f1))
    (hr : kscan .mod false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (r, f2)) :
    nv.toNat * mv.toNat ≤ crossMax ∧ Tv.toNat = nv.toNat * mv.toNat ∧ Tv = nv * mv ∧
      nv.toNat * mv.toNat + mv.toNat < 2 ^ 63 ∧ ValsB.gather Tv d x = .ok x' ∧ ValsB.gather Tv r y = .ok y' := by
  simp only [Vals.cross, expandNote, bind, Except.bind, pure, Except.pure] at h
  by_cases hb : crossMax < nv.toNat * mv.toNat
  · simp [hb, throw, throwThe, MonadExceptOf.throw, Except.bind, Bind.bind] at h
  simp only [hb, if_false] at h
  rcases hix : crossIx nv mv with _ | ⟨T0, iR, iS⟩
  · simp [hix, Except.bind, Bind.bind] at h
  rcases hgx : ValsB.gather T0 iR x with _ | gx
  · simp [hix, hgx, Except.bind, Bind.bind] at h
  rcases hgy : ValsB.gather T0 iS y with _ | gy
  · simp [hix, hgx, hgy, Except.bind, Bind.bind, Pure.pure, Except.pure] at h
  simp [hix, hgx, hgy, Except.bind, Bind.bind, Pure.pure, Except.pure] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hT, -⟩ := crossIx_ok hix
  have hb2 : ¬(2 ^ 63 ≤ nv.toNat * mv.toNat + mv.toNat ∨ USize.size ≤ nv.toNat * mv.toNat) := fun hc => by
    unfold crossIx at hix; simp [hc, Except.bind, Bind.bind, throw, throwThe, MonadExceptOf.throw] at hix
  have hI : T0 = nv * mv ∧ colMap .first T0 .pos .pos .i64 .i64 [] [(.rdiv, mv.toUInt64)] = .ok iR ∧
      colMap .first T0 .pos .pos .i64 .i64 [] [(.rmod, mv.toUInt64)] = .ok iS := by
    unfold crossIx at hix
    simp only [hb2, if_false, Except.bind, Bind.bind, Pure.pure, Except.pure] at hix
    split at hix
    · cases hix
    rename_i e1 h1
    split at hix
    · cases hix
    rename_i e2 h2
    simp only [Except.ok.injEq, Prod.mk.injEq] at hix
    obtain ⟨rfl, rfl, rfl⟩ := hix
    have h3 : (nv.toNat * mv.toNat).toUSize = nv * mv := by simp
    exact ⟨h3.symm, h1, h2⟩
  obtain ⟨hT0, h1, h2⟩ := hI
  subst hT0
  have hdi : d = iR := colMap_const_eq (op := .div) (op' := .rdiv) hk (by simp [colMap, hd, Except.bind, Bind.bind, Pure.pure, Except.pure]) h1
    (fun w v h => by revert h; simp only [Kernel.Op.eval]; split <;> simp_all)
  have hri : r = iS := colMap_const_eq (op := .mod) (op' := .rmod) hk (by simp [colMap, hr, Except.bind, Bind.bind, Pure.pure, Except.pure]) h2
    (fun w v h => by revert h; simp only [Kernel.Op.eval]; split <;> simp_all)
  subst hdi hri
  exact ⟨by omega, hT, rfl, by omega, hgx, hgy⟩
/-- `crossMax` fits a `USize` of either width. -/
theorem crossMax_usize : crossMax.toUSize.toNat = crossMax := by
  have h := USize.size_eq
  unfold crossMax
  rcases h with h | h <;> simp [Nat.toUSize, USize.toNat_ofNat, h]

/-- `crossB` builds the kernel chain of `Vals.cross`. -/
theorem crossB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {nr mr : Nat} {nv mv Tv : USize} {A B : Obj}
    {xs ys : Cols} {x : ValsB false A nv} {y : ValsB false B mv} {x' : ValsB false A Tv} {y' : ValsB false B Tv}
    {k d r : Enc} {f1 f2 : Option UInt64} {kk : Nat × Cols × Cols → Bld (Array Nat)} {out : Array Val}
    (hn : rs[nr]? = some (.size nv)) (hm : rs[mr]? = some (.size mv))
    (hle : nv.toNat * mv.toNat ≤ crossMax) (hTn : Tv.toNat = nv.toNat * mv.toNat) (hT : Tv = nv * mv)
    (hlt : nv.toNat * mv.toNat + mv.toNat < 2 ^ 63) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63)
    (hcm : crossMax.toUSize.toNat = crossMax)
    (hk : colConst Tv mv.toUInt64 = .ok k)
    (hd : kscan .div false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (d, f1))
    (hr : kscan .mod false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (r, f2))
    (hgx : ValsB.gather Tv d x = .ok x') (hgy : ValsB.gather Tv r y = .ok y')
    (hxs : ColsOf A xs) (hys : ColsOf B ys)
    (hx : (Cols.regs xs).mapM (fun i => rs[i]?) = some x.regVals)
    (hy : (Cols.regs ys).mapM (fun i => rs[i]?) = some y.regVals) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (T : Nat) (xs' ys' : Cols) (R : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape xs' = Cols.shape xs → Cols.shape ys' = Cols.shape ys →
      Extends rs R → (T :: (Cols.regs xs' ++ Cols.regs ys')).mapM (fun i => R[i]?) =
        some (.size Tv :: (x'.regVals ++ y'.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk (T, xs', ys')) R out) :
    ∃ fg', Builds abiOf fg fg' (crossB nr mr xs ys >>= kk) rs out := by
  subst hT
  have hext : ∀ (i : Nat) (v : Val), rs[i]? = some v → rs[i]? = some v := fun _ _ h => h
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  unfold crossB
  simp only [discard_eq, bind_assoc, pure_bind]
  refine litE fun c0 R0 h0 m0 => ?_
  upx m0 [hn hm]
  refine call1E (v := .bit (decide (mv = 0))) (by abiK) rfl
    (reads_of (l := [mr, c0]) (vs := [.size mv, .size 0]) (by simp [h0, hm])) (by simp [arg, hsz, Out.out]; rfl) rfl
    fun e R1 he m1 => ?_
  upx m1 [hn hm h0]
  have hpast : (if decide (mv = 0) then #[Val.bit false] else #[Val.bit (decide (crossMax.toUSize / mv < nv))]) =
      #[Val.bit false] := by
    by_cases h0 : mv = 0
    · simp [h0]
    · have hmpos : 0 < mv.toNat := Nat.pos_of_ne_zero fun h => h0 (USize.toNat_inj.mp (by simpa using h))
      have : ¬ crossMax.toUSize / mv < nv := by
        rw [USize.lt_iff_toNat_lt, USize.toNat_div, hcm]
        exact Nat.not_lt.mpr ((Nat.le_div_iff_mul_le hmpos).mpr hle)
      simp [h0, this]
  refine Builds.bindFG (fg1 := fg) (Free.ite _ _ _) (Builds.ite (bt := decide (mv = 0)) (ot := #[.bit false])
    (oe := #[.bit (decide (crossMax.toUSize / mv < nv))]) (by simpa using he)
    (Builds.litG fun r R hr _ => Builds.pure fun _ => reads_of (l := [r]) (vs := [.bit false]) (by simp [hr])) ?_ rfl)
    ?_
  · refine Builds.litG fun cl R2 hl m2 => Builds.call1G (v := .size (crossMax.toUSize / mv)) (by abiK) rfl
      (reads_of (l := [cl, mr]) (vs := [.size crossMax.toUSize, .size mv]) (by simp [hl, m2 hm])) ?_ rfl
      fun dv R3 hdv m3 => Builds.call1G (v := .bit (decide (crossMax.toUSize / mv < nv))) (by abiK) rfl
      (reads_of (l := [dv, nr]) (vs := [.size (crossMax.toUSize / mv), .size nv]) (by simp [hdv, m3 (m2 hn)])) ?_ rfl
      fun b R4 hb m4 => Builds.pure fun _ => reads_of (l := [b]) (vs := [.bit (decide (crossMax.toUSize / mv < nv))])
        (by simp [hb])
    · simp [arg, hsz, Out.out]; rfl
    · simp [arg, hsz, Out.out]; rfl
  intro a R2 ha m2
  rw [hpast] at ha
  obtain ⟨p, hp0, hpR⟩ := holds_at ha (i := 0) rfl
  rw [nth_of (by simpa using hp0), pure_bind]
  upx m2 [hn hm]
  refine Builds.bindFG (fg1 := fg) (o := #[]) (Free.ite _ _ _) (Builds.ite_false (fg1 := fg) hpR
    (by with_unfolding_all rfl) (Builds.pure fun _ => reads_of (l := []) (vs := []) rfl) rfl ⟨⟨#[], by simp⟩, GExt.refl _⟩) ?_
  intro a3 R3 ha3 m3
  upx m3 [hn hm]
  refine call1E (v := .size (nv * mv)) (by abiK) rfl (reads_of (l := [nr, mr]) (vs := [.size nv, .size mv])
    (by simp [hn, hm])) (by simp [arg, hsz, Out.out]; rfl) rfl fun T R4 hT4 m4 => ?_
  upx m4 [hn hm]
  refine litE fun c1 R5 h1 m5 => ?_
  upx m5 [hn hm hT4]
  refine call1E (v := .size (2 ^ 63 - nv * mv)) (by abiK) rfl (reads_of (l := [c1, T]) (vs := [.size (2 ^ 63), .size (nv * mv)])
    (by simp [h1, hT4])) (by simp [arg, hsz, Out.out]; rfl) rfl fun s R6 hs6 m6 => ?_
  upx m6 [hn hm hT4]
  refine call1E (v := .bit (decide (mv < 2 ^ 63 - nv * mv))) (by abiK) rfl (reads_of (l := [mr, s])
    (vs := [.size mv, .size (2 ^ 63 - nv * mv)]) (by simp [hm, hs6])) (by simp [arg, hsz, Out.out]; rfl) rfl
    fun g R7 hg7 m7 => ?_
  upx m7 [hn hm hT4]
  have hlt' : mv < 2 ^ 63 - nv * mv := by
    have hle63 : (nv * mv).toNat ≤ (2 ^ 63 : USize).toNat := by omega
    rw [USize.lt_iff_toNat_lt, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle63)]
    omega
  refine Builds.guardE (by simpa [hlt'] using hg7) ?_
  refine call1E (v := .u64 mv.toUInt64) (by abiK) rfl (reads_of (l := [mr]) (vs := [.size mv]) (by simp [hm]))
    (by simp [arg, hsz, Out.out]; rfl) rfl fun w R8 hw m8 => ?_
  upx m8 [hn hm hT4]
  have hk' : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) (nv * mv) mv.toUInt64 = .ok k := by
    rw [← colConst_eq]; exact hk
  refine Builds.bind1F (Free.constB _ _) (constB_builds hT4 hw hk') fun c R9 hc9 m9 => ?_
  upx m9 [hn hm hT4]
  refine Builds.bind1F Free.posB posB_builds fun pa R10 hpa m10 => ?_
  upx m10 [hn hm hT4 hc9]
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hT4 hpa (enc_get_put _) hc9 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hd) fun dr R11 hdr m11 => ?_
  upx m11 [hn hm hT4 hc9]
  refine gatherCols_builds A (x := x) (y := x') hxs hx hT4 hdr hn hgx hfo ?_
  intro fg2 xs' ys1 he1 hf1 ho1 hs1 hr1
  have mg : Extends R11 (R11 ++ ys1) := fun h => get_app h
  upx mg [hn hm hT4 hc9]
  refine Builds.bind1F Free.posB posB_builds fun pb R12 hpb m12 => ?_
  upx m12 [hn hm hT4 hc9]
  replace hr1 := mapM_extends m12 hr1
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hT4 hpb (enc_get_put _) hc9 (enc_get_put _)
    (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hr) fun rr R13 hrr m13 => ?_
  upx m13 [hn hm hT4 hc9]
  replace hr1 := mapM_extends m13 hr1
  refine gatherCols_builds B (x := y) (y := y') hys hy hT4 hrr hm hgy ho1 ?_
  intro fg3 ys' ys2 he2 hf2 ho2 hs2 hr2
  refine hkk fg3 T xs' ys' (R13 ++ ys2) (FExt.trans he1 he2) (hf1.trans hf2) ho2 hs1 hs2
    (fun h => get_app (hext _ _ h)) ?_
  rw [List.mapM_cons, List.mapM_append, get_app (hT4), mapM_get_app hr1, hr2]
  rfl

/-- **`crossB` builds `Vals.cross`**: from the answers of the three kernels it calls (`colConst`, `kscan .div`, `kscan .mod`),
    every other premise of `crossB_builds` is `Vals.cross`'s own success. -/
theorem crossB_cross_builds {fg : Array Fun × Array Fun} {rs : Array Val} {nr mr : Nat} {nv mv Tv : USize} {A B : Obj}
    {xs ys : Cols} {x : Vals A nv} {y : Vals B mv} {x' : Vals A Tv} {y' : Vals B Tv}
    {k d r : Enc} {f1 f2 : Option UInt64} {kk : Nat × Cols × Cols → Bld (Array Nat)} {out : Array Val}
    (h : Vals.cross x y = .ok ⟨Tv, x', y'⟩) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63)
    (hn : rs[nr]? = some (.size nv)) (hm : rs[mr]? = some (.size mv))
    (hk : colConst Tv mv.toUInt64 = .ok k)
    (hd : kscan .div false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (d, f1))
    (hr : kscan .mod false .i64 .i64 Tv none [(Tv, .pos), (Tv, k)] [] [] = .ok (r, f2))
    (hxs : ColsOf A xs) (hys : ColsOf B ys)
    (hx : (Cols.regs xs).mapM (fun i => rs[i]?) = some x.regVals)
    (hy : (Cols.regs ys).mapM (fun i => rs[i]?) = some y.regVals) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (T : Nat) (xs' ys' : Cols) (R : Array Val), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape xs' = Cols.shape xs → Cols.shape ys' = Cols.shape ys →
      Extends rs R → (T :: (Cols.regs xs' ++ Cols.regs ys')).mapM (fun i => R[i]?) =
        some (.size Tv :: (x'.regVals ++ y'.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk (T, xs', ys')) R out) :
    ∃ fg', Builds abiOf fg fg' (crossB nr mr xs ys >>= kk) rs out :=
  let ⟨hle, hTn, hT, hlt, hgx, hgy⟩ := cross_kernels h hk hd hr
  crossB_builds hn hm hle hTn hT hlt h63 crossMax_usize hk hd hr hgx hgy hxs hys hx hy hfo hkk

/-- **`compB` builds `Tab.compPairs`** (what `pairB` runs): the stated hypothesis of `pairB_builds`, proved apart. A table
    `L` of `a`-key and `b`-value columns in registers, `S` of `b` and `c`; `kk` continues on a table of `a` and `c`
    columns holding the answer `T`. -/
def CompSpec (a b c : Obj) : Prop := ∀ {fg : Array Fun × Array Fun} {L : Tab a b} {S : Tab b c} {T : Tab a c}
    {TL TS : TabB} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}, ColsOf a TL.key → ColsOf b TL.val →
    ColsOf b TS.key → ColsOf c TS.val →
    TL.regs.mapM (fun i => rs[i]?) = some (.size L.n :: (L.key.regVals ++ L.val.regVals)) →
    TS.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
    Tab.compPairs L S = .ok T → Ordered fg.1 →
    (∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf a U.key → ColsOf c U.val →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T.n :: (T.key.regVals ++ T.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) →
    ∃ fg', Builds abiOf fg fg' (compB TL TS >>= kk) rs out

/-- **`pairB` builds `Tab.pair`**, given `compB`'s spec: the rebracketing of the key (`repath`) keeps the registers. -/
theorem pairB_builds {A B C : Obj} (hcomp : CompSpec (.prod A B) A C) {fg : Array Fun × Array Fun} {R : Tab A B}
    {S : Tab A C} {T : Tab A (.prod B C)} {RB SB : TabB} {rs out : Array Val} {kk : TabB → Bld (Array Nat)}
    (hRk : ColsOf A RB.key) (hRv : ColsOf B RB.val) (hSk : ColsOf A SB.key) (hSv : ColsOf C SB.val)
    (hR : RB.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hS : SB.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)))
    (hp : R.pair S = .ok T) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (U : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → ColsOf A U.key → ColsOf (.prod B C) U.val →
      U.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T.n :: (T.key.regVals ++ T.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk U) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (pairB A B C RB SB >>= kk) rs out := by
  simp only [Tab.pair, Functor.map, Except.map] at hp
  split at hp
  · cases hp
  rename_i T' hT'
  cases hp
  simp only [TabB.regs] at hR hS
  obtain ⟨hn, hx⟩ := mapM_get_cons hR
  simp only [Cols.regs_append] at hx
  obtain ⟨hx1, hx2⟩ := mapM_split (ColsOf.regs_length hRk R.key) hx
  obtain ⟨k1, e1, g1, r1⟩ := repath_eq A (pre := ".1") hRk
  obtain ⟨v1, e2, g2, r2⟩ := repath_eq B (pre := ".2") hRv
  unfold pairB
  simp only [bind_assoc, e1, e2, pure_bind]
  refine hcomp (L := ⟨R.n, (R.key, R.val), R.key⟩) (TL := ⟨RB.n, k1 ++ v1, RB.key⟩) ?_ ?_ hSk hSv ?_ ?_ hT' hfo ?_
  · exact ⟨k1, v1, rfl, g1, g2⟩
  · exact hRk
  · simp only [TabB.regs, Cols.regs_append, r1, r2, List.mapM_cons, hn, List.mapM_append, hx2, hx1]
    rfl
  · exact hS
  · intro fg2 U ys he hf ho hU1 hU2 hU
    obtain ⟨c1, c2, h, h1, h2⟩ := hU1
    obtain ⟨c1', e3, g3, r3⟩ := repath_eq A (pre := "") h1
    obtain ⟨c2', e4, g4, r4⟩ := repath_eq B (pre := ".1") h2
    obtain ⟨v', e5, g5, r5⟩ := repath_eq C (pre := ".2") hU2
    have ht : U.key.take (objWidth A) = c1 := by rw [h]; simp [← ColsOf.length_eq h1]
    have hd : U.key.drop (objWidth A) = c2 := by rw [h]; simp [← ColsOf.length_eq h1]
    simp only [ht, hd, e3, e4, e5, bind_assoc, pure_bind]
    refine hkk fg2 ⟨U.n, c1', c2' ++ v'⟩ ys he hf ho g3 ⟨c2', v', rfl, g4, g5⟩ ?_
    simp only [TabB.regs, h, Cols.regs_append, r3, r4, r5] at hU ⊢
    simpa [ValsB.regVals, List.append_assoc] using hU

end Rel.Lang.Plan
