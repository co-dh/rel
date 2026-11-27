module

public import Rel.Lang.PlanSpecSelect

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `compBitsB` builds `Tab.compBits` (PLAN-THM-E12, part a)

`compBitsB R S` is `funT [R, S]` of `code2B`, two `codeB`s, `csrB`, `bitMatrixB`, a `kbitrows` call and `ofBitsB`: the
chain `Tab.compBits` binds (`Vals.code2`, `Vals.code`, `csr`, `bitMatrix`, `kbitrows`, `Tab.ofBits`). Each builder has a
`_builds` theorem stating the kernel answers it runs as premises, as in `groupsW_builds`. -/

namespace Rel.Lang.Plan

open Rel Rel.Kernel Rel.Verify

/-- **`codeB` builds `Vals.code`**: `ascSeenB`'s premises, then the `kscatter .last` of the groups through `p` (`hc`) and
    the `kgather` of `f` through `p` (`hd`); `kk` continues with registers holding `k`, `c`, `d`. -/
theorem codeB_builds {fg : Array Fun × Array Fun} {o : Bool} (A : Obj) {nv : USize} {x : ValsB o A nv}
    {cs : Cols} {L : List Nat} {rs : Array Val} {n : Nat} {ks : List (AscKey × Enc)} {vs : List Enc} {p : Enc}
    {k : Nat} {g f z c d : Enc} {r : Enc × Option UInt64} {kk : Nat × Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hcs : ColsOf A cs) (hL : regsOf cs = pure L)
    (hx : L.mapM (fun i => rs[i]?) = some x.regVals) (hn : rs[n]? = some (.size nv)) (hks : x.cols = .ok ks)
    (hN : nv.toNat ≤ 2 ^ 63) (ha : kasc nv ks = .ok (vs, p)) (hk : kseen nv ((ks.map (·.1)).zip vs) = .ok (k, g, f))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 nv (some z) [(nv, z), (nv, g)] [] [] = .ok r)
    (hc : kscatter .last nv p g nv 0 = .ok c) (hd : kgather k.toUSize f nv p = .ok d) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (a b e : Nat), (∃ x, fg2.1 = fg.1 ++ x) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → [a, b, e].mapM (fun i => R[i]?) =
        some [.size k.toUSize, Reg.put c, Reg.put d] → ∃ fg', Builds abiOf fg2 fg' (kk (a, b, e)) R out) :
    ∃ fg', Builds abiOf fg fg' (codeB n cs >>= kk) rs out := by
  unfold codeB
  simp only [bind_assoc]
  refine ascSeenB_builds A hcs hL hx hn hks hN ha hk hz hsc hfo ?_
  intro fg2 ys a b e' d' he hf ho hread
  obtain ⟨hk4, hread⟩ := mapM_get_cons hread
  obtain ⟨hg4, hread⟩ := mapM_get_cons hread
  obtain ⟨hf4, hread⟩ := mapM_get_cons hread
  obtain ⟨hp4, -⟩ := mapM_get_cons hread
  have hn4 : (rs ++ ys)[n]? = some (.size nv) := get_app hn
  dsimp only
  refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds hn4 hp4 hg4 hn4 (by rop) hc) fun cr R1 hcr hE1 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE1 hk4) (hE1 hf4) (hE1 hn4) (hE1 hp4) hd) fun dr R2 hdr hE2 => ?_
  refine hkk fg2 R2 a cr dr he (by rw [hf]; exact GExt.refl _) ho (fun h => hE2 (hE1 (get_app h))) ?_
  simp [hE2 (hE1 hk4), hE2 hcr, hdr]



/-- **`code2B` builds `Vals.code2`**: `catB`, `concatB` of the two sides `x`, `y` (counts `a`, `b`, registers `n₁`, `n₂`) into
    `Z` of `p = a + b` rows, `codeB` of `Z` (`codeB_builds`' premises), then the two `kgather`s of the numbers `c` through
    the positions (`e1`) and through `catB`'s offsets, which are `shiftCol`'s column (`TagOff`; `hsh`, `hg2`). `kk` continues
    with registers holding `k`, `e1`, `e2`, `p`, the columns of `Z`, and the register holding each number's first row. -/
theorem code2B_builds (hT : TagOff) (h63 : (2 ^ 63 : USize).toNat = 2 ^ 63) (A : Obj) {o : Bool} {a b p : USize}
    {x : ValsB o A a} {y : ValsB o A b} {Z : ValsB o A p} {xs ys : Cols} {fg : Array Fun × Array Fun} {rs : Array Val}
    {n₁ n₂ : Nat} {sh : Enc} {ks : List (AscKey × Enc)} {vs : List Enc} {pe : Enc} {k : Nat} {g f z c d e1 e2 : Enc}
    {r : Enc × Option UInt64} {kk : Nat × Nat × Nat × Nat × Cols × Nat → Bld (Array Nat)} {out : Array Val}
    (hxs : ColsOf A xs) (hys : ColsOf A ys) (hx : (Cols.regs xs).mapM (fun i => rs[i]?) = some x.regVals)
    (hy : (Cols.regs ys).mapM (fun i => rs[i]?) = some y.regVals) (h1 : rs[n₁]? = some (.size a))
    (h2 : rs[n₂]? = some (.size b)) (hlt : a.toNat + b.toNat < 2 ^ 63) (hp : catRows a b = .ok p)
    (hZ : ValsB.concat p x y = .ok Z) (hsh : shiftCol b a.toUInt64 = .ok sh) (hks : Z.cols = .ok ks)
    (ha : kasc p ks = .ok (vs, pe)) (hk : kseen p ((ks.map (·.1)).zip vs) = .ok (k, g, f))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) p 0 = .ok z)
    (hsc : kscan .max false .i64 .i64 p (some z) [(p, z), (p, g)] [] [] = .ok r)
    (hc : kscatter .last p pe g p 0 = .ok c) (hd : kgather k.toUSize f p pe = .ok d)
    (hg1 : kgather a .pos p c = .ok e1) (hg2 : kgather b sh p c = .ok e2) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (a' b' c' d' : Nat) (zs : Cols) (e' : Nat),
      (∃ x, fg2.1 = fg.1 ++ x) → GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → Cols.shape zs = Cols.shape xs →
      (Cols.regs zs).mapM (fun i => R[i]?) = some Z.regVals →
      [a', b', c', d', e'].mapM (fun i => R[i]?) =
        some [.size k.toUSize, Reg.put e1, Reg.put e2, .size p, Reg.put d] →
      ∃ fg', Builds abiOf fg2 fg' (kk (a', b', c', d', zs, e')) R out) :
    ∃ fg', Builds abiOf fg fg' (code2B n₁ n₂ xs ys >>= kk) rs out := by
  have hN : p.toNat ≤ 2 ^ 63 := by rw [catRows_ok hp]; omega
  obtain ⟨zc, oc, f0, hzc, hoc, hshift⟩ := hT a b hlt
  obtain rfl : sh = oc := Except.ok.inj (hsh.symm.trans hshift)
  unfold code2B
  simp only [bind_assoc]
  refine Builds.bind2F (Free.catB _ _) (catB_builds h1 h2 hp hzc hoc) fun r1 r2 R2 hr1 hr2 hE => ?_
  dsimp only
  refine concatB_builds hT.catOff h63 A hxs hys (mapM_extends hE hx) (mapM_extends hE hy) hr1 (hE h1) (hE h2) hZ hfo ?_
  intro fg2 zs ys' heC hfC hoC hs hr
  refine codeB_builds A (x := Z) (cs := zs) (L := Cols.regs zs) (n := r1) (ColsOf.shape A hxs hs) (regsOf_eq _) hr
    (get_app hr1) hks hN ha hk hz hsc hc hd hoC ?_
  intro fg3 R3 a' b' e' he3 hf3 ho3 hE3 hread
  obtain ⟨hk3, hread⟩ := mapM_get_cons hread
  obtain ⟨hc3, hread⟩ := mapM_get_cons hread
  obtain ⟨hd3, -⟩ := mapM_get_cons hread
  have hn3 : R3[r1]? = some (.size p) := hE3 (get_app hr1)
  have ho2 : R3[r2]? = some (Reg.put sh) := hE3 (get_app hr2)
  refine Builds.bind1F Free.posB posB_builds fun rp R4 hrp hE4 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE4 (hE3 (get_app (hE h1)))) hrp (hE4 hn3) (hE4 hc3) hg1)
    fun g1 R5 hg5 hE5 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE5 (hE4 (hE3 (get_app (hE h2))))) (hE5 (hE4 ho2))
    (hE5 (hE4 hn3)) (hE5 (hE4 hc3)) hg2) fun g2 R6 hg6 hE6 => ?_
  simp only [pure_bind]
  refine hkk fg3 R6 a' g1 g2 r1 zs e' (FExt.trans heC he3) (hfC.trans hf3) ho3 ?_ ?_ ?_ ?_
  · exact fun h => hE6 (hE5 (hE4 (hE3 (get_app (hE h)))))
  · exact hs
  · exact mapM_extends (fun h => hE6 (hE5 (hE4 (hE3 h)))) hr
  · simp [hE6 (hE5 (hE4 hk3)), hE6 (hE5 (hE4 hn3)), hE6 hg5, hg6, hE6 (hE5 (hE4 hd3))]


/-! ### One-register wrappers: `Builds.bind1F`'s shape for the emitters `Builds.litG`, `ctorBG`, `listBG`, `callKG` open

Each emitter is `Free` and its register holds one fixed value, so a continuation that is itself `∃ fg'` (a `prefixB_builds`,
a `Builds.bind1F` after it) follows it. -/

theorem Builds.litF {fg : Array Fun × Array Fun} {v : Val} {rs out : Array Val} {c : Nat → Bld (Array Nat)}
    (hk : ∀ r R, R[r]? = some v → Extends rs R → ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.lit v >>= c) rs out :=
  Builds.bind1F (Free.lit v) (Builds.litG fun r R hr _ => Builds.pure fun _ => reads_of (l := [r]) (vs := [v]) (by simp [hr]))
    hk

theorem Builds.ctorBF {fg : Array Fun × Array Fun} {tag : Nat} {objs scal : Array Nat} {os ss rs out : Array Val}
    {c : Nat → Bld (Array Nat)} (ho : objs.mapM (reg rs "ctor") = .ok os) (hs : scal.mapM (reg rs "ctor") = .ok ss)
    (hk : ∀ r R, R[r]? = some (.ctor tag os ss) → Extends rs R → ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.ctorB tag objs scal >>= c) rs out :=
  Builds.bind1F (Free.ctorB tag objs scal) (Builds.ctorBG ho hs fun r R hr _ => Builds.pure fun _ =>
    reads_of (l := [r]) (vs := [.ctor tag os ss]) (by simp [hr])) hk

theorem Builds.listBF {fg : Array Fun × Array Fun} {rs out : Array Val} {l : List Nat} {vs : List Val}
    {c : Nat → Bld (Array Nat)} (h : l.mapM (fun x => rs[x]?) = some vs)
    (hk : ∀ r R, R[r]? = some (vs.foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])) → Extends rs R →
      ∃ fg', Builds abiOf fg fg' (c r) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.listB l >>= c) rs out :=
  Builds.bind1F (Free.listB l) (Builds.listBG h fun r R hr _ => Builds.pure fun _ =>
    reads_of (l := [r]) (vs := [vs.foldr (fun v c => .ctor 1 #[v, c] #[]) (.ctor 0 #[] #[])]) (by simp [hr])) hk

theorem Builds.callKF {fg : Array Fun × Array Fun} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {as : Array Nat} {vs o rs out : Array Val} {c : Array Nat → Bld (Array Nat)} (hk : abiOf k.sym = some k)
    (hf : k.run = .inl f) (ha : as.mapM (reg rs k.sym) = .ok vs) (ho : f vs = .ok o) (hs : o.size = k.res.size)
    (hc : ∀ a R, a.toList.mapM (fun x => R[x]?) = some o.toList → Extends rs R →
      ∃ fg', Builds abiOf fg fg' (c a) R out) :
    ∃ fg', Builds abiOf fg fg' (Plan.callK k as >>= c) rs out := by
  refine Builds.bindF (Free.callK k as) ?_ fun a xs h => hc a (rs ++ xs) (holds_of_reg (h "")) fun h => get_app h
  rw [← bind_pure (Plan.callK k as)]
  exact Builds.callK hk hf ha ho hs (Builds.pure (mapM_reg_range _ _))

/-- **`csrB` builds `csr`**: `n` holds the row count `nv`, `g` the group count `gv`, `gid` and `x` the columns `gidc`,
    `xc`. The kernel answers are the premises: the ones (`hone`), their `kscatter .add` by `gidc` (`hsc`), the
    `colPrefix .add` of that (`hP`), `kasc` of `gidc` (`ha`) and the `kgather` of `xc` through its permutation (`hy`);
    `kk` continues with registers holding the group ends `P` and `x` in group order `y`. -/
theorem csrB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n g gid x : Nat} {nv gv : USize}
    {gidc xc one sc P y p : Enc} {vs : List Enc} {kk : Nat × Nat → Bld (Array Nat)} {out : Array Val}
    (hn : rs[n]? = some (.size nv)) (hg : rs[g]? = some (.size gv)) (hgid : rs[gid]? = some (Reg.put gidc))
    (hx : rs[x]? = some (Reg.put xc))
    (hone : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 1 = .ok one)
    (hsc : kscatter .add nv gidc one gv 0 = .ok sc) (hP : colPrefix .add gv sc = .ok P)
    (ha : kasc nv [(.atom .i64, gidc)] = .ok (vs, p)) (hy : kgather nv p nv xc = .ok y) (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (a b : Nat), (∃ e, fg2.1 = fg.1 ++ e) →
      GExt fg.2 fg2.2 → Ordered fg2.1 → Extends rs R → [a, b].mapM (fun i => R[i]?) = some [Reg.put P, Reg.put y] →
      ∃ fg', Builds abiOf fg2 fg' (kk (a, b)) R out) :
    ∃ fg', Builds abiOf fg fg' (csrB n g gid x >>= kk) rs out := by
  obtain ⟨z, r, hz, hk, hr1⟩ := colPrefix_kscan hP
  unfold csrB
  simp only [bind_assoc, pure_bind]
  refine Builds.bind1F (Free.wordsB _ _) (wordsB_builds hn hone) fun w R1 hw hE1 => ?_
  refine Builds.bind1F (Free.scatterB _ _ _ _ _ _) (scatterB_builds (hE1 hn) (hE1 hgid) hw (hE1 hg) (by rop) hsc)
    fun s R2 hs hE2 => ?_
  refine prefixB_builds (nv := gv) (av := sc) (z := z) (r := r) (by rop) (hE2 (hE1 hg)) hs hz hk ?_ hfo ?_
  · exact fun h => kscan_last_isSome (w := 8) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (Or.inl (by with_unfolding_all rfl)) hk h
  intro fg2 q l ys he hf ho hq hl
  rw [hr1] at hq
  simp only [keyB, keysB, bind_assoc, pure_bind]
  have E2 : Extends rs (R2 ++ ys) := fun h => get_app (hE2 (hE1 h))
  have hsz : ∀ x : USize, (Reg.get? (Val.size x) : Option USize) = some x := fun _ => rfl
  refine Builds.litF fun c0 R3 h0 m3 => ?_
  refine Builds.ctorBF (reads_of (l := []) (vs := []) rfl) (reads_of (l := [c0]) (vs := [Reg.put QAtomicType.i64])
    (by simp [h0])) fun k R4 hk4 m4 => ?_
  refine Builds.ctorBF (reads_of (l := [k, gid]) (vs := [.ctor 0 #[] #[Reg.put QAtomicType.i64], Reg.put gidc])
    (by simp [hk4, m4 (m3 (E2 hgid))])) (reads_of (l := []) (vs := []) rfl) fun e R5 he5 m5 => ?_
  refine Builds.listBF (l := [e]) (vs := [Val.ctor 0 #[.ctor 0 #[] #[Reg.put QAtomicType.i64], Reg.put gidc] #[]])
    (by simp [he5]) fun lr R6 hl6 m6 => ?_
  have hread : (Reg.get? (([Val.ctor 0 #[.ctor 0 #[] #[Reg.put QAtomicType.i64], Reg.put gidc] #[]]).foldr
      (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[])) : Option (List (AscKey × Enc))) =
      some [(.atom .i64, gidc)] :=
    (listGet?_foldr _).trans ((pairs_get [(.ctor 0 #[] #[Reg.put QAtomicType.i64], Reg.put gidc)]).trans
      (by simp [ascGet?_atom, enc_get_put]))
  generalize ([Val.ctor 0 #[.ctor 0 #[] #[Reg.put QAtomicType.i64], Reg.put gidc] #[]]).foldr
    (fun v c => Val.ctor 1 #[v, c] #[]) (Val.ctor 0 #[] #[]) = F at hl6 hread
  refine Builds.callKF (o := #[Reg.put vs, Reg.put p]) (by abiK) rfl
    (reads_of (l := [n, lr]) (vs := [.size nv, F]) (by simp [hl6, m6 (m5 (m4 (m3 (E2 hn))))])) ?_ rfl
    fun sp R7 hsp m7 => ?_
  · simp [arg, hsz, hread, ha, Out.out]; rfl
  obtain ⟨p1, hp1, hpR1⟩ := holds_at hsp (i := 1) rfl
  rw [nth_of (by simpa using hp1), pure_bind]
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (m7 (m6 (m5 (m4 (m3 (E2 hn)))))) hpR1
    (m7 (m6 (m5 (m4 (m3 (E2 hn)))))) (m7 (m6 (m5 (m4 (m3 (E2 hx)))))) hy) fun gr R8 hg8 hE8 => ?_
  refine hkk fg2 R8 q gr he hf ho (fun h => hE8 (m7 (m6 (m5 (m4 (m3 (E2 h))))))) ?_
  simp [hE8 (m7 (m6 (m5 (m4 (m3 hq))))), hg8]

/-- **`bitMatrixB` builds `bitMatrix`'s kernel chain**: `constB` of the word `w` (`hwc`), `kscan .mul` of `r` against it
    (`hm`), `kscan .add` of that against `c` (`ha`), the ones (`hone`) `kscatter`ed to `na · w` bits (`hsc`). `bitMatrix`
    reads the product as `colMap .first r r` with the post step `(.mul, w)`: the two answers are one column (`hmul`, the
    one place the plan and its model part ways, as `WhereAgree`). -/
theorem bitMatrixB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {n na w r c : Nat} {nv av wv : USize}
    {rc cc wcol mc ac one m : Enc} {f1 f2 : Option UInt64}
    (hn : rs[n]? = some (.size nv)) (hna : rs[na]? = some (.size av)) (hw : rs[w]? = some (.size wv))
    (hr : rs[r]? = some (Reg.put rc)) (hc : rs[c]? = some (Reg.put cc))
    (hwc : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv wv.toUInt64 = .ok wcol)
    (hm : kscan .mul false .i64 .i64 nv none [(nv, rc), (nv, wcol)] [] [] = .ok (mc, f1))
    (ha : kscan .add false .i64 .i64 nv none [(nv, mc), (nv, cc)] [] [] = .ok (ac, f2))
    (hone : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) nv 1 = .ok one)
    (hsc : kscatter .last nv ac one (av * wv) 0 = .ok m) :
    Builds abiOf fg fg (do let x ← bitMatrixB n na w r c; Pure.pure #[x]) rs #[Reg.put m] := by
  unfold bitMatrixB
  simp only [bind_assoc, show wordOf = u64B from rfl]
  refine Builds.bind1G (u64B_builds hw) fun wr R1 hwr hE1 => ?_
  refine Builds.bind1G (constB_builds (hE1 hn) hwr hwc) fun wcr R2 hwcr hE2 => ?_
  refine Builds.bind1G (mapB_builds (hE2 (hE1 hn)) (hE2 (hE1 hr)) (enc_get_put _) hwcr
    (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hm) fun mr R3 hmr hE3 => ?_
  refine Builds.bind1G (mapB_builds (hE3 (hE2 (hE1 hn))) hmr (enc_get_put _)
    (hE3 (hE2 (hE1 hc))) (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) ha)
    fun ar R4 har hE4 => ?_
  refine Builds.bind1G (wordsB_builds (hE4 (hE3 (hE2 (hE1 hn)))) hone) fun on R5 hon hE5 => ?_
  refine Builds.call1G (vs := #[.size av, .size wv]) (v := .size (av * wv)) (by abiK) (by rop) ?_ ?_ rfl
    fun cr R6 hcr hE6 => ?_
  · rw [List.mapM_toArray]
    simp [reg, hE5 (hE4 (hE3 (hE2 (hE1 hna)))), hE5 (hE4 (hE3 (hE2 (hE1 hw))))]
    rfl
  · simp [arg]
    rfl
  refine Builds.bind1G (scatterB_builds (hE6 (hE5 (hE4 (hE3 (hE2 (hE1 hn)))))) (hE6 (hE5 har)) (hE6 hon) hcr
    (by rop) hsc) fun x R7 hx hE7 => ?_
  exact Builds.pure fun who => by simp [reg, hx]; rfl

/-- `call1 USize.mul` of two size registers holds their product. -/
theorem mulB_builds {fg : Array Fun × Array Fun} {rs : Array Val} {a b : Nat} {av bv : USize}
    (ha : rs[a]? = some (.size av)) (hb : rs[b]? = some (.size bv)) :
    Builds abiOf fg fg (do let r ← call1 (kernel% USize.mul) #[a, b]; Pure.pure #[r]) rs #[.size (av * bv)] := by
  refine Builds.call1G (vs := #[.size av, .size bv]) (v := .size (av * bv)) (by abiK) (by rop) ?_ ?_ rfl
    fun r R hr m => Builds.pure fun who => by simp [reg, hr]; rfl
  · rw [List.mapM_toArray]
    simp [reg, ha, hb]
    rfl
  · simp [arg]
    rfl

/-- **`ofBitsB` builds `Tab.ofBits`' kernel chain**: `whereB` of the `g · w` bits `o` (`WhereAgree`: `whereCol` and `whereB`'s
    calls answer the count `M` and the positions `sel`), the positions' quotient and remainder by `w` (`hdiv`, `hmod`, the
    `kscan .div`, `.mod` of `sel` against the constant column `hwc`), each `kgather`ed through `ra`, `rc` (`hix`, `hiy`) and
    read through the two sides (`hgx`, `hgy`); `kk` continues with a table of the shape of `x`, `y` holding them. -/
theorem ofBitsB_builds (A C : Obj) {o' p' : Bool} {gv wv Mv nxv nyv : USize} {X : ValsB o' A nxv} {Y : ValsB p' C nyv}
    {X' : ValsB o' A Mv} {Y' : ValsB p' C Mv} {xs ys : Cols} {fg : Array Fun × Array Fun} {rs : Array Val}
    {g w o nx ra ny rc : Nat} {oc sel rac rcc wcol dc mc ixc iyc : Enc} {f1 f2 : Option UInt64}
    {kk : TabB → Bld (Array Nat)} {out : Array Val}
    (hxs : ColsOf A xs) (hys : ColsOf C ys) (hx : (Cols.regs xs).mapM (fun i => rs[i]?) = some X.regVals)
    (hy : (Cols.regs ys).mapM (fun i => rs[i]?) = some Y.regVals) (hg : rs[g]? = some (.size gv))
    (hw : rs[w]? = some (.size wv)) (ho : rs[o]? = some (Reg.put oc)) (hnx : rs[nx]? = some (.size nxv))
    (hra : rs[ra]? = some (Reg.put rac)) (hny : rs[ny]? = some (.size nyv)) (hrc : rs[rc]? = some (Reg.put rcc))
    (hW : WhereAgree (gv * wv) Mv oc sel)
    (hwc : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) Mv wv.toUInt64 = .ok wcol)
    (hdiv : kscan .div false .i64 .i64 Mv none [(Mv, sel), (Mv, wcol)] [] [] = .ok (dc, f1))
    (hmod : kscan .mod false .i64 .i64 Mv none [(Mv, sel), (Mv, wcol)] [] [] = .ok (mc, f2))
    (hix : kgather Mv dc gv rac = .ok ixc) (hiy : kgather Mv mc wv rcc = .ok iyc)
    (hgx : ValsB.gather Mv ixc X = .ok X') (hgy : ValsB.gather Mv iyc Y = .ok Y') (hfo : Ordered fg.1)
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (R : Array Val) (W : TabB), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Extends rs R → Cols.shape W.key = Cols.shape xs → Cols.shape W.val = Cols.shape ys →
      W.regs.mapM (fun i => R[i]?) = some (.size Mv :: (X'.regVals ++ Y'.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) R out) :
    ∃ fg', Builds abiOf fg fg' (ofBitsB g w o nx xs ra ny ys rc >>= kk) rs out := by
  obtain ⟨zc2, pc, ixc0, ix1c, zrc, onec, cutc, fo, ixf, cutf, f0, hz2, hp2, hf2, hK2, hix2, hs2, hzr, hone2, hcut, hg2,
    hrt⟩ := hW
  unfold ofBitsB
  simp only [bind_assoc, show wordOf = u64B from rfl]
  refine Builds.bind1F (Free.call1 _ _) (mulB_builds hg hw) fun gw R1 hgw hE1 => ?_
  refine Builds.bind2F (Free.whereB _ _) (whereB_builds hgw (by simp [hE1 ho, enc_get_put]) hz2 hp2 hf2 hK2 hix2
    hs2 hzr hone2 hcut hg2 hrt) fun kr sr R2 hk2 hsr2 hE2 => ?_
  dsimp only
  refine Builds.bind1F (Free.call1 _ _) (u64B_builds (hE2 (hE1 hw))) fun wr R3 hwr hE3 => ?_
  refine Builds.bind1F (Free.constB _ _) (constB_builds (hE3 hk2) hwr hwc) fun wcr R4 hwcr hE4 => ?_
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds (hE4 (hE3 hk2)) (hE4 (hE3 hsr2)) (enc_get_put _) hwcr
    (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hdiv) fun dr R5 hdr hE5 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE5 (hE4 (hE3 hk2))) hdr
    (hE5 (hE4 (hE3 (hE2 (hE1 hg))))) (hE5 (hE4 (hE3 (hE2 (hE1 hra))))) hix) fun ir R6 hir hE6 => ?_

  have h6 : Extends rs R6 := fun h => hE6 (hE5 (hE4 (hE3 (hE2 (hE1 h)))))
  have hm6 : R6[kr]? = some (.size Mv) := hE6 (hE5 (hE4 (hE3 hk2)))
  refine Builds.bind1F (Free.mapB _ _ _ _ _ _ _ _) (mapB_builds hm6 (hE6 (hE5 (hE4 (hE3 hsr2)))) (enc_get_put _)
    (hE6 (hE5 hwcr)) (enc_get_put _) (by rop) (qtype_get_put _) (qtype_get_put _) (by rop) (by rop) hmod)
    fun mr R7 hmr hE7 => ?_
  refine Builds.bind1F (Free.gatherB _ _ _ _) (gatherB_builds1 (hE7 hm6) hmr (hE7 (h6 hw)) (hE7 (h6 hrc)) hiy)
    fun jr R8 hjr hE8 => ?_
  have h8 : Extends rs R8 := fun h => hE8 (hE7 (h6 h))
  have hm8 : R8[kr]? = some (.size Mv) := hE8 (hE7 hm6)
  refine gatherCols_builds A (x := X) (y := X') hxs (mapM_extends h8 hx) hm8 (hE8 (hE7 hir)) (h8 hnx) hgx hfo ?_
  intro fg3 ks' ys3 he3 hf3 ho3 hs3 hr3
  refine gatherCols_builds C (x := Y) (y := Y') hys (mapM_get_app (mapM_extends h8 hy)) (get_app hm8) (get_app hjr)
    (get_app (h8 hny)) hgy ho3 ?_
  intro fg4 vs' ys4 he4 hf4 ho4 hs4 hr4
  simp only [pure_bind]
  refine hkk fg4 ((R8 ++ ys3) ++ ys4) ⟨kr, ks', vs'⟩ (FExt.trans he3 he4) (hf3.trans hf4) ho4
    (fun h => get_app (get_app (h8 h))) hs3 hs4 ?_
  simp only [TabB.regs, Cols.regs_append]
  refine omapM_cons.mpr ⟨_, _, get_app (get_app hm8), ?_, rfl⟩
  rw [List.mapM_append, mapM_get_app hr3, hr4]
  rfl



/-! ### `compBitsB`'s plan function: its body, and that it grows -/

/-- The body of `compBitsB`'s plan function (`funT [R, S]`). -/
def compBitsBody (R S : TabB) : Bld TabB := do
  let (kb, bR, bS, _) ← code2B R.n S.n R.val S.key
  let (ka, aR, ra) ← codeB R.n R.key
  let (kc, cS, rc) ← codeB S.n S.val
  let (ends, idx) ← csrB R.n ka aR bR
  let m ← bitMatrixB S.n kb kc bS cS
  let o ← nth (← callK (kernel% Rel.Kernel.kbitrows) #[← lit (.bit false), kc, kb, R.n, ka, ends, idx, m]) 0 "kbitrows"
  ofBitsB ka kc o R.n R.key ra S.n S.val rc

theorem compBitsB_eq (R S : TabB) :
    compBitsB R S = funT [R, S] (fun | [R, S] => compBitsBody R S | _ => throw "compBits: not two tables") := rfl

theorem Grows.codeB (n : Nat) (cs : Cols) : Grows (Plan.codeB n cs) := by
  unfold Plan.codeB
  refine (Grows.ascSeenB _ _).bind fun q => ?_
  obtain ⟨k, g, f, p⟩ := q
  exact (Grows.scatterB _ _ _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.code2B (n₁ n₂ : Nat) (xs ys : Cols) : Grows (Plan.code2B n₁ n₂ xs ys) := by
  unfold Plan.code2B
  refine (Grows.catB _ _).bind fun q => ?_
  obtain ⟨N, off⟩ := q
  refine (Grows.concatB (Col.sizes xs + 1) _ _ _ _ _ _ (Nat.lt_succ_self _)).bind fun _ => (Grows.codeB _ _).bind fun q => ?_
  obtain ⟨k, c, rep⟩ := q
  exact Grows.posB.bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.csrB (n g gid x : Nat) : Grows (Plan.csrB n g gid x) := by
  simp only [Plan.csrB, Plan.keyB, Plan.keysB, bind_assoc, pure_bind]
  exact (Grows.wordsB _ _).bind fun _ => (Grows.scatterB _ _ _ _ _ _).bind fun _ => (Grows.prefixB _ _ _).bind fun _ =>
    (Grows.lit _).bind fun _ => (Grows.ctorB _ _ _).bind fun _ => (Grows.ctorB _ _ _).bind fun _ =>
    (Grows.listB _).bind fun _ => (Grows.callK _ _).bind fun _ => (Grows.nth _ _ _).bind fun _ =>
    (Grows.gatherB _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.bitMatrixB (n na w r c : Nat) : Grows (Plan.bitMatrixB n na w r c) := by
  unfold Plan.bitMatrixB
  exact (Grows.u64B _).bind fun _ => (Grows.constB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
    (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.wordsB _ _).bind fun _ => (Grows.call1 _ _).bind fun _ =>
    Grows.scatterB _ _ _ _ _ _

theorem Grows.ofBitsB (g w o nx : Nat) (x : Cols) (ra ny : Nat) (y : Cols) (rc : Nat) :
    Grows (Plan.ofBitsB g w o nx x ra ny y rc) := by
  unfold Plan.ofBitsB
  refine (Grows.call1 _ _).bind fun _ => (Grows.whereB _ _).bind fun q => ?_
  obtain ⟨M, sel⟩ := q
  exact (Grows.u64B _).bind fun _ => (Grows.constB _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ =>
    (Grows.gatherB _ _ _ _).bind fun _ => (Grows.mapB _ _ _ _ _ _ _ _).bind fun _ => (Grows.gatherB _ _ _ _).bind fun _ =>
    (Grows.gatherCols _ _ _ _).bind fun _ => (Grows.gatherCols _ _ _ _).bind fun _ => Grows.pure _

theorem Grows.compBitsBody (R S : TabB) : Grows (Plan.compBitsBody R S) := by
  unfold Plan.compBitsBody
  refine (Grows.code2B _ _ _ _).bind fun q => ?_
  obtain ⟨kb, bR, bS, q4⟩ := q
  refine (Grows.codeB _ _).bind fun q => ?_
  obtain ⟨ka, aR, ra⟩ := q
  refine (Grows.codeB _ _).bind fun q => ?_
  obtain ⟨kc, cS, rc⟩ := q
  refine (Grows.csrB _ _ _ _).bind fun q => ?_
  obtain ⟨ends, idx⟩ := q
  exact (Grows.bitMatrixB _ _ _ _ _).bind fun _ => (Grows.lit _).bind fun _ => (Grows.callK _ _).bind fun _ =>
    (Grows.nth _ _ _).bind fun _ => Grows.ofBitsB _ _ _ _ _ _ _ _ _


theorem Typed.codeB {m n : Nat} (cs : Cols) (hn : m ≤ n) (hcs : AllGe m (Cols.regs cs)) :
    Typed m (fun r : Nat × Nat × Nat => m ≤ r.1 ∧ m ≤ r.2.1 ∧ m ≤ r.2.2) (Plan.codeB n cs) := by
  unfold Plan.codeB
  refine (Typed.ascSeenB cs hn hcs).bind fun q hq => ?_
  obtain ⟨k, g, f, p⟩ := q
  obtain ⟨hk, hg, hf, hp⟩ := hq
  dsimp only at hk hg hf hp ⊢
  exact Typed.scatterB.bind fun c hc => Typed.gatherB.bind fun d hd => Typed.pure ⟨hk, hc, hd⟩

theorem Typed.code2B {m n₁ n₂ : Nat} (xs ys : Cols) (h1 : m ≤ n₁) (h2 : m ≤ n₂) (hxs : AllGe m (Cols.regs xs))
    (hys : AllGe m (Cols.regs ys)) :
    Typed m (fun r : Nat × Nat × Nat × Nat × Cols × Nat => m ≤ r.1 ∧ m ≤ r.2.1 ∧ m ≤ r.2.2.1 ∧ m ≤ r.2.2.2.1 ∧
      AllGe m (Cols.regs r.2.2.2.2.1) ∧ m ≤ r.2.2.2.2.2) (Plan.code2B n₁ n₂ xs ys) := by
  unfold Plan.code2B
  refine (Typed.catB h1 h2).bind fun p hp => ?_
  obtain ⟨N, off⟩ := p
  obtain ⟨hN, hoff⟩ := hp
  dsimp only at hN hoff ⊢
  refine ((Typed.concatBOf (S := []) (Col.sizes xs + 1) N n₁ n₂ off xs ys (Nat.lt_succ_self _) (.inl hN) h1 h2 hxs
    hys).mono fun r h a ha => (h a ha).resolve_right (by simp)).bind fun z hz => ?_
  refine (Typed.codeB z hN hz).bind fun q hq => ?_
  obtain ⟨k, c, rep⟩ := q
  obtain ⟨hk, hc, hrep⟩ := hq
  dsimp only at hk hc hrep ⊢
  exact Typed.posB.bind fun pa hpa => Typed.gatherB.bind fun e1 he1 => Typed.gatherB.bind fun e2 he2 =>
    Typed.pure ⟨hk, he1, he2, hN, hz, hrep⟩

theorem Typed.csrB {m n g gid x : Nat} (hn : m ≤ n) (hg : m ≤ g) (hgid : m ≤ gid) :
    Typed m (fun r : Nat × Nat => m ≤ r.1 ∧ m ≤ r.2) (Plan.csrB n g gid x) := by
  simp only [Plan.csrB, Plan.keyB, Plan.keysB, bind_assoc, pure_bind]
  refine Typed.wordsB.bind fun w hw => Typed.scatterB.bind fun s hs => (Typed.prefixB hg hs).bind fun q hq => ?_
  obtain ⟨pp, l⟩ := q
  obtain ⟨hpp, hl⟩ := hq
  dsimp only at hpp hl ⊢
  refine (Typed.lit _).bind fun c hc => (Typed.ctorB (by simp) (by simp [hc]) _).bind fun k hk => ?_
  refine (Typed.ctorB (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption) (by simp) _).bind
    fun e he => ?_
  refine (Typed.listB (by simp [AllGe, he])).bind fun lr hlr => ?_
  refine (Typed.callK (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)).bind fun sp hsp => ?_
  refine (Typed.nth hsp _ _).bind fun p1 hp1 => Typed.gatherB.bind fun gr hgr => Typed.pure ⟨hpp, hgr⟩

theorem Typed.bitMatrixB {m n na w r c : Nat} (hn : m ≤ n) (hna : m ≤ na) (hw : m ≤ w) (hr : m ≤ r) (hc : m ≤ c) :
    Typed m (fun x => m ≤ x) (Plan.bitMatrixB n na w r c) := by
  simp only [Plan.bitMatrixB, show Plan.wordOf = Plan.u64B from rfl]
  refine Typed.u64B.bind fun wr hwr => Typed.constB.bind fun wc hwc => (Typed.mapB hn hr hwc).bind fun mr hmr =>
    (Typed.mapB hn hmr hc).bind fun ar har => Typed.wordsB.bind fun on hon =>
    (Typed.call1 (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)).bind fun cr hcr =>
    Typed.scatterB

theorem Typed.ofBitsB {m g w o nx ny : Nat} {ra rc : Nat} {x y : Cols} (hg : m ≤ g) (hw : m ≤ w) (ho : m ≤ o) (hnx : m ≤ nx)
    (hny : m ≤ ny) (hx : AllGe m (Cols.regs x)) (hy : AllGe m (Cols.regs y)) :
    Typed m (fun U => AllGe m U.regs) (Plan.ofBitsB g w o nx x ra ny y rc) := by
  simp only [Plan.ofBitsB, show Plan.wordOf = Plan.u64B from rfl]
  refine (Typed.call1 (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)).bind fun gw hgw => ?_
  refine (Typed.whereB hgw ho).bind fun q hq => ?_
  obtain ⟨M, sel⟩ := q
  obtain ⟨hM, hsel⟩ := hq
  dsimp only at hM hsel ⊢
  refine Typed.u64B.bind fun wr hwr => Typed.constB.bind fun wc hwc => (Typed.mapB hM hsel hwc).bind fun dr hdr =>
    Typed.gatherB.bind fun ir hir => (Typed.mapB hM hsel hwc).bind fun mr hmr => Typed.gatherB.bind fun jr hjr =>
    (Typed.gatherCols hM nx x hnx hx).bind fun x' hx' => (Typed.gatherCols hM ny y hny hy).bind fun y' hy' =>
    Typed.pure ?_
  intro a ha
  simp only [TabB.regs, Cols.regs_append, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | ha | ha
  · exact hM
  · exact hx' a ha
  · exact hy' a ha

theorem Typed.compBitsBody {m : Nat} {R S : TabB} (hR : AllGe m R.regs) (hS : AllGe m S.regs) :
    Typed m (fun U => AllGe m U.regs) (Plan.compBitsBody R S) := by
  have hRn : m ≤ R.n := hR _ (by simp [TabB.regs])
  have hSn : m ≤ S.n := hS _ (by simp [TabB.regs])
  have hRk : AllGe m (Cols.regs R.key) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hRv : AllGe m (Cols.regs R.val) := fun a ha => hR a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSk : AllGe m (Cols.regs S.key) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  have hSv : AllGe m (Cols.regs S.val) := fun a ha => hS a (by simp [TabB.regs, Cols.regs_append, ha])
  unfold Plan.compBitsBody
  refine (Typed.code2B R.val S.key hRn hSn hRv hSk).bind fun q hq => ?_
  obtain ⟨kb, bR, bS, NB, zb, rb⟩ := q
  obtain ⟨hkb, hbR, hbS, hNB, hzb, hrb⟩ := hq
  dsimp only at hkb hbR hbS hNB hzb hrb ⊢
  refine (Typed.codeB R.key hRn hRk).bind fun q hq => ?_
  obtain ⟨ka, aR, ra⟩ := q
  obtain ⟨hka, haR, hra⟩ := hq
  dsimp only at hka haR hra ⊢
  refine (Typed.codeB S.val hSn hSv).bind fun q hq => ?_
  obtain ⟨kc, cS, rc⟩ := q
  obtain ⟨hkc, hcS, hrc⟩ := hq
  dsimp only at hkc hcS hrc ⊢
  refine (Typed.csrB hRn hka haR).bind fun q hq => ?_
  obtain ⟨ends, idx⟩ := q
  obtain ⟨hends, hidx⟩ := hq
  dsimp only at hends hidx ⊢
  refine (Typed.bitMatrixB hSn hkb hkc hbS hcS).bind fun mm hmm => (Typed.lit _).bind fun lb hlb =>
    (Typed.callK (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)).bind
    fun os hos => (Typed.nth hos _ _).bind fun o ho => Typed.ofBitsB hka hkc ho hRn hSn hRk hSv


/-! ### `funT` of a two-table body

`selectB_builds` and `compB_builds` are one proof with the body and the output shape changed: `funT [R', S']` of a body
`body R S` builds what the body builds at the two tables renamed to fresh registers (`tabsAt_two`), when the body grows
and is typed (`Grows`, `Typed`), and the answer's columns have the shape `K`, `V`. -/

theorem funT2_builds {A B C D E F : Obj} {R : Tab A B} {S : Tab C D} {T' : Tab E F} {R' S' : TabB} {K V : Cols}
    {body : TabB → TabB → Bld TabB} {nm : String} {fg : Array Fun × Array Fun} {rs : Array Val}
    {kk : TabB → Bld (Array Nat)} {out : Array Val} (hG : ∀ R S, Grows (body R S))
    (hTy : ∀ {m : Nat} {R S : TabB}, AllGe m R.regs → AllGe m S.regs → Typed m (fun U => AllGe m U.regs) (body R S))
    (hKc : ColsOf E K) (hVc : ColsOf F V)
    (hR : R'.regs.mapM (fun i => rs[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)))
    (hS : S'.regs.mapM (fun i => rs[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)))
    (hfo : Ordered fg.1)
    (hbody : ∀ {R1 S1 : TabB} {rs' : Array Val} {kk' : TabB → Bld (Array Nat)} {out' : Array Val},
      Cols.shape R1.key = Cols.shape R'.key → Cols.shape R1.val = Cols.shape R'.val →
      Cols.shape S1.key = Cols.shape S'.key → Cols.shape S1.val = Cols.shape S'.val →
      R1.regs.mapM (fun i => rs'[i]?) = some (.size R.n :: (R.key.regVals ++ R.val.regVals)) →
      S1.regs.mapM (fun i => rs'[i]?) = some (.size S.n :: (S.key.regVals ++ S.val.regVals)) →
      (∀ (fg2 : Array Fun × Array Fun) (U : TabB) (Rn : Array Val), Extends rs' Rn → (∃ e, fg2.1 = fg.1 ++ e) →
        GExt fg.2 fg2.2 → Ordered fg2.1 → Cols.shape U.key = Cols.shape K → Cols.shape U.val = Cols.shape V →
        U.regs.mapM (fun i => Rn[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
        ∃ fg', Builds abiOf fg2 fg' (kk' U) Rn out') →
      ∃ fg', Builds abiOf fg fg' (body R1 S1 >>= kk') rs' out')
    (hkk : ∀ (fg2 : Array Fun × Array Fun) (W : TabB) (ys : Array Val), (∃ e, fg2.1 = fg.1 ++ e) → GExt fg.2 fg2.2 →
      Ordered fg2.1 → Cols.shape W.key = Cols.shape K → Cols.shape W.val = Cols.shape V →
      W.regs.mapM (fun i => (rs ++ ys)[i]?) = some (.size T'.n :: (T'.key.regVals ++ T'.val.regVals)) →
      ∃ fg', Builds abiOf fg2 fg' (kk W) (rs ++ ys) out) :
    ∃ fg', Builds abiOf fg fg' (funT [R', S'] (fun | [R, S] => body R S | _ => throw nm) >>= kk) rs out := by
  have hlR := mapM_get_length hR
  have hlS := mapM_get_length hS
  obtain ⟨R1, S1, hUs, hsR1, hsR2, hsS1, hsS2, hr1, hs1⟩ := tabsAt_two R' S' rs.size
  let pv : List Val := (.size R.n :: (R.key.regVals ++ R.val.regVals)) ++ (.size S.n :: (S.key.regVals ++ S.val.regVals))
  have hpl : (R'.regs ++ S'.regs).length = pv.length := by rw [List.length_append, hlR, hlS]; simp [pv]; omega
  have hA : tabsRegs [R', S'] = Pure.pure (R'.regs ++ S'.regs) := by rw [tabsRegs_eq]; simp
  have ha : ∀ who, (R'.regs ++ S'.regs).toArray.mapM (reg rs who) = .ok pv.toArray := fun _ =>
    reads_of (by rw [List.mapM_append, hR, hS]; rfl)
  have g : (R1.regs ++ S1.regs).mapM (fun i => (rs ++ pv.toArray)[i]?) = some pv := by
    rw [hr1, hs1, List.range'_append_1, ← List.length_append, hpl]
    exact mapM_range_append rs pv
  obtain ⟨gR, gS⟩ := mapM_split (by rw [hr1, List.length_range', hlR]) g
  let P : TabB → Prop := fun W => Cols.shape W.key = Cols.shape K ∧ Cols.shape W.val = Cols.shape V
  let o : Array Val := (Val.size T'.n :: (T'.key.regVals ++ T'.val.regVals)).toArray
  have hB : ∃ fg1, Builds abiOf fg fg1 (body R1 S1 >>= answerRegs P) (rs ++ pv.toArray) o := by
    refine hbody hsR1 hsR2 hsS1 hsS2 gR gS ?_
    intro fg4 U' ys3 he4 hf4 ho4 hs4 hs5 hs6 hr4
    refine ⟨fg4, Builds.answerRegs (P := P) ⟨hs5, hs6⟩ (tabsRegs_eq _) fun _ => ?_⟩
    simpa [o] using reads_of hr4
  obtain ⟨fg1, ⟨a1, ha1⟩, hb1, hB1⟩ := hB
  have hm1 : AllGe rs.size R1.regs := fun a ha => by rw [hr1, List.mem_range'_1] at ha; omega
  have hm2 : AllGe rs.size S1.regs := fun a ha => by rw [hs1, List.mem_range'_1] at ha; omega
  have hT : Typed rs.size (fun _ => True) (body R1 S1) := (hTy hm1 hm2).mono fun _ _ => trivial
  obtain ⟨ctys, hcl⟩ := Typed.cloTys (fg := fg) (fg1 := fg1) (k := (R'.regs ++ S'.regs).length) hT
  refine funT_builds (P := P) (Us := [R1, S1]) (ctys := ctys) (o := o) hA ha hUs (hB1 #[]) hfo ?_
    (fun U body xs R rtys h _ hR hy is => hcl U body _ R rtys h hR hy is) ?_
  · intro Ts
    rcases Ts with _ | ⟨T1, _ | ⟨T2, _ | ⟨T3, Ts⟩⟩⟩ <;> try exact Grows.throw _
    exact hG T1 T2
  · intro U' ⟨hsk, hsv⟩ fg2 Rr V ys he hf ho' hRr hV
    obtain ⟨AU, YU, u1, -, -, u4⟩ := tab_spec U'
    rw [tabsRegs_eq] at u1
    obtain rfl := (pure_inj u1).symm
    have hl : Rr.toList.length = ([U'].flatMap TabB.regs).length := by
      have h1 := mapM_ok_size (hRr "")
      have k1 := ColsOf.regs_length (ColsOf.shape E hKc hsk) T'.key
      have k2 := ColsOf.regs_length (ColsOf.shape F hVc hsv) T'.val
      simp only [o, List.size_toArray, List.length_cons, List.length_append] at h1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, TabB.regs, Cols.regs_append, List.length_cons,
        List.length_append, Array.length_toList, k1, k2]
      omega
    obtain ⟨V', f1, f2, -, f4, f5⟩ := u4 Rr.toList [] (by simpa using hl)
    rw [List.append_nil] at f1
    obtain rfl : V = V' := by
      have := pure_inj (hV.symm.trans f1); simp only [Prod.mk.injEq, List.cons.injEq, and_true] at this; exact this
    rw [tabsRegs_eq] at f2
    have f2' := pure_inj f2
    have hread := holds_of_reg (hRr "")
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at f2'
    rw [← f2'] at hread
    obtain ⟨e1', he1⟩ := he
    exact hkk fg2 V ys ⟨a1 ++ e1', by rw [he1, ha1, Array.append_assoc]⟩ (by rw [hf]; exact hb1) ho'
      (f4.trans hsk) (f5.trans hsv) (by simpa [o] using hread)

end Rel.Lang.Plan
