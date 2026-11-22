import Rel.RepCols
import Rel.Run.Bits

/-! **`Tab.WF` kept by each `Tab` op** (PLAN 8.5): an op's output sides are `Vals.gather`ed, `Vals.concat`ed or
`Vals.nub`bed from its inputs' sides (`Vals.gather_wf`, `Vals.concat_wf`, `Tab.canon_wf`), or are sides of no row
(`Vals.none_wf`), so a cell of its output is a cell of an input. These are the base the switch of `Rel.Wf`'s `tab`
case to `Tab.WF` stands on: each op's `_wf` lemma there is one of these. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

set_option hygiene false in
/-- `h : x = .ok t` split through its binds and matches: each error branch closed, each other one kept. -/
local macro "okSplit" : tactic => `(tactic| repeat' (split at h <;> try (cases h; done)))

/-- A step that keeps `P` keeps it through `List.foldlM`. -/
theorem foldlM_keeps {α β : Type} {P : β → Prop} {f : β → α → Except String β}
    (hf : ∀ b a b', f b a = .ok b' → P b → P b') : ∀ (l : List α) {b b' : β}, l.foldlM f b = .ok b' → P b → P b'
  | [], _, _, h, hb => by simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hb
  | a :: l, _, _, h, hb => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc; exact foldlM_keeps hf l h (hf _ a c hc hb)

/-- **A side of no rows is `Vals.WF`**: an `arr` side of it has no cell. -/
theorem Vals.none_wf : {A : Obj} → {x : Vals A 0} → Vals.none A = .ok x → Vals.WF x
  | .atom _, _, _ => trivial
  | .prod _ _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp; split at h; · cases h
    rename_i q hq; cases h
    exact ⟨Vals.none_wf hp, Vals.none_wf hq⟩
  | .arr _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i f hf; cases h
    exact ⟨fun i => absurd i.2 (by simp), Vals.none_wf hf⟩
  | .sum _ _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i p hp; split at h; · cases h
    rename_i q hq; cases h
    exact ⟨Vals.none_wf hp, Vals.none_wf hq⟩

namespace Tab
variable {A B C D I : Obj}

/-- **`𝟘` is `Tab.WF`**: both sides `Vals.none`. -/
theorem zero_wf {t : Tab A B} (h : (Tab.zero : Except String (Tab A B)) = .ok t) : t.WF := by
  simp only [Tab.zero, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨Vals.none_wf hx, Vals.none_wf hy⟩

/-- **`dom` keeps `Tab.WF`**: `Vals.nub` of the key side, on both sides. -/
theorem dom_wf {R : Tab A B} {t : Tab A A} (h : R.dom = .ok t) (hR : R.WF) : t.WF := by
  unfold Tab.dom at h
  cases hn : Vals.nub R.key with
  | error e => simp [hn, Functor.map, Except.map] at h
  | ok y =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h; subst h
    exact ⟨Vals.nub_wf hn hR.1, Vals.nub_wf hn hR.1⟩

/-- **`ran` keeps `Tab.WF`**: `Vals.nub` of the value side, on both sides. -/
theorem ran_wf {R : Tab A B} {t : Tab B B} (h : R.ran = .ok t) (hR : R.WF) : t.WF := by
  unfold Tab.ran at h
  cases hn : Vals.nub R.val with
  | error e => simp [hn, Functor.map, Except.map] at h
  | ok y =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h; subst h
    exact ⟨Vals.nub_wf hn hR.2, Vals.nub_wf hn hR.2⟩

/-- **`idU X` is `Tab.WF`** on a `Vals.WF` `X` (`dom_wf`). -/
theorem idU_wf {n : USize} {X : Vals A n} {t : Tab A A} (h : Tab.idU X = .ok t) (hX : Vals.WF X) : t.WF :=
  dom_wf h ⟨hX, hX⟩

/-- **`R°` keeps `Tab.WF`**: the two sides swapped, `canon`. -/
theorem conv_wf {R : Tab A B} {t : Tab B A} (h : R.conv = .ok t) (hR : R.WF) : t.WF :=
  canon_wf h ⟨hR.2, hR.1⟩

theorem outl_wf {n : USize} {X : Vals (.prod A B) n} {t : Tab (.prod A B) A} (h : Tab.outl X = .ok t)
    (hX : Vals.WF X) : t.WF := canon_wf h ⟨hX, hX.1⟩

theorem outr_wf {n : USize} {X : Vals (.prod A B) n} {t : Tab (.prod A B) B} (h : Tab.outr X = .ok t)
    (hX : Vals.WF X) : t.WF := canon_wf h ⟨hX, hX.2⟩

/-- **`keep` keeps `Tab.WF`**: both sides gathered. -/
theorem keep_wf {T t : Tab A B} {b : Enc} (h : T.keep b = .ok t) (hT : T.WF) : t.WF := by
  simp only [Tab.keep, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact ⟨Vals.gather_wf ‹_› hT.1, Vals.gather_wf ‹_› hT.2⟩

/-- **`concat` keeps `Tab.WF`** (`Vals.concat_wf` on `catPlan`'s count and offsets). -/
theorem concat_wf {R S t : Tab A B} (h : R.concat S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.concat, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨hn, ho⟩ := catPlan_ok (show catPlan R.n S.n = .ok (p.1, p.2) from hp)
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨Vals.concat_wf hn ho hx hR.1 hS.1, Vals.concat_wf hn ho hy hR.2 hS.2⟩

/-- **`∪` keeps `Tab.WF`**: `canon` of the concatenation. -/
theorem union_wf {R S t : Tab A B} (h : R.union S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.union, bind, Except.bind] at h
  split at h; · cases h
  exact canon_wf h (concat_wf ‹_› hR hS)

/-- **`tagged` keeps `Tab.WF`**: its table is the concatenation. -/
theorem tagged_wf {R S : Tab A B} {p : Tab A B × Enc} (h : R.tagged S = .ok p) (hR : R.WF) (hS : S.WF) :
    p.1.WF := by
  simp only [Tab.tagged, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i q hq
  obtain ⟨hn, ho⟩ := catPlan_ok (show catPlan R.n S.n = .ok (q.1, q.2) from hq)
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; okSplit
  cases h; exact ⟨Vals.concat_wf hn ho hx hR.1 hS.1, Vals.concat_wf hn ho hy hR.2 hS.2⟩

/-- **`select` keeps `Tab.WF`**: the kept groups' rows gathered from the tagged concatenation. -/
theorem select_wf {keep : USize → Enc → Enc → Except String Enc} {R S t : Tab A B} (h : select keep R S = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.select, bind, Except.bind, Functor.map, Except.map] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨C, tag⟩ := p
  have hC : Vals.WF (A := .prod A B) (C.key, C.val) := tagged_wf hp hR hS
  dsimp only at h
  okSplit
  cases h; exact Vals.gather_wf ‹_› hC

theorem inter_wf {R S t : Tab A B} (h : R.inter S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := select_wf h hR hS

theorem diff_wf {R S t : Tab A B} (h : R.diff S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := select_wf h hR hS

/-- **`diag q D` keeps `Tab.WF`** where `q` does (`inter_wf`). -/
theorem diag_wf {q : Tab A A → Except String (Tab A A)} (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {D t : Tab A A}
    (h : diag q D = .ok t) (hD : D.WF) : t.WF := by
  simp only [Tab.diag, bind, Except.bind] at h
  split at h; · cases h
  exact inter_wf h (hq _ _ ‹_› hD) hD

end Tab

/-- **`Tab.ofBits` is `Tab.WF`** on `Vals.WF` sides: both gathered. -/
theorem Tab.ofBits_wf {n m : USize} {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {t : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok t) (hx : Vals.WF x) (hy : Vals.WF y) : t.WF := by
  simp only [Tab.ofBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact ⟨Vals.gather_wf ‹_› hx, Vals.gather_wf ‹_› hy⟩

/-- **`Vals.cross` keeps `Vals.WF`**: both sides gathered. -/
theorem Vals.cross_wf {n m : USize} {x : Vals A n} {y : Vals B m} {r : (T : USize) × Vals A T × Vals B T}
    (h : Vals.cross x y = .ok r) (hx : Vals.WF x) (hy : Vals.WF y) : Vals.WF r.2.1 ∧ Vals.WF r.2.2 := by
  simp only [Vals.cross, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact ⟨Vals.gather_wf ‹_› hx, Vals.gather_wf ‹_› hy⟩

namespace Tab

theorem cross_wf {n m : USize} {X : Vals A n} {Y : Vals B m} {t : Tab A B} (h : Tab.cross X Y = .ok t)
    (hX : Vals.WF X) (hY : Vals.WF Y) : t.WF := by
  simp only [Tab.cross, bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  exact canon_wf h (Vals.cross_wf hr hX hY)

theorem top_wf {n m : USize} {X : Vals A n} {Y : Vals B m} {t : Tab A B} (h : Tab.top X Y = .ok t)
    (hX : Vals.WF X) (hY : Vals.WF Y) : t.WF := cross_wf h hX hY

/-- **`R × S` keeps `Tab.WF`**: `Vals.cross` of the pair sides, `canon`. -/
theorem prod_wf {R : Tab A B} {S : Tab C D} {t : Tab (.prod A C) (.prod B D)} (h : R.prod S = .ok t) (hR : R.WF)
    (hS : S.WF) : t.WF := by
  simp only [Tab.prod, bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨h1, h2⟩ := Vals.cross_wf (A := .prod A B) (B := .prod C D) hr hR hS
  exact canon_wf h ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-- **`inl X` keeps `Tab.WF`**: `X` on both sides, a right summand of no row. -/
theorem inl_wf {n : USize} {X : Vals A n} {t : Tab A (.sum A B)} (h : Tab.inl (B := B) X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.inl, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hX, hX, Vals.none_wf ‹_›⟩

theorem inr_wf {n : USize} {Y : Vals B n} {t : Tab B (.sum A B)} (h : Tab.inr (A := A) Y = .ok t)
    (hY : Vals.WF Y) : t.WF := by
  simp only [Tab.inr, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hY, Vals.none_wf ‹_›, hY⟩

/-- **`compExpand` keeps `Tab.WF`**: `R.key` and `S.val` gathered at each output row, `canon`. -/
theorem compExpand_wf {R : Tab A B} {S : Tab B C} {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc}
    {t : Tab A C} (h : compExpand R S x = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  obtain ⟨N, p, g, f, K, cR, cS, w⟩ := x
  simp only [Tab.compExpand, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hR.1, Vals.gather_wf ‹_› hS.2⟩

theorem compOne_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : compOne R S = .ok t) (hR : R.WF) (hS : S.WF) :
    t.WF := by
  simp only [Tab.compOne, bind, Except.bind] at h
  split at h; · cases h
  exact compExpand_wf h hR hS

theorem compBlock_wf {R : Tab A B} {S : Tab B C} {c : Enc} {j : Nat} {t : Tab A C} (h : compBlock R S c j = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compBlock, bind, Except.bind] at h
  okSplit
  exact compOne_wf h (keep_wf ‹_› hR) hS

/-- **`compBlocks` keeps `Tab.WF`**: each block by `compBlock_wf`, met by `∪` (`union_wf`). -/
theorem compBlocks_wf {R : Tab A B} {S : Tab B C} {nb : Nat} {bid : Arr .i64 R.n} {t : Tab A C}
    (h : compBlocks R S nb bid = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compBlocks, bind, Except.bind] at h
  okSplit
  refine foldlM_keeps (P := Tab.WF) (fun b a b' hb hw => ?_) _ h (compBlock_wf ‹_› hR hS)
  simp only [bind, Except.bind] at hb
  split at hb; · cases hb
  exact union_wf hb hw (compBlock_wf ‹_› hR hS)

theorem compFrom_wf {bound : Nat} {R : Tab A B} {S : Tab B C} {x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc}
    {t : Tab A C} (h : compFrom bound R S x = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compFrom, bind, Except.bind] at h
  okSplit
  all_goals first | exact compExpand_wf h hR hS | exact compBlocks_wf h hR hS

/-- **`R ≫ S` keeps `Tab.WF`** (`compOne_wf`, `compFrom_wf`). -/
theorem comp_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : R.comp S = .ok t) (hR : R.WF) (hS : S.WF) :
    t.WF := by
  simp only [Tab.comp, Tab.compWith, bind, Except.bind] at h
  okSplit
  all_goals first | exact compOne_wf h hR hS | exact compFrom_wf h hR hS

/-- **`⟨R, S⟩` keeps `Tab.WF`**: `comp` of `⟨𝟙, R⟩°` and `S`, its key rebracketed. -/
theorem pair_wf {R : Tab A B} {S : Tab A C} {t : Tab A (.prod B C)} (h : R.pair S = .ok t) (hR : R.WF)
    (hS : S.WF) : t.WF := by
  simp only [Tab.pair, Functor.map, Except.map] at h
  split at h; · cases h
  rename_i T hT; cases h
  have := comp_wf hT ⟨⟨hR.1, hR.2⟩, hR.1⟩ hS
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **`Rᴵ` keeps `Tab.WF`** on a `Vals.WF` `X` (`outl_wf`, `outr_wf`, `comp_wf`, `inter_wf`). -/
theorem flat_wf {n : USize} {X : Vals (.prod I A) n} {R : Tab I (.prod A B)} {t : Tab (.prod I A) B}
    (h : Tab.flat X R = .ok t) (hX : Vals.WF X) (hR : R.WF) : t.WF := by
  simp only [Tab.flat, bind, Except.bind] at h
  split at h; · cases h
  rename_i a ha; split at h; · cases h
  rename_i L hL; split at h; · cases h
  rename_i b hb; split at h; · cases h
  rename_i c hc; split at h; · cases h
  rename_i d hd; split at h; · cases h
  rename_i M hM; split at h; · cases h
  rename_i P hP; split at h; · cases h
  rename_i e he
  have hRv : Vals.WF R.val := hR.2
  have wL := comp_wf hL (outl_wf ha hX) hR
  have wM := comp_wf hM (outr_wf hb hX) (conv_wf hd (outl_wf hc hRv))
  exact comp_wf h (inter_wf hP wL wM) (outr_wf he hRv)

end Tab

/-! ### The bit-matrix and division ops -/

/-- **`Vals.code2`'s joined side keeps `Vals.WF`**: the concatenation of the two (`Vals.concat_wf`). -/
theorem Vals.code2_wf {n₁ n₂ : USize} {x : Vals A n₁} {y : Vals A n₂}
    {r : USize × Enc × Enc × ((N : USize) × Vals A N × Enc)} (h : Vals.code2 x y = .ok r) (hx : Vals.WF x)
    (hy : Vals.WF y) : Vals.WF r.2.2.2.2.1 := by
  simp only [Vals.code2, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨hn, ho⟩ := catPlan_ok (show catPlan n₁ n₂ = .ok (p.1, p.2) from hp)
  split at h; · cases h
  rename_i z hz
  okSplit
  cases h; exact Vals.concat_wf hn ho hz hx hy

namespace Tab

theorem compBits_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : compBits R S = .ok t) (hR : R.WF) (hS : S.WF) :
    t.WF := by
  simp only [Tab.compBits, bind, Except.bind] at h
  okSplit
  exact ofBits_wf h hR.1 hS.2

/-- A table `compSelM` answers is `compFrom`'s (`compFrom_wf`). -/
theorem compSelM_inl_wf {bits : Nat} {R : Tab A B} {S : Tab B C} {t : Tab A C}
    (h : compSelM bits R S = .ok (.inl t)) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compSelM, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | (cases h; exact compFrom_wf ‹_› hR hS) | cases h

/-- **`compSel` keeps `Tab.WF`**: `compFrom`'s table or the matrix read back (`ofBits_wf`). -/
theorem compSel_wf {bits : Nat} {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : compSel bits R S = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compSel, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | (cases h; exact compSelM_inl_wf ‹_› hR hS) | exact ofBits_wf h hR.1 hS.2

/-- **`keepBits` keeps `Tab.WF`**: rows of `T.canon` kept twice (`keep_wf`). -/
theorem keepBits_wf {T t : Tab A C} {n m : USize} {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m}
    (h : T.keepBits g w o x ra y rc = .ok t) (hT : T.WF) : t.WF := by
  simp only [Tab.keepBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact keep_wf h (keep_wf ‹_› (canon_wf ‹_› hT))

/-- **`ldivBits` keeps `Tab.WF`**: its matrix read back over the joined sides of `Vals.code2` (`code2_wf`). -/
theorem ldivBits_wf {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldivBits R S UB UC = .ok t) (hR : R.WF) (hS : S.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact ofBits_wf h (Vals.code2_wf ‹_› hR.2 hB.2) (Vals.code2_wf ‹_› hS.2 hC.2)

theorem mem_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) B} (h : Tab.mem X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.mem, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hX, Vals.gather_wf ‹_› hX.2⟩

theorem cmpPairs_wf {op : Op} {t : QAtomicType} {T u : Tab (.atom t) (.atom t)} (h : cmpPairs op T = .ok u)
    (hT : T.WF) : u.WF := by
  simp only [Tab.cmpPairs, bind, Except.bind] at h
  okSplit
  exact keep_wf h hT

theorem cmpOn_wf {op : Op} {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {u : Tab (.atom t) (.atom t)} (h : cmpOn op K L = .ok u) (hK : Vals.WF K) (hL : Vals.WF L) : u.WF := by
  simp only [Tab.cmpOn, bind, Except.bind] at h
  okSplit
  exact cmpPairs_wf h (cross_wf ‹_› hK hL)

theorem lt_wf {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {u : Tab (.atom t) (.atom t)} (h : Tab.lt t K L = .ok u) (hK : Vals.WF K) (hL : Vals.WF L) : u.WF := by
  simp only [Tab.lt, bind, Except.bind] at h
  okSplit
  exact cmpOn_wf h hK hL

theorem leq_wf {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {u : Tab (.atom t) (.atom t)} (h : Tab.leq t K L = .ok u) (hK : Vals.WF K) (hL : Vals.WF L) : u.WF := by
  simp only [Tab.leq, bind, Except.bind] at h
  okSplit
  exact cmpOn_wf h hK hL

/-- **`R \ S` keeps `Tab.WF`**: the groups of `Q = r° ≫ ⟨𝟙, s⟩` gathered (`compOne_wf`), `∪` the vacuous part
(`cross_wf` of `ran`s). -/
theorem ldiv_wf {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldiv R S UB UC = .ok t) (hR : R.WF) (hS : S.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldiv, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i r hr; split at h; · cases h
  rename_i s hs; split at h; · cases h
  rename_i Q hQ
  have wr := canon_wf hr hR
  have ws := canon_wf hs hS
  have wQ := compOne_wf hQ ⟨wr.2, wr.1⟩ ⟨ws.1, ws.1, ws.2⟩
  okSplit
  exact union_wf h ⟨Vals.gather_wf ‹_› wQ.1, Vals.gather_wf ‹_› wQ.2.2⟩
    (cross_wf ‹_› (diff_wf ‹_› (ran_wf ‹_› hB) (ran_wf ‹_› hR)).1 (ran_wf ‹_› hC).1)

/-- **`ldivSel` keeps `Tab.WF`** (`ldiv_wf`, `ldivBits_wf`). -/
theorem ldivSel_wf {bits : Nat} {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldivSel bits R S UB UC = .ok t) (hR : R.WF) (hS : S.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivSel, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | exact ldiv_wf h hR hS hB hC | exact ldivBits_wf h hR hS hB hC

theorem rdiv_wf {R : Tab A C} {S : Tab B C} {UA : Tab A A} {UB : Tab B B} {t : Tab A B}
    (h : rdiv R S UA UB = .ok t) (hR : R.WF) (hS : S.WF) (hA : UA.WF) (hB : UB.WF) : t.WF := by
  simp only [Tab.rdiv, bind, Except.bind] at h
  okSplit
  exact conv_wf h (ldiv_wf ‹_› (conv_wf ‹_› hS) (conv_wf ‹_› hR) hB hA)

/-- **`ldivTabMat`'s two sides keep `Vals.WF`**: each the joined side of a `Vals.code2` (`code2_wf`). -/
theorem ldivTabMat_sides_wf {R : Tab A B} {UB : Tab B B} {UC : Tab C C} {n m g w : USize} {o ra rc : Enc}
    {x : Vals A n} {y : Vals C m} {kb kc N N' : USize} {o' rb rc' : Enc} {zb : Vals B N} {zc : Vals C N'}
    (h : ldivTabMat R UB UC g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hR : R.WF) (hB : UB.WF) (hC : UC.WF) (hy : Vals.WF y) : Vals.WF zb ∧ Vals.WF zc := by
  simp only [Tab.ldivTabMat, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h
  exact ⟨Vals.code2_wf ‹_› hR.2 hB.2, Vals.code2_wf ‹_› (Vals.gather_wf ‹_› hy) hC.2⟩

/-- **`compTabMat`'s key side keeps `Vals.WF`**: rows of `R.key` gathered. -/
theorem compTabMat_key_wf {R : Tab A B} {n g w ka M : USize} {o o' ra ra' : Enc} {x : Vals B n} {key : Vals A M}
    (h : compTabMat R g w o x ra = .ok (ka, o', ⟨M, key⟩, ra')) (hR : R.WF) : Vals.WF key := by
  simp only [Tab.compTabMat, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact Vals.gather_wf ‹_› hR.1

theorem inlConv_wf {n : USize} {X : Vals (.sum A B) n} {t : Tab (.sum A B) A} (h : Tab.inlConv X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  simp only [Tab.inlConv, bind, Except.bind] at h
  okSplit
  all_goals first | exact zero_wf h | exact comp_wf h (idU_wf ‹_› hX) (conv_wf ‹_› (inl_wf ‹_› hX.1))

theorem inrConv_wf {n : USize} {X : Vals (.sum A B) n} {t : Tab (.sum A B) B} (h : Tab.inrConv X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  simp only [Tab.inrConv, bind, Except.bind] at h
  okSplit
  all_goals first | exact zero_wf h | exact comp_wf h (idU_wf ‹_› hX) (conv_wf ‹_› (inr_wf ‹_› hX.2))

end Tab

end Rel
