/-
  `thinLOn` in two passes (doc/rel-rows.md §1), read back under its bit: `thinAC`'s and `thinKC`'s steps from their
  primitives' read-backs, the two passes' meaning `thinTwoDen` on one array, and `thinTwoDen_eq`: it is `thinLDen`,
  the chain from the end that `thinLOn` is specified by.
-/
import Rel.CRelLoop

namespace Rel

open Tab Rel.Kernel Rel.Verify Rel Rel.Alg Rel.KernelWF
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Rel.Rep Rel.Rep.FoldN Rel.Rep.OpsN Rel.Rep.Prim Rel.Rep.ListN

namespace Rep

/-! ## Chains by index, one element at a time -/

/-- The chain a right fold leaves on `xs`: `ys[n]` passes `P0`, `R xs[t] ys[t+1] ys[t]` at each `t`, `w = ys[0]`
    (`rep_foldOnC`'s right side, `thinLDen`). -/
def IxChain {α β : Type _} (R : α → β → β → Prop) (P0 : β → Prop) (xs : List α) (w : β) : Prop :=
  ∃ ys : List β, ∃ hy : ys.length = xs.length + 1, P0 (ys[xs.length]'(by omega)) ∧
    (∀ t (ht : t < xs.length), R (xs[t]'ht) (ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧ w = ys[0]'(by omega)

theorem ixChain_congr {α β : Type _} (R : α → β → β → Prop) {P0 P1 : β → Prop} (hP : ∀ y, P0 y ↔ P1 y)
    (xs : List α) (w : β) : IxChain R P0 xs w ↔ IxChain R P1 xs w := by
  simp only [IxChain, hP]

theorem ixChain_nil {α β : Type _} (R : α → β → β → Prop) (P0 : β → Prop) (w : β) :
    IxChain R P0 [] w ↔ P0 w := by
  constructor
  · rintro ⟨ys, hy, h0, -, rfl⟩; simpa using h0
  · intro h; exact ⟨[w], rfl, h, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩

theorem ixChain_cons {α β : Type _} (R : α → β → β → Prop) (P0 : β → Prop) (x : α) (xs : List α) (w : β) :
    IxChain R P0 (x :: xs) w ↔ ∃ v, IxChain R P0 xs v ∧ R x v w := by
  constructor
  · rintro ⟨ys, hy, h0, hs, rfl⟩
    simp only [List.length_cons] at hy
    refine ⟨ys[1]'(by omega), ⟨ys.tail, by simp [hy], ?_, fun t ht => ?_, by simp⟩, ?_⟩
    · simpa using h0
    · simpa using hs (t + 1) (by simp; omega)
    · simpa using hs 0 (by simp)
  · rintro ⟨v, ⟨ys, hy, h0, hs, rfl⟩, hR⟩
    refine ⟨w :: ys, by simp [hy], by simpa using h0, fun t ht => ?_, rfl⟩
    cases t with
    | zero => simpa using hR
    | succ t => simpa using hs t (by simp at ht; omega)

/-- The states a `loop` passes through on `xs` from `c` (`rep_loopOnC`'s right side). -/
def IxLoop {α γ : Type _} (F : γ × α → γ → Prop) (c : γ) (xs : List α) (c' : γ) : Prop :=
  ∃ g : Nat → γ, g 0 = c ∧ (∀ t (ht : t < xs.length), F (g t, xs[t]'ht) (g (t + 1))) ∧ c' = g xs.length

theorem ixLoop_nil {α γ : Type _} (F : γ × α → γ → Prop) (c c' : γ) : IxLoop F c [] c' ↔ c' = c :=
  ⟨fun ⟨_, h0, _, e⟩ => e.trans h0, fun e => ⟨fun _ => c, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _), e⟩⟩

theorem ixLoop_cons {α γ : Type _} (F : γ × α → γ → Prop) (c : γ) (x : α) (xs : List α) (c' : γ) :
    IxLoop F c (x :: xs) c' ↔ ∃ c₁, F (c, x) c₁ ∧ IxLoop F c₁ xs c' := by
  constructor
  · rintro ⟨g, h0, hs, rfl⟩
    refine ⟨g 1, ?_, fun t => g (t + 1), rfl, fun t ht => hs (t + 1) (by simp; omega), rfl⟩
    rw [← h0]; exact hs 0 (by simp)
  · rintro ⟨c₁, hF, g, h0, hs, rfl⟩
    refine ⟨fun t => Nat.casesOn t c fun t => g t, rfl, fun t ht => ?_, rfl⟩
    cases t with
    | zero => show F (c, x) (g 0); rw [h0]; exact hF
    | succ t => exact hs t (by simp at ht; omega)

/-! ## The two passes on one array -/

/-- `thinA(Q)` on `(x, (h, as))`, `h` the last element pushed, `as` the actions so far: `x` pushed onto an empty
    `h` (action 0); with `h = b :: bs`, `x` replaces `b` when `le x b` (1), is dropped when `le b x` (2), and is
    pushed when neither (0). -/
def thinAStep {B : Obj} (le : B.El → B.El → Bool) (p : B.El × (List B.El × List Int64))
    (v : List B.El × List Int64) : Prop :=
  (p.2.1 = [] ∧ v = ([p.1], p.2.2 ++ [0])) ∨ ∃ b bs, p.2.1 = b :: bs ∧
    ((le p.1 b = true ∧ v = ([p.1], p.2.2 ++ [1])) ∨ (le b p.1 = true ∧ v = (p.2.1, p.2.2 ++ [2])) ∨
      (le p.1 b = false ∧ le b p.1 = false ∧ v = ([p.1], p.2.2 ++ [0])))

/-- `thinK` on `(((o, c), as), x)`, `as` not empty, `a` its last: `x` dropped when `a = 2`; otherwise `x` appended
    to `o` when `c = 0`, and `a` the new `c`. -/
def thinK {B : Obj} (s : ((List B.El × Int64) × List Int64) × B.El) : (List B.El × Int64) × List Int64 :=
  if s.1.2.getLastD 0 ≠ 2 then
    ((if s.1.1.2 = 0 then s.1.1.1 ++ [s.2] else s.1.1.1, s.1.2.getLastD 0), s.1.2.dropLast)
  else (s.1.1, s.1.2.dropLast)

/-- One step of `thinLDen`'s chain: `x` bumped into the thinned rest `y`. -/
def thinLStep {B : Obj} (le : B.El → B.El → Bool) (x : B.El) (y y' : List B.El) : Prop :=
  (y = [] ∧ y' = [x]) ∨ ∃ b bs, y = b :: bs ∧
    ((le x b = true ∧ y' = x :: bs) ∨ (le b x = true ∧ y' = y) ∨ (le x b = false ∧ le b x = false ∧ y' = x :: y))

/-- **The two passes' meaning on one array**: the actions `as` of the right fold of `thinAStep`, then the left `loop`
    of `thinK` from `(([], 0), as)`; `w` the kept elements it ends with. -/
def thinTwoDen {B : Obj} (le : B.El → B.El → Bool) (xs w : List B.El) : Prop :=
  ∃ s, IxChain (fun x v w => thinAStep le (x, v) w) (· = ([], [])) xs s ∧
    ∃ c, IxLoop (fun s v => s.1.2 ≠ [] ∧ v = thinK s) (([], 0), s.2) xs c ∧ w = c.1.1

theorem thinK_snoc {B : Obj} (o : List B.El) (c a : Int64) (as : List Int64) (x : B.El) :
    thinK (((o, c), as ++ [a]), x) =
      if a ≠ 2 then ((if c = 0 then o ++ [x] else o, a), as) else ((o, c), as) := by
  simp [thinK, List.getLastD_eq_getLast?]

/-- What the second pass makes of the actions `as` of `xs` from any `((o, c), as)`: it ends, and at `o` then the
    thinned rest `y`, its head left out unless `c = 0` (the head was replaced by the element to its left). -/
def thinLoopOK {B : Obj} (xs : List B.El) (as : List Int64) (y : List B.El) : Prop :=
  ∀ o c, (∃ c', IxLoop (fun s v => s.1.2 ≠ [] ∧ v = thinK s) ((o, c), as) xs c') ∧
    ∀ c', IxLoop (fun s v => s.1.2 ≠ [] ∧ v = thinK s) ((o, c), as) xs c' →
      c'.1.1 = o ++ (if c = 0 then y else y.tail)

theorem thinLoopOK_nil {B : Obj} : thinLoopOK (B := B) [] [] [] := fun o c =>
  ⟨⟨((o, c), []), (ixLoop_nil _ _ _).2 rfl⟩, fun c' h => by
    rw [(ixLoop_nil _ _ _).1 h]; by_cases hc : c = 0 <;> simp [hc]⟩

/-- A kept action `a` (push 0 or replace 1) on `x` puts `x` before the rest, its head gone when `a` replaced it. -/
theorem thinLoopOK_keep {B : Obj} {xs : List B.El} {as : List Int64} {y : List B.El} (x : B.El) (a : Int64)
    (ha : a ≠ 2) (r : List B.El) (hr : r = if a = 0 then y else y.tail) (h : thinLoopOK xs as y) :
    thinLoopOK (x :: xs) (as ++ [a]) (x :: r) := by
  intro o c
  have e : thinK (((o, c), as ++ [a]), x) = ((if c = 0 then o ++ [x] else o, a), as) := by
    rw [thinK_snoc, if_pos ha]
  obtain ⟨⟨c', hc'⟩, hv⟩ := h (if c = 0 then o ++ [x] else o) a
  refine ⟨⟨c', (ixLoop_cons _ _ _ _ _).2 ⟨_, ⟨by simp, e.symm⟩, hc'⟩⟩, fun c'' h' => ?_⟩
  obtain ⟨c₁, ⟨-, e₁⟩, h₁⟩ := (ixLoop_cons _ _ _ _ _).1 h'
  rw [e₁, e] at h₁
  rw [hv _ h₁, hr]
  by_cases hc : c = 0 <;> simp [hc]

/-- A drop (action 2) on `x` leaves the state as it was. -/
theorem thinLoopOK_drop {B : Obj} {xs : List B.El} {as : List Int64} {y : List B.El} (x : B.El)
    (h : thinLoopOK xs as y) : thinLoopOK (x :: xs) (as ++ [2]) y := by
  intro o c
  have e : thinK (((o, c), as ++ [2]), x) = ((o, c), as) := by rw [thinK_snoc, if_neg (by simp)]
  obtain ⟨⟨c', hc'⟩, hv⟩ := h o c
  refine ⟨⟨c', (ixLoop_cons _ _ _ _ _).2 ⟨_, ⟨by simp, e.symm⟩, hc'⟩⟩, fun c'' h' => ?_⟩
  obtain ⟨c₁, ⟨-, e₁⟩, h₁⟩ := (ixLoop_cons _ _ _ _ _).1 h'
  rw [e₁, e] at h₁
  exact hv _ h₁

/-- From the first pass's chain to `thinLDen`'s: the last element pushed is the rest's head. -/
theorem thin_two_fwd {B : Obj} (le : B.El → B.El → Bool) (xs : List B.El) :
    ∀ h as, IxChain (fun x v w => thinAStep le (x, v) w) (· = ([], [])) xs (h, as) →
      ∃ y, IxChain (thinLStep le) (· = []) xs y ∧ h = y.take 1 ∧ thinLoopOK xs as y := by
  induction xs with
  | nil =>
    intro h as hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((ixChain_nil (fun x v w => thinAStep le (x, v) w) (· = ([], [])) _).1 hc)
    exact ⟨[], (ixChain_nil _ _ _).2 rfl, rfl, thinLoopOK_nil⟩
  | cons x xs ih =>
    intro h' as' hc
    obtain ⟨⟨h, as⟩, hc, hA⟩ := (ixChain_cons _ _ _ _ _).1 hc
    obtain ⟨y, hy, rfl, hok⟩ := ih h as hc
    rcases hA with ⟨hh, he⟩ | ⟨b, bs, hh, hA⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hy0 : y = [] := by simpa using hh
      subst hy0
      exact ⟨[x], (ixChain_cons _ _ _ _ _).2 ⟨[], hy, Or.inl ⟨rfl, rfl⟩⟩, rfl,
        thinLoopOK_keep x 0 (by decide) [] (if_pos rfl).symm hok⟩
    · cases y with
      | nil => simp at hh
      | cons b' t =>
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        rcases hA with ⟨hl, he⟩ | ⟨hl, he⟩ | ⟨hl1, hl2, he⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        · exact ⟨x :: t, (ixChain_cons _ _ _ _ _).2 ⟨_, hy, Or.inr ⟨b', t, rfl, Or.inl ⟨hl, rfl⟩⟩⟩, rfl,
            thinLoopOK_keep x 1 (by decide) t (if_neg (by decide)).symm hok⟩
        · exact ⟨b' :: t, (ixChain_cons _ _ _ _ _).2 ⟨_, hy, Or.inr ⟨b', t, rfl, Or.inr (Or.inl ⟨hl, rfl⟩)⟩⟩,
            rfl, thinLoopOK_drop x hok⟩
        · exact ⟨x :: b' :: t,
            (ixChain_cons _ _ _ _ _).2 ⟨_, hy, Or.inr ⟨b', t, rfl, Or.inr (Or.inr ⟨hl1, hl2, rfl⟩)⟩⟩, rfl,
            thinLoopOK_keep x 0 (by decide) (b' :: t) (if_pos rfl).symm hok⟩

/-- From `thinLDen`'s chain to the first pass's: each case of the bump is one action. -/
theorem thin_two_bwd {B : Obj} (le : B.El → B.El → Bool) (xs : List B.El) :
    ∀ y, IxChain (thinLStep le) (· = []) xs y → ∃ h as,
      IxChain (fun x v w => thinAStep le (x, v) w) (· = ([], [])) xs (h, as) ∧ h = y.take 1 ∧
        thinLoopOK xs as y := by
  induction xs with
  | nil =>
    intro y hc
    obtain rfl := (ixChain_nil _ _ _).1 hc
    exact ⟨[], [], (ixChain_nil _ _ _).2 rfl, rfl, thinLoopOK_nil⟩
  | cons x xs ih =>
    intro y' hc
    obtain ⟨y, hc, hT⟩ := (ixChain_cons _ _ _ _ _).1 hc
    obtain ⟨h, as, hA, rfl, hok⟩ := ih y hc
    rcases hT with ⟨rfl, rfl⟩ | ⟨b, bs, rfl, ⟨hl, rfl⟩ | ⟨hl, rfl⟩ | ⟨hl1, hl2, rfl⟩⟩
    · exact ⟨[x], as ++ [0], (ixChain_cons _ _ _ _ _).2 ⟨_, hA, Or.inl ⟨rfl, rfl⟩⟩, rfl,
        thinLoopOK_keep x 0 (by decide) [] (if_pos rfl).symm hok⟩
    · exact ⟨[x], as ++ [1], (ixChain_cons _ _ _ _ _).2 ⟨_, hA, Or.inr ⟨b, [], rfl, Or.inl ⟨hl, rfl⟩⟩⟩, rfl,
        thinLoopOK_keep x 1 (by decide) bs (if_neg (by decide)).symm hok⟩
    · exact ⟨[b], as ++ [2], (ixChain_cons _ _ _ _ _).2 ⟨_, hA, Or.inr ⟨b, [], rfl, Or.inr (Or.inl ⟨hl, rfl⟩)⟩⟩,
        rfl, thinLoopOK_drop x hok⟩
    · exact ⟨[x], as ++ [0],
        (ixChain_cons _ _ _ _ _).2 ⟨_, hA, Or.inr ⟨b, [], rfl, Or.inr (Or.inr ⟨hl1, hl2, rfl⟩)⟩⟩, rfl,
        thinLoopOK_keep x 0 (by decide) (b :: bs) (if_pos rfl).symm hok⟩

/-- **`⟦two passes⟧ = thinLDen`**: the actions appended right to left, then the kept elements appended left to
    right, are the chain from the end, each element bumped into the thinned rest to its right. -/
theorem thinTwoDen_eq {B : Obj} (le : B.El → B.El → Bool) : thinTwoDen le = thinLDen le := by
  funext xs w
  have eL : thinLDen le xs w ↔ IxChain (thinLStep le) (· = []) xs w :=
    ixChain_congr (thinLStep le) (P0 := fun y => ∃ p, (nilVal B).row p = y)
      (fun y => ⟨fun ⟨p, h⟩ => by rw [← h, nilVal_row], fun h => ⟨⟨0, by simp⟩, by rw [nilVal_row, h]⟩⟩) xs w
  refine propext (Iff.trans ?_ eL.symm)
  constructor
  · rintro ⟨⟨h, as⟩, hA, c, hL, rfl⟩
    obtain ⟨y, hy, -, hok⟩ := thin_two_fwd le xs h as hA
    rw [(hok [] 0).2 c hL]
    simpa using hy
  · intro hy
    obtain ⟨h, as, hA, -, hok⟩ := thin_two_bwd le xs w hy
    obtain ⟨⟨c, hc⟩, hv⟩ := hok [] 0
    exact ⟨(h, as), hA, c, hc, by rw [hv c hc]; simp⟩

/-! ## The steps' read-backs -/

/-- `R` on the states `P`, the function `f` there: the read-back each piece of `thinAC`, `thinKC` has. -/
abbrev FnOn {A B : Obj} (R : Tab A B) (P : A.El → Prop) (f : A.El → B.El) : Prop :=
  ∀ s z, rep R s z ↔ P s ∧ z = f s

theorem fnOn_congr {A B : Obj} {R : Tab A B} {P P' : A.El → Prop} {f : A.El → B.El} (h : FnOn R P f)
    (hP : ∀ s, P s ↔ P' s) : FnOn R P' f := fun s z => (h s z).trans (and_congr_left' (hP s))

theorem fnOn_outl {A B C : Obj} {T : Tab A (.prod B C)} {P : A.El → Prop} {f : A.El → (Obj.prod B C).El}
    (h : FnOn T P f) : FnOn (outl T) P fun s => (f s).1 := fun s z =>
  (outl_holds T s z).trans ⟨fun ⟨w, hw⟩ => by obtain ⟨hp, e⟩ := (h _ _).1 hw; exact ⟨hp, congrArg Prod.fst e⟩,
    fun ⟨hp, e⟩ => ⟨(f s).2, (h _ _).2 ⟨hp, by rw [e]⟩⟩⟩

theorem fnOn_outr {A B C : Obj} {T : Tab A (.prod B C)} {P : A.El → Prop} {f : A.El → (Obj.prod B C).El}
    (h : FnOn T P f) : FnOn (outr T) P fun s => (f s).2 := fun s z =>
  (outr_holds T s z).trans ⟨fun ⟨w, hw⟩ => by obtain ⟨hp, e⟩ := (h _ _).1 hw; exact ⟨hp, congrArg Prod.snd e⟩,
    fun ⟨hp, e⟩ => ⟨(f s).1, (h _ _).2 ⟨hp, by rw [e]⟩⟩⟩

theorem fnOn_comp {A B C : Obj} {R : Tab A B} {S : Tab B C} {P Q : A.El → Prop} {f : A.El → B.El}
    {g : A.El → C.El} (hR : FnOn R P f) (hS : ∀ s, P s → ∀ z, rep S (f s) z ↔ Q s ∧ z = g s)
    (hb : (compC R S).2 = true) : FnOn (compC R S).1 (fun s => P s ∧ Q s) g := fun s z => by
  rw [rep_compC _ _ hb, comp_apply]
  constructor
  · rintro ⟨y, h1, h2⟩
    obtain ⟨hp, rfl⟩ := (hR _ _).1 h1
    obtain ⟨hq, e⟩ := (hS s hp z).1 h2
    exact ⟨⟨hp, hq⟩, e⟩
  · rintro ⟨⟨hp, hq⟩, e⟩
    exact ⟨f s, (hR _ _).2 ⟨hp, rfl⟩, (hS s hp z).2 ⟨hq, e⟩⟩

theorem fnOn_pair {A B C : Obj} {R : Tab A B} {S : Tab A C} {P Q : A.El → Prop} {f : A.El → B.El}
    {g : A.El → C.El} (hR : FnOn R P f) (hS : FnOn S Q g) (hb : (pairC R S).2 = true) :
    FnOn (pairC R S).1 (fun s => P s ∧ Q s) fun s => (f s, g s) := fun s z => by
  obtain ⟨z1, z2⟩ := z
  rw [rep_pairC _ _ hb]
  show rep R s z1 ∧ rep S s z2 ↔ _
  rw [hR, hS, Prod.mk.injEq]
  exact ⟨fun ⟨⟨hp, e1⟩, hq, e2⟩ => ⟨⟨hp, hq⟩, e1, e2⟩, fun ⟨⟨hp, hq⟩, e1, e2⟩ => ⟨⟨hp, e1⟩, hq, e2⟩⟩

theorem fnOn_snoc {K B : Obj} {T : Tab K (.prod (.arr B) B)} {P : K.El → Prop} {f : K.El → List B.El}
    {g : K.El → B.El} (hT : FnOn T P fun s => (f s, g s)) (hb : (snocC T).2 = true) :
    FnOn (snocC T).1 P fun s => f s ++ [g s] := fun s z => by
  rw [rep_snocC _ hb]
  constructor
  · rintro ⟨bs, b, h, rfl⟩
    obtain ⟨hp, e⟩ := (hT _ _).1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, rfl⟩; exact ⟨f s, g s, (hT _ _).2 ⟨hp, rfl⟩, rfl⟩

theorem fnOn_top {A B : Obj} {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (k : B.El)
    (hk : ∀ b, (∃ j, Ub.row j = b) ↔ b = k) (hb : (topC Ua Ub).2 = true) :
    FnOn (topC Ua Ub).1 (fun s => ∃ i, Ua.row i = s) fun _ => k := fun s z => by
  rw [rep_topC _ _ hb, comp_apply]
  constructor
  · rintro ⟨s', ⟨rfl, hs⟩, hz⟩
    rw [comp_apply] at hz
    obtain ⟨z', -, rfl, hz'⟩ := hz
    exact ⟨hs, (hk _).1 hz'⟩
  · rintro ⟨hs, e⟩
    exact ⟨s, ⟨rfl, hs⟩, by rw [comp_apply]; exact ⟨z, trivial, rfl, (hk z).2 e⟩⟩

theorem fnOn_dom {A B : Obj} {R : Tab A B} {P : A.El → Prop} {f : A.El → B.El} (hR : FnOn R P f)
    (hb : (domC R).2 = true) : FnOn (domC R).1 P fun s => s := fun s z => by
  rw [(rep_domC _ hb).trans (dom_corefl _)]
  show s = z ∧ (∃ b, rep R s b) ↔ _
  exact ⟨fun ⟨e, b, h⟩ => ⟨((hR _ _).1 h).1, e.symm⟩, fun ⟨hp, e⟩ => ⟨e.symm, f s, (hR _ _).2 ⟨hp, rfl⟩⟩⟩

theorem fnOn_diff {A : Obj} {C1 C2 : Tab A A} {P Q : A.El → Prop} (h1 : FnOn C1 P fun s => s)
    (h2 : FnOn C2 Q fun s => s) (hb : (diffC C1 C2).2 = true) :
    FnOn (diffC C1 C2).1 (fun s => P s ∧ ¬ Q s) fun s => s := fun s z => by
  rw [rep_diffC _ _ hb, h1, h2]
  constructor
  · rintro ⟨⟨hp, rfl⟩, hn⟩; exact ⟨⟨hp, fun hq => hn ⟨hq, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨hp, hn⟩, rfl⟩; exact ⟨⟨hp, rfl⟩, fun ⟨hq, _⟩ => hn hq⟩

theorem fnOn_union {A B : Obj} {R S : Tab A B} {P Q : A.El → Prop} {f : A.El → B.El} (h1 : FnOn R P f)
    (h2 : FnOn S Q f) (hb : (unionC R S).2 = true) : FnOn (unionC R S).1 (fun s => P s ∨ Q s) f := fun s z => by
  rw [rep_unionC _ _ hb]
  show rep R s z ∨ rep S s z ↔ _
  rw [h1, h2]; exact or_and_right.symm

theorem fnOn_union_if {A B : Obj} {R S : Tab A B} {P Q : A.El → Prop} [DecidablePred Q] {f g : A.El → B.El}
    (h1 : FnOn R (fun s => P s ∧ Q s) f) (h2 : FnOn S (fun s => P s ∧ ¬ Q s) g) (hb : (unionC R S).2 = true) :
    FnOn (unionC R S).1 P fun s => if Q s then f s else g s := fun s z => by
  rw [rep_unionC _ _ hb]
  show rep R s z ∨ rep S s z ↔ _
  rw [h1, h2]
  by_cases hq : Q s <;> simp [hq]

theorem fnOn_corefl {A : Obj} {C : Tab A A} {P : A.El → Prop} (h : ∀ s s', rep C s s' ↔ s = s' ∧ P s) :
    FnOn C P fun s => s := fun s z => (h s z).trans ⟨fun ⟨e, hp⟩ => ⟨hp, e.symm⟩, fun ⟨hp, e⟩ => ⟨e.symm, hp⟩⟩

/-- A coreflexive `D` is the identity on the states it holds. -/
theorem fnOn_self {A : Obj} {D : Tab A A} (hD : ∀ s s', rep D s s' → s = s') :
    FnOn D (fun s => rep D s s) fun s => s := fun s z =>
  ⟨fun h => ⟨by obtain rfl := hD _ _ h; exact h, (hD _ _ h).symm⟩, fun ⟨h, e⟩ => e ▸ h⟩

/-- The one row of `col [k]`. -/
theorem col_one_row (k b : Int64) : (∃ j, Vals.row (A := .atom .long) (col [k]) j = b) ↔ b = k := by
  have h1 : ([k] : List Int64).length < USize.size := by
    show 1 < USize.size; rcases USize.size_eq with e | e <;> omega
  constructor
  · rintro ⟨j, hj⟩; rw [Vals.row_atom, col_get [k] h1 j] at hj; simp at hj; exact hj.symm
  · intro e
    exact ⟨⟨0, by simp⟩, by rw [Vals.row_atom, col_get [k] h1, e]; rfl⟩

/-- `idU (col [k])` on a value of `R`: the values equal to `k`. -/
theorem fnOn_compK {A : Obj} {R : Tab A .long} {P : A.El → Prop} {f : A.El → Int64} (k : Int64)
    (hR : FnOn R P f) (hb : (compC R (idU (col [k]))).2 = true) :
    FnOn (compC R (idU (col [k]))).1 (fun s => P s ∧ f s = k) f :=
  fnOn_comp hR (fun s _ z => by
    rw [rep_idU]
    show f s = z ∧ (∃ i, Vals.row (A := .atom .long) (col [k]) i = f s) ↔ _
    rw [col_one_row]
    exact ⟨fun ⟨e, h⟩ => ⟨h, e.symm⟩, fun ⟨h, e⟩ => ⟨e.symm, h⟩⟩) hb

theorem snoc_eq_iff {α : Type _} (xs bs : List α) (b d : α) :
    xs = bs ++ [b] ↔ xs ≠ [] ∧ (bs, b) = (xs.dropLast, xs.getLastD d) := by
  constructor
  · rintro rfl; simp [List.getLastD_eq_getLast?]
  · rintro ⟨hne, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    rcases List.eq_nil_or_concat xs with rfl | ⟨L, c, rfl⟩
    · exact absurd rfl hne
    · simp [List.getLastD_eq_getLast?]

/-- **`thinKC`'s step on a coreflexive `D`, read back under its bit**: `thinK` on the states of `D` whose actions are
    not empty, each piece read back by its twin's lemma. -/
theorem thinKC_rep {B : Obj}
    (D : Tab (.prod (.prod (.prod (.arr B) .long) (.arr .long)) B)
      (.prod (.prod (.prod (.arr B) .long) (.arr .long)) B))
    (hD : ∀ s s', rep D s s' → s = s') (hb : (thinKC D).2 = true) :
    FnOn (thinKC D).1 (fun s => rep D s s ∧ s.1.2 ≠ []) thinK := by
  simp only [thinKC, Bool.and_eq_true, and_assoc] at hb
  obtain ⟨hun, hu, ha2, hdr, hdu, hnd, hc0, hkp, hkk, hnk, hko, hkx, hks, hno, ho', hna, hoa, hna', hr1, hdoc,
    hda', hr2, hbody⟩ := hb
  have h0 := fnOn_self hD
  have hL := fnOn_outl h0
  have hOC := fnOn_outl hL
  have hO := fnOn_outl hOC
  have hC := fnOn_outr hOC
  have hAs := fnOn_outr hL
  have hX := fnOn_outr h0
  -- `snoc°` of the actions: all but the last, and the last
  have hU := fnOn_comp hAs (Q := fun (s : (Obj.prod (.prod (.prod (.arr B) .long) (.arr .long)) B).El) => s.1.2 ≠ [])
    (g := fun (s : (Obj.prod (.prod (.prod (.arr B) .long) (.arr .long)) B).El) =>
      ((s.1.2.dropLast, s.1.2.getLastD 0) : (Obj.prod (.arr .long) .long).El))
    (fun s hm z => by
      obtain ⟨z1, z2⟩ := z
      obtain ⟨i, -, hi⟩ := (hAs s s.1.2).2 ⟨hm, rfl⟩
      rw [rep_unsnocC _ hun, snoc_eq_iff _ _ _ 0]
      exact ⟨fun ⟨_, h⟩ => ⟨h.1, h.2⟩, fun ⟨h1, h2⟩ => ⟨⟨i, hi⟩, h1, h2⟩⟩) hu
  have hA := fnOn_outr hU
  have hA' := fnOn_outl hU
  have hDR := fnOn_dom (fnOn_compK 2 hA ha2) hdr
  have hND := fnOn_diff (fnOn_dom hU hdu) hDR hnd
  have hKP := fnOn_dom (fnOn_compK 0 hC hc0) hkp
  have hKK := fnOn_comp hND (fun s _ => hKP s) hkk
  have hNK := fnOn_diff hND hKP hnk
  have hKS := fnOn_snoc (fnOn_pair (fnOn_comp hKK (fun s _ => hO s) hko) hX hkx) hks
  have hNO := fnOn_comp hNK (fun s _ => hO s) hno
  -- the non-drop states, `ND`, and `o'` on them
  have hO' := fnOn_union_if
    (P := fun (s : (Obj.prod (.prod (.prod (.arr B) .long) (.arr .long)) B).El) =>
      (rep D s s ∧ s.1.2 ≠ []) ∧ s.1.2.getLastD 0 ≠ 2)
    (Q := fun (s : (Obj.prod (.prod (.prod (.arr B) .long) (.arr .long)) B).El) => s.1.1.2 = 0) (fnOn_congr hKS fun s => by grind) (fnOn_congr hNO fun s => by grind) ho'
  have hR1 := fnOn_pair (fnOn_pair hO' (fnOn_comp hND (fun s _ => hA s) hna) hoa)
    (fnOn_comp hND (fun s _ => hA' s) hna') hr1
  have hR2 := fnOn_pair (fnOn_comp hDR (fun s _ => hOC s) hdoc) (fnOn_comp hDR (fun s _ => hA' s) hda') hr2
  exact fnOn_union_if
    (Q := fun (s : (Obj.prod (.prod (.prod (.arr B) .long) (.arr .long)) B).El) => s.1.2.getLastD 0 ≠ 2)
    (fnOn_congr hR1 fun s => by grind)
    (fnOn_congr hR2 fun s => by grind) hbody

/-- **`thinAC`'s step on a coreflexive `D`, read back under its bit**: `thin_cases_set` for the three cases, each
    output piece read back by its twin's lemma. `hq` is the test's own spec: where `q`'s bit is set, `q` on a
    coreflexive keeps the pairs of it `le` holds of. -/
theorem thinAC_rep {B : Obj}
    (q : Tab (.prod B B) (.prod B B) → Tab (.prod B B) (.prod B B) × Bool) (le : B.El → B.El → Bool)
    (hq : ∀ (D : Tab (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep D = corefl (α := (Obj.prod B B).El) S → (q D).2 = true →
      ∀ a b, S (a, b) → ((∃ c, rep (q D).1 (a, b) c) ↔ le a b = true))
    (D : Tab (.prod B (.prod (.arr B) (.arr .long))) (.prod B (.prod (.arr B) (.arr .long))))
    (hD : ∀ s s', rep D s s' → s = s') (hb : (thinAC q D).2 = true) :
    ∀ x (h : List B.El) (as : List Int64) v, rep (thinAC q D).1 (x, (h, as)) v ↔
      rep D (x, (h, as)) (x, (h, as)) ∧ thinAStep le (x, (h, as)) v := by
  simp only [thinAC, Bool.and_eq_true, and_assoc] at hb
  obtain ⟨hun, hu, hab, hrab, hG1, hq1, hup, hsw, hq3, hdown, hdu, hl1, hl2, hl3, hlone, hK0, hK1, hK2, hpu,
    hpa, hN, hnp, hsg, hc0, hc1, hcu, hac, hsa, ho1, hdh, hc2, hdc, hsd, ho2, hbody⟩ := hb
  -- `swapInC`'s bit, its pieces' bits
  simp only [swapInC, okbit] at hsw
  obtain ⟨⟨⟨⟨hss, hrs⟩, hG2⟩, hq2⟩, hsw⟩ := hsw
  have h0 := fnOn_self hD
  have eD : rep D = corefl (α := (Obj.prod B (.prod (.arr B) (.arr .long))).El) fun s => rep D s s :=
    Core.Rel.ext fun s s' => (fnOn_corefl (C := D) (P := fun s => rep D s s) fun s s' =>
      (h0 s s').trans ⟨fun ⟨h, e⟩ => ⟨e.symm, h⟩, fun ⟨e, h⟩ => ⟨h, e.symm⟩⟩) s s' |>.trans
        ⟨fun ⟨h, e⟩ => ⟨e.symm, h⟩, fun ⟨e, h⟩ => ⟨h, e.symm⟩⟩
  have hx := fnOn_outl h0
  have hR := fnOn_outr h0
  have hh := fnOn_outl hR
  have has := fnOn_outr hR
  have eab := (rep_ranC _ hrab).trans (dom_corefl _); have ers := (rep_ranC _ hrs).trans (dom_corefl _)
  obtain ⟨eUp, eDn, eLone⟩ := thin_cases_set le D _ eD (fun s => s.1) (fun s => s.2.1) _ hx _ hh _
    (rep_unconsC _ hun) (rep_compC _ _ hu) _ (rep_pairC _ _ hab) _ eab _
    (fun a b h => hq _ _ eab hG1 a b (by rw [eab] at h; exact h.2)) _ (rep_compC _ _ hq1)
    _ ((rep_domC _ hup).trans (dom_corefl _)) _ (rep_pairC _ _ hss) _ ers
    _ (fun a b h => hq _ _ ers hG2 b a (by rw [ers] at h; exact h.2)) _ (rep_compC _ _ hq2)
    _ ((rep_domC _ hsw).trans (dom_corefl _)) _ (rep_compC _ _ hq3) _ ((rep_domC _ hdown).trans (dom_corefl _))
    _ ((rep_domC _ hdu).trans (dom_corefl _)) _ (rep_diffC _ _ hl1) _ (rep_diffC _ _ hl2) _ (rep_diffC _ _ hl3)
    _ (rep_unionC _ _ hlone)
  have hUp := fnOn_corefl eUp
  have hDn := fnOn_corefl eDn
  have hLone := fnOn_corefl eLone
  -- a state of `D` is a key of `D`
  have hkey : ∀ s, rep D s s → ∃ i, (Tab.key D).row i = s := fun s ⟨i, hk, _⟩ => ⟨i, hk⟩
  have hNil : ∀ b, (∃ j, (nilVal B).row j = b) ↔ b = [] :=
    fun b => ⟨fun ⟨j, h⟩ => by rw [← h, nilVal_row], fun h => ⟨⟨0, by simp⟩, by rw [nilVal_row, h]⟩⟩
  -- `x` pushed or replacing: `h` becomes `[x]`; the action appended: 0 (`lone`), 1 (`up`), 2 (`down`)
  have hSG := fnOn_snoc (fnOn_pair (fnOn_top (Tab.key D) (nilVal B) ([] : List B.El) hNil hN)
    (fnOn_comp (fnOn_union hLone hUp hpu) (fun s _ => hx s) hpa) hnp) hsg
  have hC0 := fnOn_comp hLone (fun s _ => fnOn_top (B := .atom .long) (Tab.key D) (col [(0 : Int64)]) 0 (col_one_row 0) hK0 s) hc0
  have hC1 := fnOn_comp hUp (fun s _ => fnOn_top (B := .atom .long) (Tab.key D) (col [(1 : Int64)]) 1 (col_one_row 1) hK1 s) hc1
  have hC2 := fnOn_comp hDn (fun s _ => fnOn_top (B := .atom .long) (Tab.key D) (col [(2 : Int64)]) 2 (col_one_row 2) hK2 s) hc2
  have hO2 := fnOn_pair (fnOn_comp hDn (fun s _ => hh s) hdh) (fnOn_snoc (fnOn_pair has hC2 hdc) hsd) ho2
  -- `up` and `lone` are disjoint, so the action of the first branch is 0 on `lone`, else 1
  have hUL : ∀ s : (Obj.prod B (.prod (.arr B) (.arr .long))).El,
      (∃ b bs, s.2.1 = b :: bs ∧ le s.1 b = true) →
      ¬ (s.2.1 = [] ∨ ∃ b bs, s.2.1 = b :: bs ∧ le s.1 b = false ∧ le b s.1 = false) := by
    rintro s ⟨b, bs, e, hl⟩ (he | ⟨b', bs', e', hl', -⟩)
    · rw [e] at he; exact List.cons_ne_nil _ _ he
    · rw [e] at e'; obtain ⟨rfl, -⟩ := List.cons.inj e'; rw [hl] at hl'; exact Bool.noConfusion hl'
  have hCU := by
    classical
    exact fnOn_union_if
      (P := fun s : (Obj.prod B (.prod (.arr B) (.arr .long))).El =>
        (rep D s s ∧ ((s.2.1 = [] ∨ ∃ b bs, s.2.1 = b :: bs ∧ le s.1 b = false ∧ le b s.1 = false) ∨
          ∃ b bs, s.2.1 = b :: bs ∧ le s.1 b = true)) ∧ ∃ i, (Tab.key D).row i = s)
      (Q := fun s : (Obj.prod B (.prod (.arr B) (.arr .long))).El =>
        s.2.1 = [] ∨ ∃ b bs, s.2.1 = b :: bs ∧ le s.1 b = false ∧ le b s.1 = false)
      (fnOn_congr hC0 fun s => ⟨fun ⟨⟨d, l⟩, k⟩ => ⟨⟨⟨d, Or.inl l⟩, k⟩, l⟩, fun ⟨⟨⟨d, _⟩, k⟩, l⟩ => ⟨⟨d, l⟩, k⟩⟩)
      (fnOn_congr hC1 fun s => ⟨fun ⟨⟨d, u⟩, k⟩ => ⟨⟨⟨d, Or.inr u⟩, k⟩, hUL s u⟩,
        fun ⟨⟨⟨d, lu⟩, k⟩, nl⟩ => ⟨⟨d, lu.resolve_left nl⟩, k⟩⟩) hcu
  have hSA := fnOn_snoc (fnOn_pair has hCU hac) hsa
  intro x h as v
  have hk := hkey (x, (h, as))
  simp only [thinAC]
  rw [rep_unionC _ _ hbody]
  change _ ∨ _ ↔ _
  rw [rep_pairC _ _ ho1, hO2]
  obtain ⟨v1, v2⟩ := v
  change (_ ∧ _) ∨ _ ↔ _
  rw [hSG, hSA]
  by_cases hd : rep D (x, (h, as)) (x, (h, as))
  · have hi := hk hd
    rcases h with _ | ⟨b, bs⟩
    · simp [thinAStep, hd, hi]
    · cases e1 : le x b <;> cases e2 : le b x <;> simp [thinAStep, hd, hi, e1, e2]
  · simp [hd]

/-- **`thinLOn` under `thinLOnC`'s bit**: the right fold of `thinAC` (`rep_foldOnC`, each step by `thinAC_rep`)
    leaves the actions, the `loop` of `thinKC` (`rep_loopOnC`, each step by `thinKC_rep`) appends the kept elements:
    `thinTwoDen`, which `thinTwoDen_eq` makes `thinLDen`. What stays: `hq`, the test's own spec. -/
theorem rep_thinLOnC {B : Obj} {n : USize} (q : Tab (.prod B B) (.prod B B) → Tab (.prod B B) (.prod B B) × Bool)
    (le : B.El → B.El → Bool) (X : Vals (.arr B) n)
    (hq : ∀ (D : Tab (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep D = corefl (α := (Obj.prod B B).El) S → (q D).2 = true →
      ∀ a b, S (a, b) → ((∃ c, rep (q D).1 (a, b) c) ↔ le a b = true))
    (hb : (thinLOnC q X).2 = true) :
    ∀ (xs : List B.El) w, rep (thinLOnC q X).1 xs w ↔ (∃ i, X.row i = xs) ∧ thinLDen le xs w := by
  simp only [thinLOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hF, hN⟩, hC⟩, hnc⟩, hs0⟩, hP⟩, hL⟩ := hb
  have hF0 :=
    rep_foldOnC (E := B) (V := .prod (.arr B) (.arr .long)) (P := .prod B (.prod (.arr B) (.arr .long))) (m := 1) false pairC Prod.mk pairC_pt _ (thinAC q) X hF
      _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) (fun _ p w => thinAStep le p w)
      (fun _ _ _ hbi p w hp hcor => by
        obtain ⟨x, h, as⟩ := p
        simp only [demandStepC, Bool.and_eq_true] at hbi
        refine (thinAC_rep q le hq _ hcor hbi.1.2 x h as w).trans (and_iff_right ?_)
        obtain ⟨s, hs⟩ := hp; obtain rfl := hcor _ _ hs; exact hs)
  have hSeed : ∀ y, (∃ p, Vals.row (A := .prod (.arr B) (.arr .long)) (n := 1) (nilVal B, nilVal .long) p = y) ↔
      y = ([], []) := fun y =>
    ⟨fun ⟨p, h⟩ => by
      rw [← h]; show (Vals.row (nilVal B) p, Vals.row (nilVal .long) p) = _; rw [nilVal_row, nilVal_row],
     fun h => ⟨⟨0, by simp⟩, by
      rw [h]; show (Vals.row (nilVal B) _, Vals.row (nilVal .long) _) = _; rw [nilVal_row, nilVal_row]⟩⟩
  -- `rep_foldOnC`'s right side is `IxChain` up to `ordL false xs ≡ xs` and the seed, which `hSeed` reads
  have hFold : ∀ xs w, rep (foldOnC false pairC ((nilVal B, nilVal .long) : Vals (.prod (.arr B) (.arr .long)) 1)
      (thinAC q) X).1 xs w ↔ (∃ i, X.row i = xs) ∧
        IxChain (fun x v w => thinAStep le (x, v) w) (· = ([], [])) xs w := fun xs w =>
    (hF0 xs w).trans (and_congr_right fun _ =>
      ⟨fun ⟨ys, hy, h0, hs, hw⟩ => by unfold IxChain; exact ⟨ys, hy, (hSeed _).1 h0, hs, hw⟩,
       fun h => by obtain ⟨ys, hy, h0, hs, hw⟩ := h; exact ⟨ys, hy, (hSeed _).2 h0, hs, hw⟩⟩)
  have hNil : ∀ b, (∃ j, (nilVal B).row j = b) ↔ b = [] :=
    fun b => ⟨fun ⟨j, h⟩ => by rw [← h, nilVal_row], fun h => ⟨⟨0, by simp⟩, by rw [nilVal_row, h]⟩⟩
  have hNC := fnOn_pair (fnOn_top X (nilVal B) ([] : List B.El) hNil hN)
    (fnOn_top (B := .atom .long) X (col [(0 : Int64)]) 0 (col_one_row 0) hC) hnc
  have hLoop := rep_loopOnC thinKC _ hL (fun s v => s.1.2 ≠ [] ∧ v = thinK s)
    (fun D S hD hb cy c' hS => by
      have hDc : rep D cy cy := by rw [hD]; exact ⟨rfl, hS⟩
      rw [thinKC_rep D (fun s s' h => by rw [hD] at h; exact h.1) hb cy c']
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hDc, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩)
  intro xs w
  simp only [thinLOnC]
  rw [← thinTwoDen_eq]
  constructor
  · intro hw
    obtain ⟨z, hz⟩ := (outl_holds _ _ _).1 hw
    obtain ⟨z', hz'⟩ := (outl_holds _ _ _).1 hz
    obtain ⟨⟨c01, as⟩, ys, hPk, g, hg0, hgs, hc⟩ := (hLoop _ _).1 hz'
    rw [rep_pairC _ _ hP] at hPk
    obtain ⟨hs0k, hid⟩ := hPk
    rw [rep_idU] at hid
    obtain ⟨rfl, hX⟩ := hid
    rw [rep_pairC _ _ hs0] at hs0k
    obtain ⟨hnck, hask⟩ := hs0k
    obtain ⟨-, hc01⟩ := (hNC _ _).1 hnck
    obtain ⟨h, hFk⟩ := (outr_holds _ _ _).1 hask
    obtain ⟨-, hA⟩ := (hFold _ _).1 hFk
    exact ⟨hX, (h, as), hA, _, ⟨g, by rw [hg0, show c01 = ([], 0) from hc01], hgs, hc⟩, rfl⟩
  · rintro ⟨hX, ⟨h, as⟩, hA, ⟨⟨w', z⟩, z'⟩, ⟨g, hg0, hgs, hc⟩, rfl⟩
    refine (outl_holds _ _ _).2 ⟨z, (outl_holds _ _ _).2 ⟨z', (hLoop _ _).2 ⟨(([], 0), as), xs, ?_, g, hg0, hgs, hc⟩⟩⟩
    rw [rep_pairC _ _ hP]
    refine ⟨?_, by rw [rep_idU]; exact ⟨rfl, hX⟩⟩
    rw [rep_pairC _ _ hs0]
    exact ⟨(hNC _ _).2 ⟨⟨hX, hX⟩, rfl⟩, (outr_holds _ _ _).2 ⟨h, (hFold _ _).2 ⟨hX, hA⟩⟩⟩

#print axioms thinTwoDen_eq
#print axioms rep_thinLOnC

end Rep

namespace CRel

open Rel Rel.Kernel Rel.Alg Rel.Rep FoldN
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **`CRel.thinLOn` read back under its bit**: `rep_thinLOnC`. -/
theorem rep_thinLOn {B : Obj} {n : USize} (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B))
    (le : B.El → B.El → Bool) (X : Vals (.arr B) n)
    (hq : ∀ (D : Tab (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep D = corefl (α := (Obj.prod B B).El) S → (q (some D)).ok = true →
      ∀ a b, S (a, b) → ((∃ c, rep (q (some D)).rel (a, b) c) ↔ le a b = true))
    (hb : (thinLOn q X).ok = true) :
    ∀ (xs : List B.El) w, rep (thinLOn q X).rel xs w ↔ (∃ i, X.row i = xs) ∧ thinLDen le xs w :=
  by unfold CRel.thinLOn at hb ⊢; rw [rep_ofC hb]; exact rep_thinLOnC _ le X hq (ofC_ok hb).1

#print axioms rep_thinLOn

end CRel

end Rel
