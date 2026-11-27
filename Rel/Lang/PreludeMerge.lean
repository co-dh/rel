module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeDfn
public import Rel.Lang.PreludeConcat
public import Rel.Lang.PreludeLoop
public import Rel.Lang.PreludeOrd
public import Rel.Programs.Prelude

@[expose] public section

/-! `merge(Q) ≜ ⟨⟨𝟙, nil⟩, cat⟩ loop(π₁ (l …)) π₂` (`Programs/Prelude.lean`) means the row `merge`'s `rowDens` term,
    `List.merge` by `Q`'s test (B10b, architecture §4 "merge(Q)"): the state is `((xs, ys), acc)`, the clock `cat(x, y)`
    gives `|x| + |y|` rounds, each moves the head of `xs` (when `a Q b` or `ys` is empty) or of `ys` onto `acc`.
    The loop's step is `mstep`; after `t` rounds `acc ++ merge xs ys = merge x y` and `|xs| + |ys| = |x| + |y| - t`
    (`mstep_inv`), so the final state has empty lists and `acc = merge x y` (`loopDen_merge`). -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- One round of the merge loop on `((xs, ys), acc)`: the head of `xs` when it is `le`-before the head of `ys` or `ys`
    is empty, else the head of `ys`. -/
def mstep {α : Type} (le : α → α → Bool) : (List α × List α) × List α → (List α × List α) × List α
  | ((a :: xs, b :: ys), acc) => if le a b then ((xs, b :: ys), acc ++ [a]) else ((a :: xs, ys), acc ++ [b])
  | ((a :: xs, []), acc) => ((xs, []), acc ++ [a])
  | (([], b :: ys), acc) => (([], ys), acc ++ [b])
  | s => s

/-- A round keeps `acc ++ merge xs ys` and takes one element off the lists. -/
theorem mstep_inv {α : Type} (le : α → α → Bool) (s : (List α × List α) × List α) (h : s.1.1 ≠ [] ∨ s.1.2 ≠ []) :
    (mstep le s).2 ++ List.merge (mstep le s).1.1 (mstep le s).1.2 le = s.2 ++ List.merge s.1.1 s.1.2 le ∧
      (mstep le s).1.1.length + (mstep le s).1.2.length + 1 = s.1.1.length + s.1.2.length := by
  obtain ⟨⟨xs, ys⟩, acc⟩ := s
  rcases xs with _ | ⟨a, xs⟩ <;> rcases ys with _ | ⟨b, ys⟩
  · simp at h
  · simp [mstep]
  · simp [mstep]
  · by_cases hab : le a b <;> simp [mstep, hab] <;> omega

/-- `mstep` run `t` times. -/
def miter {α : Type} (le : α → α → Bool) : Nat → (List α × List α) × List α → (List α × List α) × List α
  | 0, s => s
  | t + 1, s => mstep le (miter le t s)

/-- After `t ≤ n` rounds from `((x, y), [])`, `n = |x| + |y|`: the invariant of `mstep_inv`. -/
theorem mstep_iter {α : Type} (le : α → α → Bool) (x y : List α) (t : Nat) (ht : t ≤ x.length + y.length) :
    (miter le t ((x, y), [])).2 ++ List.merge (miter le t ((x, y), [])).1.1 (miter le t ((x, y), [])).1.2 le =
        List.merge x y le ∧
      (miter le t ((x, y), [])).1.1.length + (miter le t ((x, y), [])).1.2.length = x.length + y.length - t := by
  induction t with
  | zero => simp [miter]
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (miter le t ((x, y), [])).1.1 ≠ [] ∨ (miter le t ((x, y), [])).1.2 ≠ [] := by
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, ne_eq, not_not] at hc
      simp [hc.1, hc.2] at h2
      omega
    obtain ⟨h3, h4⟩ := mstep_inv le _ hne
    rw [miter]
    exact ⟨h3.trans h1, by omega⟩

/-- The loop with step `T = mstep` (on non-final states) from `((x, y), [])` clocked by `x ++ y` ends at `merge x y`. -/
theorem loopDen_merge {B : Obj} (le : B.El → B.El → Bool)
    (T : Core.Rel (Obj.El (.prod (.prod (.prod (.arr B) (.arr B)) (.arr B)) B))
      (Obj.El (.prod (.prod (.arr B) (.arr B)) (.arr B))))
    (hT : ∀ s e w, T (s, e) w ↔ (s.1.1 ≠ [] ∨ s.1.2 ≠ []) ∧ w = mstep le s) (x y : List B.El) (c) :
    loopDen T (((x, y), []), x ++ y) c ↔ c = (([], []), List.merge x y le) := by
  rw [loopDen_iff]
  have hlen : (x ++ y).length = x.length + y.length := List.length_append
  constructor
  · rintro ⟨g, hg0, hg, rfl⟩
    have hgi : ∀ t, t ≤ x.length + y.length → g t = miter le t ((x, y), []) := by
      intro t
      induction t with
      | zero => intro _; exact hg0
      | succ t ih =>
        intro ht
        have := (hT _ _ _).1 (hg t (by simp only [hlen]; omega))
        rw [this.2, ih (by omega)]; rfl
    simp only [hlen]
    obtain ⟨h1, h2⟩ := mstep_iter le x y _ (Nat.le_refl _)
    rw [← hgi _ (Nat.le_refl _)] at h1 h2
    have e1 : (g (x.length + y.length)).1.1 = [] := List.length_eq_zero_iff.1 (by omega)
    have e2 : (g (x.length + y.length)).1.2 = [] := List.length_eq_zero_iff.1 (by omega)
    rw [e1, e2] at h1
    simp only [List.nil_merge, List.append_nil] at h1
    exact Prod.ext (Prod.ext e1 e2) h1
  · rintro rfl
    refine ⟨fun t => miter le t ((x, y), []), rfl, fun t ht => ?_, ?_⟩
    · have ht' : t < x.length + y.length := by simpa [hlen] using ht
      obtain ⟨h1, h2⟩ := mstep_iter le x y t (Nat.le_of_lt ht')
      refine (hT _ _ _).2 ⟨?_, rfl⟩
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, ne_eq, not_not] at hc
      simp [hc.1, hc.2] at h2
      omega
    · simp only [hlen]
      obtain ⟨h1, h2⟩ := mstep_iter le x y _ (Nat.le_refl _)
      generalize miter le (x.length + y.length) ((x, y), []) = s at h1 h2 ⊢
      obtain ⟨⟨xs, ys⟩, acc⟩ := s
      simp only [Nat.sub_self, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [List.nil_merge, List.append_nil] at h1
      simp [h1]

theorem Prim.den_merge {B : Obj} (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) :
    Prim.den (rowOf "merge") (.prod (.arr B) (.arr B)) (.arr B) [⟨.prod B B, .prod B B, T⟩] =
      fun p ys => ys = List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b)) := by
  have hs : (rowOf "merge").sig = ([((.var {} "B", .var {} "B"), some true)],
      .prod (.list (.var {} "B")) (.list (.var {} "B")), .list (.var {} "B")) := rfl
  have ho : (rowOf "merge").objs (.prod (.arr B) (.arr B)) (.arr B) [(.prod B B, .prod B B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "merge").sym) = some ⟨RowCode.merge, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
        graph fun p => List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `at(0)` as the prelude elaborates it: `Tm.at0` with the one-row table `{(0, 0)}` of `i64` for `0`. -/
def Tm.headAt {B : Obj} : Tm (.arr B) B :=
  .comp (.pair .id (.top (.val (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1)
    (Gen.atom .i64 (USize.ofNat 1) ["0000000000000000000000000000000000000000000000000000000000000000", "000000000000008001000000000000000a0000000000000000"] [])
    (Gen.atom .i64 (USize.ofNat 1) ["0000000000000000000000000000000000000000000000000000000000000000", "000000000000008001000000000000000a0000000000000000"] [])).1)))
    (.prim indexRow)

/-- The prelude's `tail`, `cat° dom(π₁ (at(0)τ ∩ 𝟙))π₂`, as a call. -/
def Tm.tailCall (B : Obj) (os : List Obj := [B]) : Tm (.arr B) (.arr B) :=
  .call [] `Rel.Programs.prelude.tail (some `Rel.Programs.prelude.tail.conv) os
    (.comp (.comp (.prim (rowOf "uncat")) (.dom (.comp .outl (.meet (.comp (Tm.headAt (B := B)) (.prim (rowOf "τ"))) .id)))) .outr)

theorem Tm.headAt_den (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (b : Obj.El B) :
    (Tm.headAt (B := B)).den ρ xs b ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  rw [← Tm.at0_den ρ xs b]
  have hz := Tm.zeroLit_den ρ
  simp only [Tm.den] at hz
  simp only [Tm.headAt, Tm.at0, Tm.den, Gen.atom_zero, hz]

theorem Tm.tailCall_den (ρ : Val) {B : Obj} {os : List Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.tailCall B os).den ρ xs ys ↔ ∃ a, xs = a :: ys := by
  simp only [Tm.tailCall, Tm.den, Val.args, Tm.dom_den, Prim.den_uncat, Prim.den_tau, Core.Rel.comp, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.graph, Core.Rel.id, Tm.headAt_den, exists_eq_left]
  constructor
  · rintro ⟨b, ⟨b1, hx, rfl, b2, ⟨⟨b', -, hb2⟩, hfst⟩, -⟩, rfl⟩
    exact ⟨b', by rw [hx, hfst, hb2]; rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨([a], ys), ⟨([a], ys), rfl, rfl, [a], ⟨⟨a, ⟨by simp, rfl⟩, rfl⟩, rfl⟩, ⟨a, ⟨by simp, rfl⟩, rfl⟩, rfl⟩, rfl⟩

set_option hygiene false in
/-- The merge loop's state `((xs, ys), acc)`. -/
local notation "𝕊" => Obj.prod (Obj.prod (Obj.arr B) (Obj.arr B)) (Obj.arr B)

/-- `merge(Q)` as the prelude elaborates it: the calls `a`, `b`, `l` of its `where` around the clocked `loop`, the
    state `S = ((xs, ys), acc)`; `.var 6 : S ⟶ S` is `l`, `.var 2`, `.var 3 : S ⟶ B` are `a`, `b`, `.var 1` is `Q`. -/
def Tm.mergeDef {B : Obj} (Q : Tm B B) : Tm (.prod (.arr B) (.arr B)) (.arr B) :=
  .arg (.arg (.call [2, 1] `a none [] (.arg (.arg (.arg (.call [3, 2, 1] `b none []
      (.arg (.arg (.arg (.arg (.call [6, 3, 2, 1] `l none []
        (.comp (.comp (.pair (.pair .id Tm.nil) (.prim (rowOf "cat")) : Tm (.prod (.arr B) (.arr B)) (.prod 𝕊 (.arr B))) (.arg (.prim (rowOf "loop") : Tm (.prod 𝕊 (.arr B)) 𝕊)
          (.comp (.outl : Tm (.prod 𝕊 B) 𝕊) (.join
            (.comp (.var 6 : Tm 𝕊 𝕊)
              (.pair (.pair (.comp (.comp .outl .outl) (Tm.tailCall B)) (.comp .outl .outr))
                (.comp (.pair .outr (.var 2 : Tm 𝕊 B)) (.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B)))))
            (.comp (.diff .id (.var 6))
              (.pair (.pair (.comp .outl .outl) (.comp (.comp .outl .outr) (Tm.tailCall B)))
                (.comp (.pair .outr (.var 3 : Tm 𝕊 B)) (.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B))))))))) .outr))
        (.join (.dom (.comp (.pair (.var 2 : Tm 𝕊 B) (.var 3))
            (.arg (.call [2] `Rel.Programs.prelude.cor (some `Rel.Programs.prelude.cor.conv) [B, B]
              (.dom (.meet (.comp .outl (.var 2 : Tm B B)) .outr))) (.var 1 : Tm B B))))
          (.diff (.dom (.var 2 : Tm 𝕊 B))
            (.dom (.var 3 : Tm 𝕊 B)))))
        (.var 3 : Tm 𝕊 B)) (.var 2 : Tm 𝕊 B))
        (.var 1 : Tm B B)))
      (.comp (.comp .outl .outr) Tm.headAt : Tm 𝕊 B))
      (.var 2 : Tm 𝕊 B)) (.var 1 : Tm B B)))
    (.comp (.comp .outl .outl) Tm.headAt : Tm 𝕊 B)) Q

theorem Tm.mergeDef_row (ρ : Val) {B : Obj} (Q : Tm B B) (p : (Obj.prod (Obj.arr B) (Obj.arr B)).El)
    (ys : (Obj.arr B).El) :
    (Tm.mergeDef Q).den ρ p ys ↔ (Tm.arg (.prim (rowOf "merge")) (pairTest Q)).den ρ p ys := by
  have hτ := Tm.pairTest_den ρ Q
  have hnil : ∀ x (l : (Obj.arr B).El), (nilDen : Core.Rel (Obj.El (.prod (.arr B) (.arr B))) _) x l ↔ l = [] :=
    fun x l => by
      simp [nilDen, Core.Rel.graph]
  -- the clocked loop from `((x, y), [])` over `x ++ y`, then `π₂`, is `merge x y` for any step that is `mstep`
  have outer : ∀ (T : Core.Rel (Obj.El (.prod 𝕊 B)) (Obj.El 𝕊)) (le : B.El → B.El → Bool),
      (∀ s e w, T (s, e) w ↔ (s.1.1 ≠ [] ∨ s.1.2 ≠ []) ∧ w = mstep le s) →
      ((((((𝟙 _).rpair nilDen).rpair fun (q : (Obj.prod (.arr B) (.arr B)).El) (zs : (Obj.arr B).El) => zs = q.1 ++ q.2) ≫ loopDen T) ≫ graph Prod.snd) p ys ↔
        ys = List.merge p.1 p.2 le) := by
    intro T le hT
    obtain ⟨x, y⟩ := p
    have hl := loopDen_merge le T hT x y
    generalize loopDen T = L at hl ⊢
    simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id, hnil, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, c, ⟨a1, b2, b3, b4, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, h⟩, rfl⟩
      exact (Prod.mk.inj ((hl _).1 h)).2
    · rintro rfl; exact ⟨[], [], _, ⟨x, y, [], x ++ y, ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, (hl _).2 rfl⟩, rfl⟩
  simp only [Tm.mergeDef, Tm.den, Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, and_self,
    Prim.den_loopRow, Prim.den_merge, ↓reduceDIte, Tm.nil, Prim.den_nilRow, Prim.den_cat, hτ]
  refine outer _ _ fun s e w => ?_
  have hd : ∀ ρ' (xs : (Obj.arr B).El) b, (Tm.headAt (B := B)).den ρ' xs b ↔ xs.head? = some b := fun ρ' xs b => by
    rw [Tm.headAt_den]; cases xs <;> simp [eq_comm]
  obtain ⟨⟨xs, zs⟩, acc⟩ := s
  simp only [Core.Rel.comp, Core.Rel.union, Core.Rel.diff, Core.Rel.inter, Core.Rel.id, Core.Rel.graph,
    Core.Rel.rpair, Core.Rel.recip, Prim.den_snoc, hd, Tm.tailCall_den, Tm.dom_den, Tm.den,
    Tm.argDen, Val.args, Val.bind, Val.empty, Nat.reduceEqDiff, reduceIte, ↓reduceDIte, and_self]
  rcases xs with _ | ⟨a, xs⟩ <;> rcases zs with _ | ⟨b, zs⟩ <;>
    simp only [mstep, exists_eq_left, exists_eq_left', exists_and_left,
      true_and, Prod.exists, Prod.mk.injEq, ne_eq,
      reduceCtorEq, not_true_eq_false, not_false_eq_true, or_false, false_or, false_and, and_false, exists_false,
      List.cons.injEq, decide_eq_true_eq, or_true,
      and_assoc, List.head?_nil, List.head?_cons, Option.some.injEq, or_and_right, exists_or,
      not_and, forall_exists_index, forall_eq', and_self]
  all_goals obtain ⟨⟨w1, w2⟩, w3⟩ := w
  · simp [eq_comm, and_assoc]
  · simp [eq_comm, and_assoc]
  · have e : (∃ c, Tm.den ρ Q a c ∧ c = b ∧ Tm.den ρ Q a c ∧ c = b) ↔ Tm.den ρ Q a b :=
      ⟨fun ⟨_, h, hc, _⟩ => hc ▸ h, fun h => ⟨b, h, rfl, h, rfl⟩⟩
    simp only [e]
    by_cases hq : Tm.den ρ Q a b <;> simp [hq, eq_comm, and_assoc]

/-- **`merge`'s text means the row** (Q3 = H), as `Tm.estDef_den`: `prelude.merge.body` at `α = general`, parameter
    `Q` the variable 1, means `merge(τ(Q))` at any objects `σ`. -/
theorem Tm.mergeDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm (Obj.prod (Obj.arr ((Obj.atom .general).inst ph σ)) (Obj.arr ((Obj.atom .general).inst ph σ)))
      (Obj.arr ((Obj.atom .general).inst ph σ))}
    (ht : Rel.Programs.prelude.merge.body.instObj ph σ = .ok t') (p ys) :
    t'.den ρ p ys ↔ (Tm.arg (.prim (rowOf "merge"))
      (pairTest (.var 1 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)))).den ρ p ys := by
  obtain rfl : Tm.mergeDef (.var 1) = t' := Except.ok.inj ht
  exact Tm.mergeDef_row ρ _ p ys

end Rel.Lang
