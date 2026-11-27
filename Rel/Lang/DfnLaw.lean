module

public import Rel.Lang.GenKFold
public import Rel.RepTabArith
public import Rel.KernelSpec.Elementwise
public import Rel.Run.Lang.Elab
import all Init.Data.Array.Basic

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! A row with a `prelude` text is the text's fused form (§4). The `.prim` rule of `build`: no `q` → the row; no
    universe (unbounded) → the row; an initial segment `0…k` or an `r.native` atom → `Prim.cut`, the row followed by
    `𝟙` of the target; any other object or atom → the text `build δ q` (`Pre.textAt`). `Tm.<sym>Def_den` proves each
    means the text, from one fact (`chain_in`): a fold from `0` whose step never decreases the value leaves `0…k`
    only at its result. At any other universe the text runs: there a partial sum or count may leave the object
    while the result is in it. -/

namespace Rel.Lang

open Rel.Kernel
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `P` an initial segment `0…k` of ℕ: no number in it is negative, and with a number every smaller one down to `0`
    is in it. -/
def InitSeg (P : Int64 → Prop) : Prop :=
  (∀ x, P x → 0 ≤ x.toInt) ∧ ∀ x y, P x → 0 ≤ y.toInt → y.toInt ≤ x.toInt → P y

/-- `P` an initial segment `0…k` of ℕ at the object `B`: `InitSeg` at `i64`, the atom ℕ is stored at; none elsewhere. -/
def Seg : (B : Obj) → (B.El → Prop) → Prop
  | .atom .i64, P => InitSeg P
  | _, _ => False

/-- A source every run holds: a list of fewer than `2^63` elements (a list cell is two `Int64` offsets). -/
def Short : (A : Obj) → A.El → Prop
  | .arr _, xs => xs.length < 2 ^ 63
  | _, _ => True

/-- **A chain from `0` that never decreases stays in `P` iff its end does**, `P` every number or an initial
    segment: every value lies between `0` and the end. -/
theorem chain_in {P : Int64 → Prop} (hP : (∀ x, P x) ∨ InitSeg P) (g : Nat → Int64) (n : Nat)
    (hg : InitSeg P → 0 ≤ (g 0).toInt ∧ ∀ t < n, (g t).toInt ≤ (g (t + 1)).toInt) :
    (∀ t ≤ n, P (g t)) ↔ P (g n) := by
  refine ⟨fun h => h n (Nat.le_refl _), fun hn t ht => ?_⟩
  rcases hP with hP | hP
  · exact hP _
  obtain ⟨h0, hm⟩ := hg hP
  have up : ∀ s, s ≤ n → ∀ t ≤ s, (g t).toInt ≤ (g s).toInt := by
    intro s
    induction s with
    | zero => intro _ t ht; rw [Nat.le_zero.1 ht]; exact Int.le_refl _
    | succ s ih =>
      intro hs t ht
      rcases Nat.lt_or_eq_of_le ht with ht | rfl
      · exact Int.le_trans (ih (by omega) t (by omega)) (hm s (by omega))
      · exact Int.le_refl _
  exact hP.2 _ _ hn (Int.le_trans h0 (up t ht 0 (Nat.zero_le _))) (up n (Nat.le_refl _) t ht)

/-- `zeroCol t` holds `t`'s word `0`. -/
theorem zeroCol_row {t : QAtomicType} (h : t.ordNum.isSome) (i : Fin (1 : USize).toNat) :
    ValsB.row (o := false) (A := .atom t) (zeroCol t h) i =QAtomicType.ofBits t 0 := by
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> first | exact ⟨_, rfl⟩ | exact absurd h (by decide)
  have hu : t ≠ .u1 := by rintro rfl; exact absurd h (by decide)
  have h0 := (Rel.Verify.wordsFoR_closed #[(0 : UInt64)] (n := 1) (by simp)).2.1
  have hi : i.1 = 0 := by have := i.2; simp at this; omega
  rw [Vals.row_atom, Arr.get_word _ h]
  congr 1
  simp only [zeroCol, Arr.mk, Arr.enc, wordsFoR] at h0 ⊢
  rw [Rel.Verify.raw_foR .i64 8 rfl (by decide)] at h0
  rw [Rel.Verify.raw_foR t w hw hu]
  generalize Column.foRBits _ _ _ = f at h0 ⊢
  have hf : f 0 = 0 := by
    have := congrArg (·[0]?) h0
    simpa [Rel.Verify.ofNat_toNat_mod64] using this
  simp [hi, hf]

/-! ### Generated literals: what `Gen` rebuilds a table or a universe literal of a body into -/

/-- `Enc.wf?` answers `some` wherever `Enc.WF` holds, but on a `u1` block whose frame or width admits a 2
    (`Column.u1Ok`), which it refuses. -/
theorem _root_.Rel.Enc.wf?_isSome {t : QAtomicType} {n : USize} {e : Enc}
    (h : Enc.WF t n e) (hu : ∀ md pk, e = .foR md pk → t = .u1 → Column.u1Ok md pk = true) :
    (Enc.wf? t n e).isSome := by
  cases e with
  | foR md pk => cases t <;> (unfold Enc.wf?; dsimp only; rw [dif_pos ⟨h.1, hu md pk rfl, h.2.2⟩]; rfl)
  | pos => cases t <;> first | rfl | (simp [Enc.WF] at h)

/-- A generated atom literal (`Gen.atom`) is the column its payload encodes, its bit `true`, wherever that payload is
    `WF` and holds no null (`Enc.wf?_isSome`). -/
theorem Gen.atom_eq {t : QAtomicType} {n : USize} {m p : List String} {e : Enc}
    (he : Enc.foR (Gen.unhex m) (Gen.unhex p) = e) (hw : Enc.WF t n e)
    (hu : ∀ md pk, e = .foR md pk → t = .u1 → Column.u1Ok md pk = true) (hN : hasNul e = false)
    (ht : t.width.isSome = true) :
    Gen.atom t n m p ht = (Arr.mk e hw hN, true) := by
  subst he
  obtain ⟨⟨w⟩, hs⟩ := Option.isSome_iff_exists.1 (Enc.wf?_isSome hw hu)
  unfold Gen.atom; dsimp only; rw [hs]; simp only [hN, dite_true]

/-- **The size of `Gen.unhex ss`** is half the chunks' UTF-8 lengths, summed: the linear form of a pack-size premise. -/
theorem Gen.unhex_size (ss : List String) : (Gen.unhex ss).size = (ss.map fun s => s.utf8ByteSize / 2).sum := by
  have h := congrArg List.length (Gen.unhex_toList ss)
  rw [ByteArray.size, ← Array.length_toList, h, List.length_flatMap]
  simp [← String.toByteArray_ofList, String.ofList_toList, Function.comp_def]

-- `maxRecDepth`: the literal's 114 digits and `Coc.encode` of one word unfold past the default depth
set_option maxRecDepth 100000 in
/-- **The literal `0`** of a body, as `Expand.atomE` writes `zeroCol .i64`, is `zeroCol .i64`: both payloads evaluate,
    the literal's by `Gen.unhex_toList`, `wordsFoR #[0]` by unfolding (`Array.range` read through `import all`). -/
theorem Gen.atom_zero : Gen.atom .i64 (USize.ofNat 1)
    ["0000000000000000000000000000000000000000000000000000000000000000", "000000000000008001000000000000000a0000000000000000"]
    [] = (zeroCol .i64 rfl, true) := by
  have hb : ∀ {a b : ByteArray}, a.data.toList = b.data.toList → a = b := fun {a b} h => by
    cases a; cases b; simp_all
  have he : Enc.foR (Gen.unhex
      ["0000000000000000000000000000000000000000000000000000000000000000", "000000000000008001000000000000000a0000000000000000"])
      (Gen.unhex []) = wordsFoR #[0] := by
    unfold wordsFoR
    congr 1 <;> apply hb <;> rw [Gen.unhex_toList] <;> with_unfolding_all rfl
  exact Gen.atom_eq (n := USize.ofNat 1) he (zeroCol .i64 rfl).wf (fun _ _ _ h => absurd h (by decide))
    (zeroCol .i64 rfl).plain (by decide)

/-- A table literal (`Gen.relV`) means its rows (`Tab.Holds`). -/
theorem Tm.relV_den (ρ : Val) {A B : Obj} {n : USize} (k : Vals A n × Bool) (v : Vals B n × Bool) (x : A.El)
    (y : B.El) : (Tm.val (Gen.relV A B n k v).1).den ρ x y ↔ ∃ i, k.1.row i = x ∧ v.1.row i = y := Iff.rfl

/-- The base `0`, `ran(u₀ {0})` of the literal zero `zeroCol`: its values are the word `0` of the atom, where it is in
    its universe. -/
theorem ranZeroCol_den {t : QAtomicType} (h : t.ordNum.isSome) (u₀ : Tm (.atom t) (.atom t)) (ρ : Val)
    {P : (Obj.atom t).El → Prop} (hU : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (v : (Obj.atom t).El) :
    (∃ a, (Tm.ran (.comp u₀ (.uni (A := .atom t) (zeroCol t h)))).den ρ a v) ↔
      v = QAtomicType.ofBits t 0 ∧ P (QAtomicType.ofBits t 0) := by
  simp only [↓Tm.ran_den, Tm.ran_den, Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, hU,
    zeroCol_row]
  constructor
  · rintro ⟨a, rfl, b, ⟨_, ⟨rfl, hb⟩, _, rfl, -⟩, _, -, _, -, hv⟩
    exact ⟨hv, hb⟩
  · rintro ⟨rfl, h0⟩
    exact ⟨_, rfl, _, ⟨_, ⟨rfl, h0⟩, ⟨0, by simp⟩, rfl, rfl⟩, _, ⟨rfl, h0⟩, ⟨0, by simp⟩, rfl, rfl⟩

/-- `Int64`'s `+` with no null and no wrap: the integer sum. -/
theorem stepDen_add_iff (x v w : Int64) : stepDen Ew.add (x, v) w ↔
    x ≠ Alg.nul ∧ v ≠ Alg.nul ∧ -2 ^ 63 < x.toInt + v.toInt ∧ x.toInt + v.toInt < 2 ^ 63 ∧ w = x + v := by
  have hx1 := Int64.le_toInt x; have hx2 := Int64.toInt_lt x
  have hv1 := Int64.le_toInt v; have hv2 := Int64.toInt_lt v
  have hnul : Alg.nul.toInt = -2 ^ 63 := by decide
  have hs := Int64.toInt_add x v
  have hne : ∀ y : Int64, y ≠ Alg.nul ↔ y.toInt ≠ -2 ^ 63 := fun y =>
    ⟨fun h e => h (Int64.toInt_inj.1 (by rw [e, hnul])), fun h e => h (by rw [e, hnul])⟩
  rw [stepDen_iff]
  simp only [Rel.Verify.Ew.intStep_add, show (Ew.add == Ew.add) = true from rfl, if_true]
  constructor
  · rintro ⟨hw, hn, ho⟩
    by_cases hxn : x = Alg.nul ∨ v = Alg.nul
    · rw [if_pos hxn] at hw; exact absurd hw hn
    rw [if_neg hxn] at hw; subst hw
    obtain ⟨hxn, hvn⟩ := not_or.1 hxn
    rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le] at ho
    have h0 : (0 : Int64).toInt = 0 := rfl
    rw [h0] at ho
    have hwn := (hne _).1 hn
    have hxi := (hne _).1 hxn
    have hvi := (hne _).1 hvn
    rw [hs] at ho hwn
    refine ⟨hxn, hvn, ?_, ?_, rfl⟩ <;> by_cases hv0 : 0 ≤ v.toInt
    all_goals
      first
        | (have := ho.1 hv0; simp only [Int.bmod] at this hwn; split at this <;> omega)
        | (have := mt ho.2 hv0; simp only [Int.bmod] at this hwn; split at this <;> omega)
  · rintro ⟨hxn, hvn, hl, hu, rfl⟩
    have h0 : (0 : Int64).toInt = 0 := rfl
    rw [if_neg (not_or.2 ⟨hxn, hvn⟩)]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hne, hs]; simp only [Int.bmod]; split <;> omega
    · rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, hs, h0]; simp only [Int.bmod]
      split <;> exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- The definition `⦇[0, π₁ succ]⦈` of `length` on `TU`, its base `Te` the value `0`: the counts `0…n` all in `TU`,
    the result `n`. -/
theorem count_iff {E : Obj} {Te TU : Core.Rel (Obj.El .long) (Obj.El .long)} {P : Int64 → Prop}
    (he : ∀ v, (∃ a, Te a v) ↔ v = 0 ∧ P 0) (hU : ∀ x y, TU x y ↔ x = y ∧ P x)
    (xs : List E.El) (hn : xs.length < 2 ^ 63) (w : Int64) :
    foldDen (E := E) (V := .long) Te (graph Prod.fst ≫ succDen TU) xs w ↔
      (∀ t ≤ xs.length, P (Int64.ofNat t)) ∧ w = Int64.ofNat xs.length := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  have step : ∀ t, t + 1 < 2 ^ 63 →
      Ew.intStep Ew.add Alg.nul (Int64.ofNat t) 1 = Int64.ofNat (t + 1) := fun t ht => by
    have hnt : Int64.ofNat t ≠ Alg.nul := fun e => by
      have := congrArg Int64.toInt e
      rw [Int64.toInt_ofNat_of_lt (by omega), show Alg.nul.toInt = -2 ^ 63 by decide] at this
      omega
    rw [Rel.Verify.Ew.intStep_add, if_neg (not_or.2 ⟨hnt, by decide⟩), Int64.ofNat_add]; rfl
  have hS : ∀ a x b, (graph Prod.fst ≫ succDen TU : Core.Rel (Obj.El (.prod .long E)) (Obj.El .long)) (a, x) b ↔
      P a ∧ b = Ew.intStep Ew.add Alg.nul a 1 ∧ P b := fun a x b => by
    simp only [Core.Rel.comp, Core.Rel.graph, hd]
    exact ⟨fun ⟨_, rfl, h⟩ => let ⟨h1, h2, h3⟩ := (succDen_iff _ _ _).1 h; ⟨(hd _).1 h1, h2, (hd _).1 h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨a, rfl, (succDen_iff _ _ _).2 ⟨(hd _).2 h1, h2, (hd _).2 h3⟩⟩⟩
  rw [foldDen_start]
  constructor
  · rintro ⟨v, hv, hf⟩
    obtain ⟨rfl, h0⟩ := (he v).1 hv
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .long) _ xs 0 w).1 hf
    have hs := fun t ht => (hS _ _ _).1 (hs t ht)
    have hg : ∀ t ≤ xs.length, g t = Int64.ofNat t := by
      intro t
      induction t with
      | zero => intro _; exact hg0
      | succ t ih => intro ht; rw [(hs t (by omega)).2.1, ih (by omega), step t (by omega)]
    refine ⟨fun t ht => ?_, hg _ (Nat.le_refl _)⟩
    rw [← hg t ht]
    cases t with
    | zero => rw [hg0]; exact h0
    | succ t => exact (hs t (by omega)).2.2
  · rintro ⟨hP, rfl⟩
    exact ⟨0, (he 0).2 ⟨rfl, hP 0 (Nat.zero_le _)⟩, (foldDen_iter (X := .long) _ xs 0 _).2 ⟨Int64.ofNat, rfl,
      fun t ht => (hS _ _ _).2 ⟨hP t (by omega), (step t (by omega)).symm, hP (t + 1) (by omega)⟩, rfl⟩⟩

/-- **The definition `⦇[0, plus]⦈` of `sum` on `TU` from the word `0` is `sum`'s fold kept in `TU`**, at any atom
    `t`, `P` every value or an initial segment `0…k`: its elements and result in `P` and `stepAt t add` folded from
    `0`. At every value nothing is cut; on `0…k` the prefix sums of its elements rise from `0` to the result
    (`chain_in`), so all are in `P` iff it is. -/
theorem plus_iff {t : QAtomicType} {TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))} {P : (Obj.atom t).El → Prop}
    (hP : (∀ x, P x) ∨ Seg (.atom t) P) (hU : ∀ x y, TU x y ↔ x = y ∧ P x) (xs : List (Obj.atom t).El)
    (w : (Obj.atom t).El) :
    (∃ v, (v = QAtomicType.ofBits t 0 ∧ P (QAtomicType.ofBits t 0)) ∧
        foldDen (E := .atom t) (V := .atom t) (fun _ b => b = v) (arithDen t Ew.add TU) xs w) ↔
      (∀ x ∈ xs, P x) ∧ P w ∧
        foldDen (E := .atom t) (V := .atom t) (fun _ b => b = QAtomicType.ofBits t 0) (stepAt t Ew.add) xs w := by
  have hd : ∀ x, (∃ v, TU x v) ↔ P x := fun x =>
    ⟨fun ⟨_, h⟩ => ((hU _ _).1 h).2, fun h => ⟨x, (hU _ _).2 ⟨rfl, h⟩⟩⟩
  have hA : ∀ a x b, arithDen t Ew.add TU (a, x) b ↔ P a ∧ P x ∧ stepAt t Ew.add (a, x) b ∧ P b := fun a x b => by
    rw [arithDen_iff]
    constructor
    · rintro ⟨h1, h2, v', hs, hv⟩; obtain ⟨rfl, hw⟩ := (hU _ _).1 hv; exact ⟨(hd _).1 h1, (hd _).1 h2, hs, hw⟩
    · rintro ⟨h1, h2, hs, hw⟩; exact ⟨(hd _).2 h1, (hd _).2 h2, b, hs, (hU _ _).2 ⟨rfl, hw⟩⟩
  constructor
  · rintro ⟨_, ⟨rfl, h0⟩, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ w).1 hf
    have hs := fun s hs' => (hA _ _ _).1 (hs s hs')
    refine ⟨fun x hx => ?_, ?_, (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ _).2
      ⟨g, hg0, fun s hs' => (hs s hs').2.2.1, rfl⟩⟩
    · obtain ⟨s, hs', rfl⟩ := List.getElem_of_mem hx; exact (hs s hs').2.1
    · rcases Nat.eq_zero_or_pos xs.length with e | e
      · rw [e, hg0]; exact h0
      · have := (hs (xs.length - 1) (by omega)).2.2.2; rwa [show xs.length - 1 + 1 = xs.length by omega] at this
  · rintro ⟨hE, hw, hf⟩
    obtain ⟨g, hg0, hs, rfl⟩ := (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ w).1 hf
    have hP' : ∀ s ≤ xs.length, P (g s) := by
      rcases hP with hall | hseg
      · exact fun s _ => hall _
      cases t <;> first | exact (hseg : False).elim | skip
      exact (chain_in (.inr hseg) g xs.length fun hI => ⟨by rw [hg0]; decide, fun s hs' => by
        obtain ⟨-, -, h1, h2, e⟩ := (stepDen_add_iff _ _ _).1 (hs s hs')
        have := hI.1 _ (hE _ (List.getElem_mem hs'))
        rw [e, Int64.toInt_add]; simp only [Int.bmod]; split <;> omega⟩).2 hw
    refine ⟨_, ⟨rfl, hg0 ▸ hP' 0 (Nat.zero_le _)⟩, (foldDen_iter (X := .atom t) (Y := .atom t) _ xs _ _).2
      ⟨g, hg0, fun s hs' => (hA _ _ _).2 ⟨hP' s (by omega), hE _ (List.getElem_mem hs'), hs s hs', hP' (s + 1) (by omega)⟩,
        rfl⟩⟩

/-- **`plus` cut to a coreflexive `U` is `arithDen`**: `(U×U) plus U` (`Tm.cut2`) keeps both operands and the sum
    in `U`. -/
theorem Tm.cut2_plus_den (ρ : Val) {t : QAtomicType} (U : Tm (.atom t) (.atom t)) (hU : ∀ x y, U.den ρ x y → x = y) :
    (Tm.cut2 (arithRow "plus") U).den ρ = arithDen t Ew.add (U.den ρ) := by
  funext p w; obtain ⟨a, b⟩ := p; apply propext; rw [arithDen_iff]
  simp only [Tm.cut2, Tm.prod, Tm.den, Tm.argDen, Prim.den_plusRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨⟨qa, qb⟩, ⟨⟨a', e1, h1⟩, ⟨b', e2, h2⟩⟩, v, hs, hv⟩
    subst e1 e2
    obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2
    exact ⟨⟨_, h1⟩, ⟨_, h2⟩, v, hs, hv⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, v, hs, hv⟩
    obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2
    exact ⟨(a, b), ⟨⟨a, rfl, h1⟩, ⟨b, rfl, h2⟩⟩, v, hs, hv⟩

/-- `lengthRow` at `[E] ⟶ ℕ` is the count of its list. -/
theorem Prim.den_lengthRow {E : Obj} :
    Prim.den lengthRow (.arr E) .long [] = fun (xs : List E.El) w => w = Int64.ofNat xs.length := by
  have ho : ∀ ps, lengthRow.objs (.arr E) .long ps = some [E, .long] := by
    simp [Prim.objs, Option.orElse, lengthRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == lengthRow.sym) =
      some ⟨RowCode.length, fun _ _ xs w => w = Int64.ofNat xs.length⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- At an atom no float, `sumDen` is the fold of `stepAt t add` from the word `0`, the definition `⦇[0, plus]⦈`'s
    step; at a float atom it adds in `f64` and rounds once, which no fold of `plus` (rounding each step) is. -/
theorem sumDen_fold {t : QAtomicType} (hf : t ∉ sumRow.native) :
    sumDen t = foldDen (E := .atom t) (V := .atom t) (fun _ b => b = QAtomicType.ofBits t 0) (stepAt t Ew.add) := by
  cases t <;> first | rfl | exact absurd (by decide) hf

/-- `sumRow` at `[t] ⟶ t` is `sumDen t`. -/
theorem Prim.den_sumRow {t : QAtomicType} : Prim.den sumRow (.arr (.atom t)) (.atom t) [] = sumDen t := by
  have ho : ∀ ps, sumRow.objs (.arr (.atom t)) (.atom t) ps = some [.atom t] := by
    simp [Prim.objs, Option.orElse, sumRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == sumRow.sym) = some ⟨RowCode.sum, fun σ _ => sumAt (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `flatRow` at `I×A ⟶ B` given `R : I ⟶ A×B` is `flatDen`. -/
theorem Prim.den_flatRow {I A B : Obj} (T : Core.Rel (Obj.El I) (Obj.El (.prod A B))) :
    Prim.den flatRow (.prod I A) B [⟨I, .prod A B, T⟩] = flatDen T := by
  have ho : ∀ ps, flatRow.objs (.prod I A) B ps = some [I, A, B] := by
    simp [Prim.objs, Option.orElse, flatRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == flatRow.sym) = some ⟨RowCode.flat, fun σ =>
      Sem.one (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ.getD 2 .long)) flatDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `foldIRow` at `I×[E] ⟶ V` given `e : I ⟶ V×V`, `S : (I×V)×E ⟶ I×V` is `foldIDen`. -/
theorem Prim.den_foldIRow {I E V : Obj} (Te : Core.Rel (Obj.El I) (Obj.El (.prod V V))) (TS : Core.Rel (Obj.El (.prod (.prod I V) E)) (Obj.El (.prod I V))) :
    Prim.den foldIRow (.prod I (.arr E)) V [⟨I, .prod V V, Te⟩, ⟨.prod (.prod I V) E, .prod I V, TS⟩] =
      foldIDen Te TS := by
  have ho : ∀ ps, foldIRow.objs (.prod I (.arr E)) V ps = some [I, V, E] := by
    simp [Prim.objs, Option.orElse, foldIRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == foldIRow.sym) = some ⟨RowCode.foldI, fun σ =>
      Sem.two (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ₂ σ)) (X₂ := .prod (.prod (σ₁ σ) (σ₂ σ)) (σ.getD 2 .long))
        (Y₂ := .prod (σ₁ σ) (σ₂ σ)) foldIDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.two]; exact dif_pos ⟨rfl, rfl, rfl, rfl⟩

/-- `F(U)` at `[V] ⟶ [V]`, `U` the coreflexive on `P`: the lists whose elements are all in `P`. -/
theorem Prim.den_mapRow_corefl {V : Obj} {TU : Core.Rel (Obj.El V) (Obj.El V)} {P : V.El → Prop} (hU : ∀ x y, TU x y ↔ x = y ∧ P x)
    (xs ys : List V.El) :
    Prim.den mapRow (.arr V) (.arr V) [⟨V, V, TU⟩] xs ys ↔ ys = xs ∧ ∀ x ∈ xs, P x := by
  have ho : ∀ ps, mapRow.objs (.arr V) (.arr V) ps = some [V, V] := by
    simp [Prim.objs, Option.orElse, mapRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == mapRow.sym) =
      some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) mapDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one, σ₁, σ₂, List.headD, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, dite_true, and_self]
  rw [Rel.Lang.mapDen_iff]; simp only [hU]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨List.ext_getElem hl fun t h1 h2 => (h t h2 h1).1.symm, fun x hx => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    exact (h t ht (by omega)).2
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, fun t ht _ => ⟨rfl, h _ (List.getElem_mem ht)⟩⟩


/-! ### Keyed lifting (§e): the law `Prim.keyLift` claims -/

/-- `r` commutes with keying: at the objects `I×v`, given each family `F` keyed, `⟨π₁,Fᴵ⟩` (`keyOf`), it means the
    keyed family of its meaning at each key `i` given the fibres `F i`. What `appliedRowL` needs to run `r` once on
    the keyed families of a program in place of once per key. -/
def Prim.KeyLifts (r : Prim) : Prop :=
  ∀ (I A B : Obj) (fs : List ((X : Obj) × (Y : Obj) × (I.El → Core.Rel (Obj.El X) (Obj.El Y)))),
    Prim.den r (.prod I A) (.prod I B) (fs.map fun ⟨X, Y, F⟩ => ⟨.prod I X, .prod I Y, keyOf F⟩) =
      keyOf fun i => Prim.den r A B (fs.map fun ⟨X, Y, F⟩ => ⟨X, Y, F i⟩)

/-- `star(R) ≜ μX : 𝟙 ∪ R X` commutes with keying (`star_keyOf`); at any other arguments both sides are `𝟘`. -/
theorem Prim.starRow_keyLifts : starRow.KeyLifts := by
  intro I A B fs
  have hf : rowDens.find? (·.1.sym == starRow.sym) = some ⟨RowCode.star, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X⟩ := rfl
  have ho : ∀ C D ps, starRow.objs C D ps = if D = C then some [C] else none := fun C D ps => by
    by_cases h : D = C <;> simp [h, Prim.objs, starRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups,
      List.eraseDupsBy, List.eraseDupsBy.loop, List.lookup]
  unfold Prim.den; rw [hf]; simp only [ho]
  by_cases hAB : B = A
  · subst hAB; simp only [if_true, RowCode.star, σ₁, List.headD, and_self, dite_true]
    match fs with
    | [] => exact keyOf_zero.symm
    | _ :: _ :: _ => exact keyOf_zero.symm
    | [⟨X, Y, F⟩] =>
      simp only [List.map_cons, List.map_nil, Sem.one]
      by_cases h : X = B ∧ Y = B
      · obtain ⟨rfl, rfl⟩ := h; simp only [and_self, dite_true]; exact star_keyOf F
      · simp only [Obj.prod.injEq, true_and, h, dite_false]; exact keyOf_zero.symm
  · simp only [Obj.prod.injEq, true_and, hAB, if_false]; exact keyOf_zero.symm

/-- **Every row with `keyLift` commutes with keying**: the obligations enumerated from `prims` itself, so a row that
    sets `keyLift` without a proof here fails `rfl`. -/
theorem Prim.keyLifts_ok (r : Prim) (hr : r ∈ prims) (hk : r.keyLift = true) : r.KeyLifts := by
  have e : prims.filter (·.keyLift) = [starRow] := rfl
  have h := List.mem_filter.2 ⟨hr, hk⟩
  rw [e, List.mem_singleton] at h; subst h; exact Prim.starRow_keyLifts

/-- A row given a family as `appliedRowL` runs it, on `⟨π₁,Rᴵ⟩` at `I×v`, means at each key `i` the row given the
    fibre of `R` at `i` (`Prim.keyLifts_ok`): the lifted term denotes the per-key family. -/
theorem Tm.den_keyedRow (ρ : Val) {r : Prim} (hr : r ∈ prims) (hk : r.keyLift = true) {I A B C D : Obj}
    (R : Tm I (.prod A B)) :
    (Tm.arg (.prim r : Tm (.prod I C) (.prod I D))
        (.pair .outl (.arg (.prim flatRow) R) : Tm (.prod I A) (.prod I B))).den ρ =
      keyOf fun i => Prim.den r C D [⟨A, B, fun a b => R.den ρ i (a, b)⟩] := by
  have e := Prim.keyLifts_ok r hr hk I C D [⟨A, B, fun i a b => R.den ρ i (a, b)⟩]
  simp only [List.map_cons, List.map_nil] at e
  rw [← e]
  have hf : (graph Prod.fst).rpair (flatDen (R.den ρ)) = keyOf fun i a b => R.den ρ i (a, b) :=
    Core.Rel.ext fun x y => by
      simp only [Core.Rel.rpair, Core.Rel.graph, Core.Rel.keyOf]
      exact and_congr_right fun _ => flatDen_iff _ _ _
  simp only [Tm.den, Tm.argDen, Prim.den_flatRow]; rw [hf]

/-- `at(0) ≜ ⟨𝟙, ⊤{0}⟩ at : [B] ⟶ B`, the head of an array; the index `0` is the one-word column `zeroCol`, whose row
    `zeroCol_row` states (a `col [0]` literal has no row lemma). -/
def Tm.at0 {B : Obj} : Tm (.arr B) B :=
  .comp (.pair .id (.top (.uni (A := .atom .i64) (zeroCol .i64 rfl)))) (.prim indexRow)

/-- **`lt` on any object `B`, a definition (B5b3)**: `dom(Λ(π₁ ∪ π₂) at(0) ∩ π₁) − dom(π₁ ∩ π₂)`, the coreflexive on
    the pairs `(x, y)` whose sorted two-element array `Λ(π₁ ∪ π₂)` starts with `x`, minus the pairs `x = y`
    (`Tm.lt_den`). Its fused form is the row `lt` (`Tab.cmpPairs`) at an integer-stored atom (`Tm.lt_row_den`, `RepSums`). -/
def Tm.ltDef (B : Obj) : Tm (.prod B B) (.prod B B) :=
  .diff (.dom (.meet (.comp (.lam (.join .outl .outr)) Tm.at0) .outl)) (.dom (.meet .outl .outr))

theorem Prim.den_indexRow {B : Obj} : Prim.den indexRow (.prod (.arr B) .long) B [] = atOn B .long := by
  have ho : indexRow.objs (.prod (.arr B) .long) B [] = some [B, .long] := by
    simp [Prim.objs, Option.orElse, indexRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == indexRow.sym) =
      some ⟨⟨"at", fun σ => (.prod (.arr (σ₁ σ)) (σ₂ σ), σ₁ σ)⟩, fun σ _ => atOn (σ₁ σ) (σ₂ σ)⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_cmpRow_lt {A : Obj} : Prim.den (cmpRow "lt") (.prod A A) (.prod A A) [] = ordDen true A := by
  have ho : (cmpRow "lt").objs (.prod A A) (.prod A A) [] = some [A] := by
    simp [Prim.objs, Option.orElse, cmpRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (cmpRow "lt").sym) =
      some ⟨⟨"lt", fun σ => (.prod (σ₁ σ) (σ₁ σ), .prod (σ₁ σ) (σ₁ σ))⟩, fun σ _ => ordDen true (σ₁ σ)⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_cmpRow_le {A : Obj} : Prim.den (cmpRow "le") (.prod A A) (.prod A A) [] = ordDen false A := by
  have ho : (cmpRow "le").objs (.prod A A) (.prod A A) [] = some [A] := by
    simp [Prim.objs, Option.orElse, cmpRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (cmpRow "le").sym) =
      some ⟨⟨"le", fun σ => (.prod (σ₁ σ) (σ₁ σ), .prod (σ₁ σ) (σ₁ σ))⟩, fun σ _ => ordDen false (σ₁ σ)⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `cmpRelRow` at an atom given `T` means `ltDen`, `leqDen` of it. -/
theorem Prim.den_cmpRelRow_lt {t : QAtomicType} (T : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) :
    Prim.den (cmpRelRow true) (.atom t) (.atom t) [⟨.atom t, .atom t, T⟩] = ltDen t T := by
  have ho : (cmpRelRow true).objs (.atom t) (.atom t) [(.atom t, .atom t)] = some [.atom t] := by
    simp [Prim.objs, Option.orElse, cmpRelRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (cmpRelRow true).sym) =
      some ⟨⟨ordSym true, fun σ => (σ₁ σ, σ₁ σ)⟩, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) (ordRelDen true (σ₁ σ))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact (dif_pos ⟨rfl, rfl⟩).trans rfl

theorem Prim.den_cmpRelRow_le {t : QAtomicType} (T : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) :
    Prim.den (cmpRelRow false) (.atom t) (.atom t) [⟨.atom t, .atom t, T⟩] = leqDen t T := by
  have ho : (cmpRelRow false).objs (.atom t) (.atom t) [(.atom t, .atom t)] = some [.atom t] := by
    simp [Prim.objs, Option.orElse, cmpRelRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (cmpRelRow false).sym) =
      some ⟨⟨ordSym false, fun σ => (σ₁ σ, σ₁ σ)⟩, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) (ordRelDen false (σ₁ σ))⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact (dif_pos ⟨rfl, rfl⟩).trans rfl

/-- `Tm.cmpDef c U` for a coreflexive test `c` of the pairs: `(a, b)` with `a` and `b` in `dom U` that `c` holds at. -/
theorem Tm.cmpDef_den (ρ : Val) {B : Obj} (c : Tm (.prod B B) (.prod B B)) (U : Tm B B)
    (hc : ∀ p q, c.den ρ p q → q = p) (a b : Obj.El B) :
    (Tm.cmpDef c U).den ρ a b ↔ (∃ v, U.den ρ a v) ∧ (∃ w, U.den ρ b w) ∧ c.den ρ (a, b) (a, b) := by
  simp only [Tm.cmpDef, Tm.den, Tm.dom_den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.top, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.id, Core.Rel.graph]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨rfl, v, h1, -⟩, w, -, rfl, w2, -, hw⟩, p, hcp, rfl⟩
    obtain rfl := hc _ _ hcp
    exact ⟨⟨v, h1⟩, ⟨w2, hw⟩, hcp⟩
  · rintro ⟨⟨v, hv⟩, ⟨w, hw⟩, hl⟩
    exact ⟨(a, b), ⟨⟨rfl, v, hv, hv⟩, b, trivial, rfl, w, hw, hw⟩, (a, b), hl, rfl⟩

theorem Tm.cmpDef_lt_den (ρ : Val) {t : QAtomicType} (U : Tm (.atom t) (.atom t)) :
    (Tm.cmpDef (.prim (cmpRow "lt")) U).den ρ = (Tm.lt U).den ρ := by
  have hd : ∀ p q, (Tm.prim (cmpRow "lt") : Tm (.prod (.atom t) (.atom t)) (.prod (.atom t) (.atom t))).den ρ p q ↔
      q = p ∧ ltAt t p.1 p.2 := fun p q => by
    simp only [Tm.den, Prim.den_cmpRow_lt, ordDen_iff, if_true]
  funext a b; apply propext
  rw [Tm.cmpDef_den ρ _ U fun p q h => ((hd p q).1 h).1, hd]
  simp only [Tm.lt, Tm.den, Tm.argDen, Prim.den_cmpRelRow_lt, true_and]
  exact (ltDen_iff _ _ _ _).symm

theorem Tm.cmpDef_le_den (ρ : Val) {t : QAtomicType} (U : Tm (.atom t) (.atom t)) :
    (Tm.cmpDef (.prim (cmpRow "le")) U).den ρ = (Tm.leq U).den ρ := by
  have hd : ∀ p q, (Tm.prim (cmpRow "le") : Tm (.prod (.atom t) (.atom t)) (.prod (.atom t) (.atom t))).den ρ p q ↔
      q = p ∧ leAt t p.1 p.2 := fun p q => by
    simp only [Tm.den, Prim.den_cmpRow_le, ordDen_iff, Bool.false_eq_true, if_false]
  funext a b; apply propext
  rw [Tm.cmpDef_den ρ _ U fun p q h => ((hd p q).1 h).1, hd]
  simp only [Tm.leq, Tm.den, Tm.argDen, Prim.den_cmpRelRow_le, true_and]
  exact (leqDen_iff _ _ _ _).symm

theorem Tm.at0_den (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (b : Obj.El B) :
    (Tm.at0 (B := B)).den ρ xs b ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  simp only [Tm.at0, Tm.den, Tm.argDen, Prim.den_indexRow]
  simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.id, atOn_iff]
  have h0 : ∀ i, ValsB.row (o := false) (A := .atom .i64) (zeroCol .i64 rfl) i = (0 : Int64) := fun i => by rw [zeroCol_row]; rfl
  simp only [h0, exists_eq_left, exists_const, and_true, true_and, exists_and_left]
  constructor
  · rintro ⟨⟨ys, k⟩, ⟨rfl, -, hk⟩, -, h⟩
    obtain ⟨-, rfl⟩ := hk
    obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 h
    exact ⟨hl, e.symm⟩
  · intro h
    exact ⟨⟨xs, 0⟩, ⟨rfl, ⟨0, by simp⟩, rfl⟩, (by decide : (0 : Int) ≤ Int64.toInt (0 : Int64)),
      List.getElem?_eq_some_iff.2 ⟨h.1, h.2.symm⟩⟩

/-- `Λ(π₁ ∪ π₂) at(0)` reads `x` at the pair `(x, y)` of two different elements exactly where `x` is the smaller:
    the one list ascending by `Obj.lt` holding both has the smaller first. -/
theorem Tm.head_lt {B : Obj} {x y : B.El} (hxy : x ≠ y) :
    (∃ ys : List B.El, (ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ b = x ∨ b = y) ∧ ∃ h : 0 < ys.length, x = ys[0]'h) ↔
      B.lt x y := by
  constructor
  · rintro ⟨ys, ⟨hp, hm⟩, h0, hx⟩
    obtain ⟨j, hj, hy⟩ := List.mem_iff_getElem.1 ((hm y).2 (Or.inr rfl))
    have hj0 : j ≠ 0 := by rintro rfl; exact hxy (hx.trans hy)
    rw [hx, ← hy]
    exact List.pairwise_iff_getElem.1 hp 0 j h0 hj (Nat.pos_of_ne_zero hj0)
  · intro hl
    exact ⟨[x, y], ⟨List.pairwise_pair.2 hl, by simp⟩, by simp, rfl⟩

/-- `lt` on any object: the coreflexive on the pairs `(x, y)` with `x` before `y` in `Obj.lt`. -/
theorem Tm.lt_den (ρ : Val) (B : Obj) :
    (Tm.ltDef B).den ρ = fun p q => q = p ∧ B.lt p.1 p.2 := by
  funext p q; apply propext
  simp only [Tm.ltDef, Tm.den, Tm.dom_den, lamDen_fun]
  simp only [Core.Rel.diff, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.id,
    Core.Rel.graph, Core.Rel.union, Tm.at0_den]
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨rfl, rfl⟩, b, ⟨hA, rfl⟩, -⟩, hne⟩
    exact ⟨⟨rfl, rfl⟩, (Tm.head_lt fun h => hne ⟨⟨rfl, rfl⟩, b, ⟨rfl, h⟩, rfl, h⟩).1 hA⟩
  · rintro ⟨⟨rfl, rfl⟩, hl⟩
    have hne : x' ≠ y' := by rintro rfl; exact B.lt_irrefl _ hl
    have h := (Tm.head_lt hne).2 hl
    exact ⟨⟨⟨rfl, rfl⟩, x', ⟨h, rfl⟩, h, rfl⟩, fun h => by obtain ⟨-, b, ⟨hb1, hb2⟩, -⟩ := h; exact hne (hb1.symm.trans hb2)⟩

/-- `ascRow` at `ℕ ⟶ B` given `T : B ⟶ C` means `ascDen` of the set `dom T`. -/
theorem Prim.den_ascRow {B : Obj} (T : Core.Rel (Obj.El B) (Obj.El B)) :
    Prim.den ascRow .long B [⟨B, B, T⟩] = ascDen B fun b => ∃ c, T b c := by
  have ho : ascRow.objs .long B [(B, B)] = some [B, .long] := by
    simp [Prim.objs, Option.orElse, ascRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == ascRow.sym) = some ⟨RowCode.asc, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => ascDen (σ₁ σ) fun b => ∃ c, T b c⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- **`asc(P)` as a definition (B5b5)**: `(dom(P) Λ(G dom(P)) L)°`, `a` of `dom P` to the count `L` of the list
    (`Λ`, ascending) of the elements of `dom P` that `G` relates `a` to; `G` is `>` on `dom P` (`Tm.ascDef_of_len`'s
    `hG`), the row's `(Tm.lt U)°` at an integer-stored atom, `(Tm.cmpDef c U)°` elsewhere (`Tm.gt_of_lt`). -/
def Tm.ascDef {B : Obj} (P G : Tm B B) (L : Tm (.arr B) .long) : Tm .long B :=
  .conv (.comp (.comp (.dom P) (.lam (.comp G (.dom P)))) L)

/-- `(Tm.cmpDef c U)°` is `>` on `dom U` where the test `c` means `Tm.ltDef` (`Tm.lt_den`; the prelude's `lt`,
    `Tm.ltDef_den`): an instance of `Tm.ascDef_of_len`'s `hG` at any object. -/
theorem Tm.gt_of_lt (ρ : Val) {B : Obj} (c : Tm (.prod B B) (.prod B B)) (U : Tm B B)
    (hc : c.den ρ = (Tm.ltDef B).den ρ) (x y : B.El) (hx : ∃ v, U.den ρ x v) (hy : ∃ v, U.den ρ y v) :
    (Tm.conv (Tm.cmpDef c U)).den ρ x y ↔ B.lt y x := by
  have hl := Tm.lt_den ρ B
  show (Tm.cmpDef c U).den ρ y x ↔ _
  rw [Tm.cmpDef_den ρ c U (fun p q h => by rw [hc, hl] at h; exact h.1) y x, hc, hl]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hy, hx, rfl, h⟩⟩

/-- Among the elements of a list ascending by `Obj.lt`, those before its `k`-th are exactly the first `k`. -/
theorem lt_take_iff {B : Obj} {ys : List B.El} (hp : ys.Pairwise B.lt) {k : Nat} {a : B.El} (hk : ys[k]? = some a)
    (b : B.El) : b ∈ ys.take k ↔ b ∈ ys ∧ B.lt b a := by
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hk
  constructor
  · intro hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    rw [List.length_take] at hi
    simp only [List.getElem_take]
    exact ⟨List.getElem_mem _, List.pairwise_iff_getElem.1 hp i k _ hk' (by omega)⟩
  · rintro ⟨hb, hl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    rcases Nat.lt_trichotomy i k with h | rfl | h
    · exact List.mem_iff_getElem.2 ⟨i, by rw [List.length_take]; omega, by simp⟩
    · exact absurd hl (Obj.lt_irrefl _ _)
    · exact absurd (List.pairwise_iff_getElem.1 hp k i hk' hi h) (Obj.lt_asymm B hl)

-- no `intOrd` hypothesis as `lt_row_den` has: `ascDen` reads `Obj.lt` itself, so the float split (totalOrder vs IEEE) is
-- only in the row `lt`, not here
/-- **`Tm.ascDef` is the row `asc` cut to `Q`** where `dom P` has a short list ascending by `Obj.lt` (`Tm.dom P`
    finite at an object whose keys separate its elements) and `L` counts a short list as `length` does, its results in
    `Q`: the row's meaning `ascDen` (`Prim.den_ascRow`, `Tab.asc_holds`) numbers `dom P` by the elements below, which
    `Λ(G dom P) L` counts, `G` being `>` on `dom P` (`hG`). -/
theorem Tm.ascDef_of_len (ρ : Val) {B : Obj} (P G : Tm B B) (L : Tm (.arr B) .long) (Q : Int64 → Prop)
    (hG : ∀ x y, (∃ c, P.den ρ x c) → (∃ c, P.den ρ y c) → (G.den ρ x y ↔ B.lt y x))
    (hL : ∀ zs : List B.El, zs.length < 2 ^ 63 → ∀ w, L.den ρ zs w ↔ w = Int64.ofNat zs.length ∧ Q w)
    (hp : ∃ ys : List B.El, ys.Pairwise B.lt ∧ (∀ b, b ∈ ys ↔ ∃ c, P.den ρ b c) ∧ ys.length < 2 ^ 63) (j : Int64)
    (a : B.El) :
    (Tm.ascDef P G L).den ρ j a ↔ Q j ∧ ascDen B (fun b => ∃ c, P.den ρ b c) j a := by
  have hd : ∀ x y, (Tm.dom P).den ρ x y ↔ y = x ∧ ∃ c, P.den ρ x c := fun x y => by
    simp only [Tm.dom_den, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.id]
    constructor
    · rintro ⟨rfl, c, h, -⟩; exact ⟨rfl, c, h⟩
    · rintro ⟨rfl, c, h⟩; exact ⟨rfl, c, h, h⟩
  simp only [Tm.ascDef, Tm.den, lamDen_fun]
  simp only [Core.Rel.comp, Core.Rel.recip, hd]
  unfold ascDen
  constructor
  · rintro ⟨zs, ⟨a1, ⟨rfl, ha⟩, hzp, hzm⟩, hl⟩
    obtain ⟨ys, hyp, hym, hys⟩ := hp
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ((hym a1).2 ha)
    have hkl : k < ys.length := (List.getElem?_eq_some_iff.1 hk).1
    have hz : zs = ys.take k := lt_sorted_unique hzp (hyp.sublist (List.take_sublist _ _)) fun b => by
      rw [hzm, lt_take_iff hyp hk, hym]
      exact ⟨fun ⟨b1, hl, e, hc⟩ => by subst e; exact ⟨hc, (hG _ _ ha hc).1 hl⟩, fun ⟨hc, hl⟩ => ⟨b, (hG _ _ ha hc).2 hl, rfl, hc⟩⟩
    obtain ⟨rfl, hQ⟩ := (hL zs (by rw [hz, List.length_take]; omega) _).1 hl
    refine ⟨hQ, ys, hyp, hym, k, hk, ?_⟩
    rw [hz, List.length_take, Nat.min_eq_left (Nat.le_of_lt hkl)]
  · rintro ⟨hQ, ys, hyp, hym, k, hk, rfl⟩
    obtain ⟨ys0, hyp0, hym0, hys0⟩ := hp
    have hys : ys.length < 2 ^ 63 := by
      rw [lt_sorted_unique hyp hyp0 fun b => by rw [hym, hym0]]; exact hys0
    have ha : ∃ c, P.den ρ a c := (hym a).1 (List.mem_of_getElem? hk)
    have hkl : k < ys.length := (List.getElem?_eq_some_iff.1 hk).1
    refine ⟨ys.take k, ⟨a, ⟨rfl, ha⟩, hyp.sublist (List.take_sublist _ _), fun b => ?_⟩, ?_⟩
    · rw [lt_take_iff hyp hk, hym]
      exact ⟨fun ⟨hc, hl⟩ => ⟨b, (hG _ _ ha hc).2 hl, rfl, hc⟩, fun ⟨b1, hl, e, hc⟩ => by subst e; exact ⟨hc, (hG _ _ ha hc).1 hl⟩⟩
    · exact (hL _ (by rw [List.length_take]; omega) _).2 ⟨by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkl)], hQ⟩

end Rel.Lang
