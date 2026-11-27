module

public import Rel.Lang.GenKFold

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The rows of `prims` a prelude definition's text names (`τ`, `cons`, `uncat`, `snoc`), each at its list object as
    `rowDens` gives it, for the theorems "the definition's `Tm.den` is the row's `rowDens` term" (B10b). A row's
    signature is restated once, by `rfl`, so a drift of `prims` from it fails here. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The row of `prims` named `s`; a name no row has gives `default`, which no `rowDens` entry answers to, so a
    theorem about it fails to hold rather than holding of the wrong row. -/
def rowOf (s : String) : Prim := (prims.find? (·.sym == s)).getD default

private abbrev B1 : OExp := .var {} "B"

/-- A left fold whose step relation is the function `f` is `List.foldl f`. -/
theorem foldDen_foldl {E V : Obj} {TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)} {f : V.El → E.El → V.El}
    (hS : ∀ a x w, TS (a, x) w ↔ w = f a x) :
    ∀ (xs : List E.El) (v w : V.El), foldDen (fun _ b => b = v) TS xs w ↔ w = xs.foldl f v
  | [], v, w => foldDen_nil TS v w
  | x :: xs, v, w => by
    rw [foldDen_cons, List.foldl_cons, ← foldDen_foldl hS xs (f v x) w]
    constructor
    · rintro ⟨v₁, v', ⟨_, rfl⟩, hs, h⟩
      rw [(hS _ _ _).1 hs] at h; exact h
    · intro h; exact ⟨v, f v x, ⟨v, rfl⟩, (hS v x _).2 rfl, h⟩

/-- A right fold whose step relation is the function `f` on the values satisfying the invariant `I` (kept by `f`,
    true of the seed) is `List.foldr f`. -/
theorem foldrDen_foldr {E V : Obj} {TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V)} {f : E.El → V.El → V.El}
    {I : V.El → Prop} (hS : ∀ x a, I a → ∀ w, TS (x, a) w ↔ w = f x a) (hI : ∀ x a, I a → I (f x a)) :
    ∀ (xs : List E.El) (v : V.El), I v → ∀ w, foldrDen (fun _ b => b = v) TS xs w ↔ w = xs.foldr f v := by
  suffices ∀ n (xs : List E.El), xs.length = n → ∀ v, I v → ∀ w,
      foldrDen (fun _ b => b = v) TS xs w ↔ w = xs.foldr f v from fun xs => this _ xs rfl
  intro n
  induction n with
  | zero =>
    intro xs h v _ w
    obtain rfl := List.length_eq_zero_iff.1 h
    simpa using foldrDen_nil TS v w
  | succ n ih =>
    intro xs h v hv w
    have hne : xs ≠ [] := by rintro rfl; simp at h
    obtain ⟨xs', x, rfl⟩ : ∃ xs' x, xs = xs' ++ [x] :=
      ⟨xs.dropLast, xs.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have hl : xs'.length = n := by simpa using h
    rw [foldrDen_snoc]
    constructor
    · rintro ⟨v₀, v', ⟨_, rfl⟩, hs, h'⟩
      rw [(hS x _ hv v').1 hs] at h'
      simpa [List.foldr_append] using (ih xs' hl _ (hI x _ hv) w).1 h'
    · intro hw
      exact ⟨v, f x v, ⟨v, rfl⟩, (hS x v hv _).2 rfl, (ih xs' hl _ (hI x _ hv) w).2 (by simpa [List.foldr_append] using hw)⟩

theorem Prim.den_tau {B : Obj} : Prim.den (rowOf "τ") B (.arr B) [] = fun a Y => Y = [a] := by
  have hs : (rowOf "τ").sig = ([], .var {} "A", .list (.var {} "A")) := rfl
  have ho : (rowOf "τ").objs B (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "τ").sym) = some ⟨RowCode.tau, fun _ _ a Y => Y = [a]⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_cons {B : Obj} :
    Prim.den (rowOf "cons") (.prod B (.arr B)) (.arr B) [] = fun p ys => ys = p.1 :: p.2 := by
  have hs : (rowOf "cons").sig = ([], .prod B1 (.list B1), .list B1) := rfl
  have ho : (rowOf "cons").objs (.prod B (.arr B)) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "cons").sym) = some ⟨RowCode.cons, fun _ _ p ys => ys = p.1 :: p.2⟩ :=
    rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_uncons {B : Obj} :
    Prim.den (rowOf "uncons") (.arr B) (.prod B (.arr B)) [] =
      Core.Rel.recip (Core.Rel.graph fun p => p.1 :: p.2) := by
  have hs : (rowOf "uncons").sig = ([], .list B1, .prod B1 (.list B1)) := rfl
  have ho : (rowOf "uncons").objs (.arr B) (.prod B (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "uncons").sym) =
      some ⟨RowCode.uncons, fun _ _ => Core.Rel.recip (Core.Rel.graph fun p => p.1 :: p.2)⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_cat {B : Obj} :
    Prim.den (rowOf "cat") (.prod (.arr B) (.arr B)) (.arr B) [] = fun p zs => zs = p.1 ++ p.2 := by
  have hs : (rowOf "cat").sig = ([], .prod (.list (.var {} "B")) (.list (.var {} "B")), .list (.var {} "B")) := rfl
  have ho : (rowOf "cat").objs (.prod (.arr B) (.arr B)) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "cat").sym) =
      some ⟨RowCode.cat, fun _ _ p zs => zs = p.1 ++ p.2⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_uncat {B : Obj} :
    Prim.den (rowOf "uncat") (.arr B) (.prod (.arr B) (.arr B)) [] = fun xs p => xs = p.1 ++ p.2 := by
  have hs : (rowOf "uncat").sig = ([], .list B1, .prod (.list B1) (.list B1)) := rfl
  have ho : (rowOf "uncat").objs (.arr B) (.prod (.arr B) (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "uncat").sym) =
      some ⟨RowCode.uncat, fun _ _ xs p => xs = p.1 ++ p.2⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_snoc {B : Obj} :
    Prim.den (rowOf "snoc") (.prod (.arr B) B) (.arr B) [] = fun p ys => ys = p.1 ++ [p.2] := by
  have hs : (rowOf "snoc").sig = ([], .prod (.list B1) B1, .list B1) := rfl
  have ho : (rowOf "snoc").objs (.prod (.arr B) B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "snoc").sym) =
      some ⟨RowCode.snoc, fun _ _ p ys => ys = p.1 ++ [p.2]⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_unsnoc {B : Obj} :
    Prim.den (rowOf "unsnoc") (.arr B) (.prod (.arr B) B) [] =
      Core.Rel.recip (Core.Rel.graph fun p => p.1 ++ [p.2]) := by
  have hs : (rowOf "unsnoc").sig = ([], .list B1, .prod (.list B1) B1) := rfl
  have ho : (rowOf "unsnoc").objs (.arr B) (.prod (.arr B) B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "unsnoc").sym) =
      some ⟨RowCode.unsnoc, fun _ _ => Core.Rel.recip (Core.Rel.graph fun p => p.1 ++ [p.2])⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

end Rel.Lang
