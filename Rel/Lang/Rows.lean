import Rel.Lang.CompileSpec

/-! The rows of `prims` with their meanings and lemmas (`doc/rel-denotation-design.md` §1.3): each row's code
    (`RowCode`, in `Compile`) beside the relation it computes, the proof type-checked where the row is written. -/

namespace Rel.Lang

open Rel Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- A relation argument's meaning with its objects. -/
abbrev Sem := (X Y : Obj) × Den X Y

/-- The code `c` computes the meaning `s`, the two at the same objects. -/
def Code.Sound (c : Code) (s : Sem) : Prop :=
  ∀ X Y e (f : Fn e X Y) (T : Den X Y), c = ⟨X, Y, e, f⟩ → s = ⟨X, Y, T⟩ → Gen.Sound f T

/-- The codes `cs` compute the meanings `ss`, position by position. -/
def Code.Sounds : List Code → List Sem → Prop
  | [], [] => True
  | c :: cs, s :: ss => Code.Sound c s ∧ Code.Sounds cs ss
  | _, _ => False

/-- A row of `prims` with its code, its meaning and the proof, at its object variables `σ`: given arguments whose
    codes compute their meanings, the row's code computes its meaning. -/
structure Row where
  code : RowCode
  den : (σ : List Obj) → List Sem → Den (code.ty σ).1 (code.ty σ).2
  sound : ∀ σ (cs : List Code) (ss : List Sem), Code.Sounds cs ss →
    ∀ f, code.run σ cs = some f → Gen.Sound f (den σ ss)

/-- A row with no relation argument is sound where its code is, at every `σ`. -/
theorem RowCode.plain_sound {sym : String} {ty : List Obj → Obj × Obj} {f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2}
    {T : (σ : List Obj) → Den (ty σ).1 (ty σ).2} (h : ∀ σ, Gen.Sound (f σ) (T σ)) (σ : List Obj) (cs : List Code)
    (ss : List Sem) (_ : Code.Sounds cs ss) (g : Fn true (ty σ).1 (ty σ).2)
    (hg : (RowCode.plain sym ty f).run σ cs = some g) : Gen.Sound g (T σ) := by
  simp only [RowCode.plain] at hg
  split at hg
  · cases hg; exact h σ
  · cases hg

/-- A row with no relation argument, its meaning `T` and the lemma `h`. -/
def Row.plain (c : RowCode) (sym : String) (ty : List Obj → Obj × Obj) (f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2)
    (e : c = RowCode.plain sym ty f) (T : (σ : List Obj) → Den (ty σ).1 (ty σ).2) (h : ∀ σ, Gen.Sound (f σ) (T σ)) :
    Row :=
  ⟨c, e ▸ fun σ _ => T σ, by subst e; exact fun σ cs ss hs => RowCode.plain_sound h σ cs ss hs⟩


open Classical in
/-- Every row of `prims` with a lemma. `rowGaps` lists the rest. -/
def rows : List Row :=
  [.plain .tau _ _ _ rfl (fun _ a Y => Y = [a]) fun _ => τ_sound,
   .plain .cons _ _ _ rfl (fun _ p ys => ys = p.1 :: p.2) fun _ => cons_sound,
   .plain .mem _ _ _ rfl (fun _ xs x => x ∈ xs) fun _ => mem_sound,
   .plain .inl _ _ _ rfl (fun _ => Core.Rel.inl) fun _ => inl_sound,
   .plain .inr _ _ _ rfl (fun _ => Core.Rel.inr) fun _ => inr_sound,
   .plain .uncons _ _ _ rfl (fun _ xs p => xs = p.1 :: p.2) fun _ => uncons_sound,
   .plain .length _ _ _ rfl (fun _ xs w => w = Int64.ofNat xs.length) fun _ => length_sound,
   .plain .sum _ _ _ rfl (fun _ xs w =>
      (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
        List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
        w = xs.foldr (· + ·) 0) fun _ => sum_sound,
   .plain .inits _ _ _ rfl (fun _ xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.take k)
     fun _ => inits_sound,
   .plain .tails _ _ _ rfl (fun _ xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k)
     fun _ => tails_sound,
   .plain .prefix _ _ _ rfl (fun _ xs ys => ys <+: xs) fun _ => prefix_sound,
   .plain .suffix _ _ _ rfl (fun _ xs ys => ys <:+ xs) fun _ => suffix_sound,
   .plain .concat _ _ _ rfl (fun _ xss ys => ys = xss.flatten) fun _ => concat_sound,
   .plain .cat _ _ _ rfl (fun _ p zs => zs = p.1 ++ p.2) fun _ => cat_sound,
   .plain .uncat _ _ _ rfl (fun _ xs p => xs = p.1 ++ p.2) fun _ => uncat_sound,
   .plain .zip _ _ _ rfl (fun _ p zs => zs = p.1.zip p.2) fun _ => zip_sound,
   .plain .snoc _ _ _ rfl (fun _ p ys => ys = p.1 ++ [p.2]) fun _ => snoc_sound,
   .plain .unsnoc _ _ _ rfl (fun _ xs p => xs = p.1 ++ [p.2]) fun _ => unsnoc_sound,
   .plain .distinct _ _ _ rfl (fun _ xs ys => ys = xs.eraseDups) fun _ => distinct_sound,
   .plain .tic _ _ _ rfl (fun _ p zss => zss = (List.range (p.2.length + 1)).map fun j => (p.1 :: p.2).take (j + 1))
     fun _ => tic_sound]

/-- The rows of `prims` with no `Row` yet: no lemma (`F`, `setify`, `asc`), or a relation argument whose `Row` is
    not written (`filter`, `takewhile`, `thinL`, `merge`, `loop`, whose lemmas exist). -/
def rowGaps : List String := ["F", "setify", "asc", "filter", "takewhile", "thinL", "merge", "loop"]

-- every row's code has its `Row` or is a gap, never both: the obligations are `rowCodes`, not `rows`
example : (rowCodes.all fun c => (rows.any (·.code.sym == c.sym)) != rowGaps.contains c.sym) = true := by decide

end Rel.Lang
