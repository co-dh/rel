import Rel.Lang.CompileSpec

/-! The rows of `prims` with their meanings and lemmas (`doc/rel-denotation-design.md` §1.3): each row's code
    (`RowCode`, in `Compile`) beside the relation it computes, the proof type-checked where the row is written. -/

namespace Rel.Lang

open Rel Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- A relation argument's meaning with its objects. -/
abbrev Sem := (X Y : Obj) × Den X Y

/-- The code `c` computes the meaning `s`, the two at the same objects (a meaning at other objects would let a row
    read its code at one pair of objects and its meaning at another). -/
def Code.Sound (c : Code) (s : Sem) : Prop :=
  ∀ X Y e (f : Fn e X Y), c = ⟨X, Y, e, f⟩ → ∃ T, s = ⟨X, Y, T⟩ ∧ Gen.Sound f T

/-- A row's meaning `D` of its one relation argument, read at `X ⟶ Y`; `𝟘` where the arguments are not one at
    `X ⟶ Y`, where `RowCode.unary` has no code. -/
def Sem.one {X Y A B : Obj} (D : Den X Y → Den A B) : List Sem → Den A B
  | [⟨X', Y', T⟩] => if h : X' = X ∧ Y' = Y then D (h.1 ▸ h.2 ▸ T) else 𝟘
  | _ => 𝟘

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

/-- A row with one relation argument is sound where its code is sound given its argument's. -/
theorem RowCode.unary_sound {sym : String} {ty par : List Obj → Obj × Obj}
    {f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (par σ).1 (par σ).2 → Den (ty σ).1 (ty σ).2}
    (h : ∀ σ e (R : Fn e (par σ).1 (par σ).2) T, Gen.Sound R T → Gen.Sound (f σ e R) (D σ T)) (σ : List Obj) :
    ∀ (cs : List Code) (ss : List Sem), Code.Sounds cs ss → ∀ (g : Fn true (ty σ).1 (ty σ).2),
      (RowCode.unary sym ty par f).run σ cs = some g → Gen.Sound g (Sem.one (D σ) ss)
  | [⟨X, Y, e, R⟩], [_], ⟨hc, _⟩, g, hg => by
    obtain ⟨T, rfl, hR⟩ := hc X Y e R rfl
    simp only [RowCode.unary, Code.at] at hg
    split at hg
    · rename_i hXY; obtain ⟨rfl, rfl⟩ := hXY
      cases hg; simpa [Sem.one] using h σ e R T hR
    · cases hg
  | [], _, _, _, hg | _ :: _ :: _, _, _, _, hg => by simp [RowCode.unary] at hg
  | [_], [], hs, _, _ | [_], _ :: _ :: _, hs, _, _ => by simp [Code.Sounds] at hs

/-- A row with one relation argument, its meaning `D` of the argument's, and the lemma `h`. -/
def Row.unary (c : RowCode) (sym : String) (ty par : List Obj → Obj × Obj)
    (f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2)
    (e : c = RowCode.unary sym ty par f) (D : (σ : List Obj) → Den (par σ).1 (par σ).2 → Den (ty σ).1 (ty σ).2)
    (h : ∀ σ e (R : Fn e (par σ).1 (par σ).2) T, Gen.Sound R T → Gen.Sound (f σ e R) (D σ T)) : Row :=
  ⟨c, e ▸ fun σ => Sem.one (D σ), by subst e; exact fun σ => RowCode.unary_sound h σ⟩

/-- A row whose argument is a pair test, its meaning `D` of the test's, and the lemma `h` at a test run on demand
    (one not on demand has no code: `RowCode.test`). -/
def Row.test (c : RowCode) (sym : String) (ty : List Obj → Obj × Obj)
    (f : (σ : List Obj) → Fn true (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Fn true (ty σ).1 (ty σ).2)
    (e : c = RowCode.test sym ty f)
    (D : (σ : List Obj) → Den (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Den (ty σ).1 (ty σ).2)
    (h : ∀ σ Q T, Gen.Sound Q T → Gen.Sound (f σ Q) (D σ T)) : Row :=
  .unary c sym ty _ _ e D fun σ e Q T hQ => by
    cases e
    · exact fun _ _ hb => absurd hb Bool.false_ne_true
    · exact h σ Q T hQ


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
     fun _ => tic_sound,
   .unary .map _ _ _ _ rfl (fun _ T xs ys => ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')) fun _ _ _ _ => map_sound,
   .unary .filter _ _ _ _ rfl (fun _ T xs ys => ys = xs.filter fun x => decide (∃ y, T x y))
     fun _ _ _ _ => filter_sound,
   .unary .takewhile _ _ _ _ rfl (fun _ T xs ys => ys = xs.takeWhile fun x => decide (∃ y, T x y))
     fun _ _ _ _ => takewhile_sound,
   .unary .loop _ _ _ _ rfl (fun σ T p c => ∃ g : Nat → (σ₁ σ).El, g 0 = p.1 ∧
      (∀ t (ht : t < p.2.length), T (g t, p.2[t]'ht) (g (t + 1))) ∧ c = g p.2.length) fun _ _ _ _ => loop_sound,
   .test .thinL _ _ _ rfl (fun _ T => thinLDen fun a b => decide (∃ c, T (a, b) c)) fun _ _ _ => thinL_sound,
   .test .merge _ _ _ rfl (fun _ T p zs => zs = List.merge p.1 p.2 fun a b => decide (∃ c, T (a, b) c))
     fun _ _ _ => merge_sound]

/-- The rows of `prims` with no `Row`: `setify` and `asc`. Each one's meaning is the composition `perm ≫ ord` of
    the permutations with the coreflexive of the ordered lists (`setify` after `distinct`), but `rep_setify` and
    `rep_asc` give it only at an object with `Obj.Ordered` (a float atom is not: NaN), and only one way: they state
    the table's lists are sorted permutations, not that every sorted permutation is in the table, so the `↔` of
    `Gen.Sound` also needs the sorted permutation unique (antisymmetry of `¬ lt`), which no lemma states. -/
def rowGaps : List String := ["setify", "asc"]

/-- The first node of `t` that `compile_sound` has no case for, with why (`doc/rel-denotation-design.md` §7);
    `none` where every node has one. -/
def Tm.gap : {A B : Obj} → {d : Bool} → Tm A B d → Option String
  | _, _, _, .lam _ | _, _, _, .E _ | _, _, _, .thin _ =>
    some "Λ, E, thin: the list a set is held as waits for D2's canonical tables (§7.1)"
  | _, _, _, .refold .. => some "refold: its rounds equal lfp only by den_local, which is not proved (§7.2)"
  | _, _, _, .call .. => some "call: a generic definition's term waits for stage 5"
  | _, _, _, .juncD .. => some "juncD: a row naming an empty side is not excluded yet (D7, §7.4)"
  | _, _, _, .prim r => if rowGaps.contains r.sym then some s!"{r.sym}: the row has no lemma (rowGaps)" else none
  | _, _, _, .mu k _ _ b | _, _, _, .nu k _ b =>
    if b.pol true k then b.gap else some s!"μ/ν: the body is not positive in its variable {k} (D8 = R, §7.3)"
  | _, _, _, .top R | _, _, _, .conv R | _, _, _, .dom R | _, _, _, .ran R | _, _, _, .est R | _, _, _, .own R
  | _, _, _, .succ R | _, _, _, .arith _ R | _, _, _, .leq R | _, _, _, .lt R | _, _, _, .share _ R
  | _, _, _, .flat R => R.gap
  | _, _, _, .comp R S | _, _, _, .meet R S | _, _, _, .join R S | _, _, _, .diff R S | _, _, _, .pair R S
  | _, _, _, .prod R S | _, _, _, .junc R S | _, _, _, .fold R S | _, _, _, .foldI R S | _, _, _, .arg R S =>
    R.gap <|> S.gap
  | _, _, _, .ldiv R S U V | _, _, _, .rdiv R S U V => R.gap <|> S.gap <|> U.gap <|> V.gap
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .zero | _, _, _, .id | _, _, _, .outl | _, _, _, .outr
  | _, _, _, .nil | _, _, _, .atPos _ | _, _, _, .var _ => none

-- every row's code has its `Row` or is a gap, never both: the obligations are `rowCodes`, not `rows`
example : (rowCodes.all fun c => (rows.any (·.code.sym == c.sym)) != rowGaps.contains c.sym) = true := by decide

end Rel.Lang
