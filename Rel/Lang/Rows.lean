import Rel.Lang.GenSpec
import Rel.Run.Lang.Compile

/-! The rows of `prims` with their meanings and lemmas (`doc/rel-denotation-design.md` §1.3): each row's code
    (`RowCode`, in `Compile`) beside the relation it computes, the proof type-checked where the row is written. -/

namespace Rel.Lang

open Tab Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc


/-- The code `c` computes the meaning `s`, the two at the same objects (a meaning at other objects would let a row
    read its code at one pair of objects and its meaning at another). -/
def Code.Sound (c : Code) (s : Sem) : Prop :=
  ∀ X Y e (f : Fn e X Y), c = ⟨X, Y, e, f⟩ → ∃ T, s = ⟨X, Y, T⟩ ∧ Gen.Sound f T


/-- The codes `cs` compute the meanings `ss`, position by position. -/
def Code.Sounds : List Code → List Sem → Prop
  | [], [] => True
  | c :: cs, s :: ss => Code.Sound c s ∧ Code.Sounds cs ss
  | _, _ => False

/-- The lemma of the row `rowDens[i]`, at its object variables `σ` where `ok` holds: given arguments whose codes
    compute their meanings, the row's code computes its meaning (the one `Tm.den` reads). -/
structure Row where
  i : Fin rowDens.length
  ok : List Obj → Bool := fun _ => true
  sound : ∀ σ, ok σ = true → ∀ (cs : List Code) (ss : List Sem), Code.Sounds cs ss →
    ∀ f, rowDens[i].1.run σ cs = some f → Gen.Sound f (rowDens[i].2 σ ss)

/-- A row with no relation argument is sound at `σ` where its code is. -/
theorem RowCode.plain_sound {sym : String} {ty : List Obj → Obj × Obj} {f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2}
    {T : (σ : List Obj) → Den (ty σ).1 (ty σ).2} {σ : List Obj} (h : Gen.Sound (f σ) (T σ)) (cs : List Code)
    (ss : List Sem) (_ : Code.Sounds cs ss) (g : Fn true (ty σ).1 (ty σ).2)
    (hg : (RowCode.plain sym ty f).run σ cs = some g) : Gen.Sound g (T σ) := by
  simp only [RowCode.plain] at hg
  split at hg
  · cases hg; exact h
  · cases hg

/-- A row with no relation argument, the lemma `h` of its meaning `T` where `ok` holds. -/
def Row.plain (i : Fin rowDens.length) {sym : String} {ty : List Obj → Obj × Obj}
    {f : (σ : List Obj) → Fn true (ty σ).1 (ty σ).2} {T : (σ : List Obj) → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.plain sym ty f, fun σ _ => T σ⟩) (ok : List Obj → Bool)
    (h : ∀ σ, ok σ = true → Gen.Sound (f σ) (T σ)) : Row :=
  { i, ok, sound := by rw [e]; exact fun σ ho cs ss hs => RowCode.plain_sound (h σ ho) cs ss hs }

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

/-- A row with one relation argument, the lemma `h` of its meaning `D` of the argument's. -/
def Row.unary (i : Fin rowDens.length) {sym : String} {ty par : List Obj → Obj × Obj}
    {f : (σ : List Obj) → (e : Bool) → Fn e (par σ).1 (par σ).2 → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (par σ).1 (par σ).2 → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.unary sym ty par f, fun σ => Sem.one (D σ)⟩)
    (h : ∀ σ e (R : Fn e (par σ).1 (par σ).2) T, Gen.Sound R T → Gen.Sound (f σ e R) (D σ T)) : Row :=
  { i, sound := by rw [e]; exact fun σ _ => RowCode.unary_sound h σ }

/-- A row whose argument is a pair test, the lemma `h` of its meaning `D` of the test's at a test run on demand
    (one not on demand has no code: `RowCode.test`). -/
def Row.test (i : Fin rowDens.length) {sym : String} {ty : List Obj → Obj × Obj}
    {f : (σ : List Obj) → Fn true (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Fn true (ty σ).1 (ty σ).2}
    {D : (σ : List Obj) → Den (.prod (σ₁ σ) (σ₁ σ)) (.prod (σ₁ σ) (σ₁ σ)) → Den (ty σ).1 (ty σ).2}
    (e : rowDens[i] = ⟨RowCode.test sym ty f, fun σ => Sem.one (D σ)⟩)
    (h : ∀ σ Q T, Gen.Sound Q T → Gen.Sound (f σ Q) (D σ T)) : Row :=
  .unary i e fun σ e Q T hQ => by
    cases e
    · exact fun _ => trivial
    · exact h σ Q T hQ

/-- Every row of `prims` with its lemma, by its index in `rowDens`. `setify` and `asc` hold where the element
    object is canonical: an ascending permutation is unique only where `¬ lt` is antisymmetric (`Obj.asc_unique`). -/
def rows : List Row :=
  [.plain ⟨0, by decide⟩ rfl (fun _ => true) fun _ _ => τ_sound,
   .plain ⟨1, by decide⟩ rfl (fun _ => true) fun _ _ => cons_sound,
   .plain ⟨2, by decide⟩ rfl (fun _ => true) fun _ _ => mem_sound,
   .plain ⟨3, by decide⟩ rfl (fun _ => true) fun _ _ => inl_sound,
   .plain ⟨4, by decide⟩ rfl (fun _ => true) fun _ _ => inr_sound,
   .unary ⟨5, by decide⟩ rfl fun _ _ _ _ => map_sound, .unary ⟨6, by decide⟩ rfl fun _ _ _ _ => filter_sound,
   .unary ⟨7, by decide⟩ rfl fun _ _ _ _ => takewhile_sound,
   .test ⟨8, by decide⟩ rfl fun _ _ _ => thinL_sound, .test ⟨9, by decide⟩ rfl fun _ _ _ => merge_sound,
   .unary ⟨10, by decide⟩ rfl fun _ _ _ _ => loop_sound,
   .plain ⟨11, by decide⟩ rfl (fun _ => true) fun _ _ => uncons_sound,
   .plain ⟨12, by decide⟩ rfl (fun _ => true) fun _ _ => length_sound,
   .plain ⟨13, by decide⟩ rfl (fun _ => true) fun _ _ => sum_sound,
   .plain ⟨14, by decide⟩ rfl (fun _ => true) fun _ _ => inits_sound,
   .plain ⟨15, by decide⟩ rfl (fun _ => true) fun _ _ => tails_sound,
   .plain ⟨16, by decide⟩ rfl (fun _ => true) fun _ _ => prefix_sound,
   .plain ⟨17, by decide⟩ rfl (fun _ => true) fun _ _ => suffix_sound,
   .plain ⟨18, by decide⟩ rfl (fun _ => true) fun _ _ => concat_sound,
   .plain ⟨19, by decide⟩ rfl (fun _ => true) fun _ _ => cat_sound,
   .plain ⟨20, by decide⟩ rfl (fun _ => true) fun _ _ => uncat_sound,
   .plain ⟨21, by decide⟩ rfl (fun _ => true) fun _ _ => zip_sound,
   .plain ⟨22, by decide⟩ rfl (fun _ => true) fun _ _ => snoc_sound,
   .plain ⟨23, by decide⟩ rfl (fun _ => true) fun _ _ => unsnoc_sound,
   .plain ⟨24, by decide⟩ rfl (fun σ => (σ₁ σ).canonical) fun _ hc =>
     let ⟨ho, hi⟩ := canonical_spec _ hc; setify_sound ho hi,
   .plain ⟨25, by decide⟩ rfl (fun _ => true) fun _ _ => distinct_sound,
   .plain ⟨26, by decide⟩ rfl (fun σ => (σ₁ σ).canonical) fun _ hc =>
     let ⟨ho, hi⟩ := canonical_spec _ hc; asc_sound ho hi,
   .plain ⟨27, by decide⟩ rfl (fun _ => true) fun _ _ => tic_sound]

/-- Every lemma of the row `r` holds at `A ⟶ B`: each `Row` of its symbol has `ok` at the objects `Prim.objs` reads
    there (none read: `Prim.run` has no code, so nothing to vouch for). -/
def Prim.ok (r : Prim) (A B : Obj) : Bool :=
  (r.objs A B).all fun σ => rows.all fun w => rowDens[w.i].1.sym != r.sym || w.ok σ

/-- `t`'s meaning is a coreflexive, read off its shape: what `thin`'s pair test needs (`thin_sound`). -/
def Tm.cor : {A B : Obj} → Tm A B → Bool
  | _, _, .id | _, _, .uni _ | _, _, .zero | _, _, .dom _ | _, _, .ran _ => true
  | _, _, .meet R S => R.cor || S.cor
  | _, _, .comp R S | _, _, .join R S => R.cor && S.cor
  | _, _, .diff R _ | _, _, .conv R | _, _, .own R | _, _, .share _ R => R.cor
  | _, _, _ => false

/-- A term `Tm.cor` passes relates each point only to itself, across the objects its parts pass through. -/
theorem Tm.cor_den {A B : Obj} (t : Tm A B) : t.cor = true → ∀ (ρ : Val) (x : A.El) (y : B.El), t.den ρ x y →
    HEq x y := by
  induction t with
  | id => intro _ _ x y h; exact heq_of_eq h
  | uni U => intro _ _ x y h; exact heq_of_eq ((idU_holds U x y).1 h).1
  | zero => intro _ _ _ _ h; exact h.elim
  | dom R _ | ran R _ => intro _ _ x y h; exact heq_of_eq h.1
  | meet R S ihR ihS =>
    intro hc ρ x y h
    simp only [Tm.cor, Bool.or_eq_true] at hc; exact hc.elim (ihR · ρ x y h.1) (ihS · ρ x y h.2)
  | comp R S ihR ihS =>
    intro hc ρ x y h
    simp only [Tm.cor, Bool.and_eq_true] at hc
    obtain ⟨z, h1, h2⟩ := h; exact (ihR hc.1 ρ x z h1).trans (ihS hc.2 ρ z y h2)
  | join R S ihR ihS =>
    intro hc ρ x y h
    simp only [Tm.cor, Bool.and_eq_true] at hc; exact h.elim (ihR hc.1 ρ x y) (ihS hc.2 ρ x y)
  | diff R S ihR _ => intro hc ρ x y h; exact ihR hc ρ x y h.1
  | conv R ih => intro hc ρ x y h; exact (ih hc ρ y x h).symm
  | own R ih => intro hc ρ x y h; exact ih hc ρ x y h
  | share _ R ih => intro hc _ x y h; exact ih hc Val.empty x y h
  | _ => intro hc; simp [Tm.cor] at hc

/-- The first node of `t` that `compile_sound` has no case for, with why (`doc/rel-denotation-design.md` §7);
    `none` where every node has one. -/
def Tm.gap : {A B : Obj} → Tm A B → Option String
  -- `Λ`'s canonical list is the strictly ascending one, which exists where the element's key is one to one
  | _, _, .lam (B := B) R =>
    if B.canonical then R.gap else some "Λ: its element object has a key that merges elements (Obj.canonical)"
  | _, _, .E (B := B) R =>
    if B.canonical then R.gap else some "E: its element object has a key that merges elements (Obj.canonical)"
  | _, _, .thin (B := B) Q =>
    if B.canonical && Q.cor then Q.gap
    else some s!"thin: needs a canonical element object ({B.canonical}) and a coreflexive pair test ({Q.cor}, Tm.cor)"
  | _, _, .hylo .. => some "hylo: its rounds equal lfp only by den_local, which is not proved (§7.2)"
  | _, _, .call .. => some "call: a generic definition's term waits for stage 5"
  | A, B, .prim r => if r.ok A B then none else some s!"{r.sym}: its lemma does not hold at these objects (Row.ok)"
  | _, _, .mu k _ _ b =>
    if b.pol true k then b.gap else some s!"μ: the body is not positive in its variable {k} (D8 = R, §7.3)"
  | _, _, .nu k S b =>
    if b.pol true k then S.gap <|> b.gap else some s!"ν: the body is not positive in its variable {k} (D8 = R, §7.3)"
  | _, _, .foldI .. => some "foldI: Gen.foldI has no lemma (foldI_sound) yet"
  -- `share` is a part computed once and reused (numbered by `Expand.number`, its code memoised by `Out.memo`, left
  -- alone by `Tm.subst`), so the part must be closed: the meaning reads `Val.empty` and a part with a free variable
  -- is the code's fault, recomputed under each binding, never a meaning that should read `ρ`
  | _, _, .share _ R => if R.fv.isEmpty then R.gap else some "share: its part is not closed"
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .est R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R
  | _, _, .flat R => R.gap
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S
  | _, _, .prod R S | _, _, .junc R S | _, _, .juncD R S | _, _, .foldr R S | _, _, .fold R S
  | _, _, .arg R S =>
    R.gap <|> S.gap
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.gap <|> S.gap <|> U.gap <|> V.gap
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr
  | _, _, .nil | _, _, .atPos _ | _, _, .var _ _ => none

end Rel.Lang
