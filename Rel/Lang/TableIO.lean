module

public import Rel.Run.Table
public import Rel.RepCols
import all Init.System.ST
import all Init.System.IO

/-! The `IO` monad's operations (`EST.pure`, `EST.throw`, `IO.ofExcept`) have no exposed body, so a `module` file
unfolds them only through `import all` of their modules. -/

@[expose] public section

namespace Rel.Lang.Table
open Rel

/-- A run of `ofRun` that returns `t` is `ofRunE` returning `t`. -/
theorem ofRun_ok {A B : Obj} {x : String} {r : Rel.Rel A B} {t : Tab A B} {s s' : Void IO.RealWorld}
    (h : ofRun x r s = .ok t s') : ofRunE x r = .ok t := by
  unfold ofRun IO.ofExcept at h
  cases e : ofRunE x r with
  | error m => rw [e] at h; simp [throw, throwThe, MonadExceptOf.throw, EST.throw] at h
  | ok u => rw [e] at h; simp [pure, EST.pure] at h; rw [h.1]

/-- A run of `ofRun` that returns `t` is `r.runE {}` returning `t`. -/
theorem ofRun_runE {A B : Obj} {x : String} {r : Rel.Rel A B} {t : Tab A B} {s s' : Void IO.RealWorld}
    (h : ofRun x r s = .ok t s') : r.runE {} = .ok t := by
  have := ofRun_ok h
  unfold ofRunE at this
  cases e : r.runE {} with
  | error m => rw [e] at this; cases this
  | ok u => rw [e] at this; cases this; rfl

/-- An `IO` bind that returns ran both its parts. -/
theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β} {s s' : Void IO.RealWorld} {b : β}
    (h : (x >>= f) s = .ok b s') : ∃ a s1, x s = .ok a s1 ∧ f a s1 = .ok b s' := by
  change EST.bind x f s = _ at h; unfold EST.bind at h
  split at h
  · rename_i a s1 e; exact ⟨a, s1, e, h⟩
  · cases h

theorem io_pure_ok {α : Type} {a b : α} {s s' : Void IO.RealWorld} (h : (pure a : IO α) s = .ok b s') : a = b := by
  simp only [pure, EST.pure] at h; cases h; rfl

theorem io_throw_ne {α : Type} {e : IO.Error} {b : α} {s s' : Void IO.RealWorld}
    (h : (throw e : IO α) s = .ok b s') : False := by
  simp [throw, throwThe, MonadExceptOf.throw, EST.throw] at h

/-- `same` returns its column cast along the equality of the counts it checked. -/
theorem same_ok {F : USize → Type} {fx fy : String} {n : USize} {y : (m : USize) × F m} {z : F n}
    {s s' : Void IO.RealWorld} (h : same fx n fy y s = .ok z s') : ∃ hh : y.1 = n, z = hh ▸ y.2 := by
  unfold same at h
  split at h
  · rename_i hh; exact ⟨hh, (io_pure_ok h).symm⟩
  · exact (io_throw_ne h).elim

/-- A `match h : d with` on an option known to be `some t` takes its `some` alternative. -/
theorem match17_some {β : Sort u} {d : Option QAtomicType} {t : QAtomicType}
    {f : (t : QAtomicType) → d = some t → β} {g : d = none → β} (hd : d = some t) :
    readValsB.match_17 (fun _ => β) d f g = f t hd := by subst hd; rfl

/-- A `match h : d with` on an option known to be `none` takes its `none` alternative. -/
theorem match17_none {β : Sort u} {d : Option QAtomicType}
    {f : (t : QAtomicType) → d = some t → β} {g : d = none → β} (hd : d = none) :
    readValsB.match_17 (fun _ => β) d f g = g hd := by subst hd; rfl

/-- `rowsOk` that returned found no row to refuse. -/
theorem rowsOk_ok {k : Nat} {f : (i : Nat) → i < k → Option String} {u : PUnit} {s s' : Void IO.RealWorld}
    (h : rowsOk k f s = .ok u s') : ∀ i (hi : i < k), f i hi = none := by
  unfold rowsOk at h
  obtain ⟨r, s1, h1, -⟩ := io_bind_ok h
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h1
  have key : ∀ (l : List Nat) (hl : ∀ a ∈ l, a < k) {s s' : Void IO.RealWorld} {u : PUnit},
      (forIn' l PUnit.unit (fun a ha _ => do
        if let some m := f a (hl a ha) then throw (IO.userError m)
        pure (ForInStep.yield PUnit.unit)) : IO PUnit) s = .ok u s' → ∀ a (ha : a ∈ l), f a (hl a ha) = none := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ a ha; cases ha
    | cons b l ih =>
      intro hl s s' u h a ha
      rw [List.forIn'_cons] at h
      obtain ⟨r, s1, h1, h⟩ := io_bind_ok h
      cases hf : f b (hl b (List.mem_cons_self ..)) with
      | some m =>
        simp only [hf] at h1
        obtain ⟨r', s2, h2, -⟩ := io_bind_ok h1
        exact (io_throw_ne h2).elim
      | none =>
        cases List.mem_cons.1 ha with
        | inl e => subst e; exact hf
        | inr hm =>
          simp only [hf] at h1
          have hr := io_pure_ok h1
          subst hr
          exact ih (fun a ha => hl a (List.mem_cons_of_mem _ ha)) h a hm
  intro i hi
  exact key _ (fun a ha => (Std.Legacy.Range.mem_of_mem_range' (r := [0:k]) ha).2.1) h1 i
    (List.mem_range'_1.2 ⟨Nat.zero_le _, by simpa [Std.Legacy.Range.size] using hi⟩)


/-- A leaf column has a real type: `Opt .general` has no well-formed payload (`Enc.WF`). -/
theorem Opt.ne_general {t : QAtomicType} {n : USize} (x : Opt t n) : t ≠ .general := by
  rintro rfl; have hw := x.wf
  cases hc : x.enc <;> (rw [hc] at hw; simp only [Enc.WF] at hw) <;> exact absurd hw.1 (by decide)

/-- `Opt.get` is the null where the block says so: the test `leafFill` makes, `Opt.isNulWith` at the column's starts. -/
theorem Opt.get_none_iff {t : QAtomicType} {n : USize} (x : Opt t n) (i : Fin n.toNat) :
    x.get i = none ↔ x.isNulWith x.enc.starts i = true := by
  rw [← Opt.getWith_starts]
  by_cases h : x.isNulWith x.enc.starts i = true <;> simp [Opt.getWith, h]

/-- **`leafFill` that returned owns every row `own` owns (where `dense`) and nulls every row it does not.** -/
theorem leafFill_ok {t : QAtomicType} {n : USize} {path : String} {own : Array Bool} {dense : Bool} {x : Opt t n}
    {u : PUnit} {s s' : Void IO.RealWorld} (h : leafFill path own dense x s = .ok u s') (i : Fin n.toNat) :
    (own.getD i true = true → dense = true → x.get i ≠ none) ∧ (own.getD i true = false → x.get i = none) := by
  unfold leafFill at h
  have hi := rowsOk_ok h i.1 i.2
  simp only [ne_eq, Opt.get_none_iff]
  refine ⟨fun ho hd hn => ?_, fun ho => ?_⟩
  · simp [ho, hd, hn] at hi
  · refine Classical.byContradiction fun hn => ?_
    simp [ho, hn] at hi

/-- **`colFill` that returned gives `ColB.OwnedOn`** over the rows `own` owns. -/
theorem colFill_ok {o : Bool} {t : QAtomicType} {n : USize} {path : String} {own : Array Bool} {x : ColB o t n}
    {u : PUnit} {s s' : Void IO.RealWorld} (h : colFill path own x s = .ok u s') {P : Fin n.toNat → Prop}
    (hP : ∀ i, P i ↔ own.getD i.1 true = true) : ColB.OwnedOn x P := by
  cases o
  · trivial
  · simp only [colFill] at h
    intro i
    refine ⟨fun hp => (leafFill_ok h i).1 ((hP i).1 hp) rfl, fun hp => ?_⟩
    have ho : own.getD i.1 true = false := by
      cases e : own.getD i.1 true
      · rfl
      · exact absurd ((hP i).2 e) hp
    rw [(leafFill_ok h i).2 ho]
    have hg := Opt.ne_general x
    clear h hP hp x
    cases t <;> first | exact absurd rfl hg | rfl

/-- A side whose cells are slices of its payload on every row, as `readValsB` checks them (`cellBadB`) and with the
payload `WFOn`, and whose summands hold such sides; what `readValsB` reads before `fillBad` says which rows are owned. -/
def _root_.Rel.ValsB.Shape : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → Prop
  | _, .atom _, _, _ => True
  | _, .one, _, _ => True
  | _, .prod _ _, _, x => ValsB.Shape x.1 ∧ ValsB.Shape x.2
  | _, .arr _, _, ⟨m, lo, hi, f⟩ => (∀ i, 0 ≤ (ColB.bound lo i).toInt ∧ (ColB.bound lo i).toInt ≤ (ColB.bound hi i).toInt ∧
      (ColB.bound hi i).toInt ≤ (m.toNat : Int)) ∧ ValsB.WFOn f fun _ => True
  | _, .sum _ _, _, s => match s.view with
    | .opt _ _ => True
    | .gen _ _ x y => ValsB.Shape x ∧ ValsB.Shape y

/-- `cellBadB` finds no bad cell exactly where every row's bounds (`ColB.bound`) are a slice. -/
theorem cellBadB_none {o : Bool} {n : USize} {m : USize} {lo hi : ColB o .i64 n} : cellBadB m lo hi = none ↔
    ∀ i, 0 ≤ (ColB.bound lo i).toInt ∧ (ColB.bound lo i).toInt ≤ (ColB.bound hi i).toInt ∧
      (ColB.bound hi i).toInt ≤ (m.toNat : Int) := by
  cases o
  · exact cellBad_none
  · simp [cellBadB, ColB.bound, List.find?_eq_none]

/-- At an owned row the bound is the row (`ColB.get`): an `Opt`'s `some` is read as it is. -/
theorem ColB.get_bound {o : Bool} {n : USize} {x : ColB o .i64 n} {P : Fin n.toNat → Prop} (h : ColB.OwnedOn x P)
    {i : Fin n.toNat} (hp : P i) : ColB.get x i = ColB.bound x i := by
  cases o
  · rfl
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 ((h i).1 hp)
    simp [ColB.get, ColB.bound, hv]

theorem tags_getD {n : USize} (tag : Arr .u1 n) (i : Fin n.toNat) : (Arr.rowsImpl tag).getD i.1 false = tag.get i := by
  rw [Arr.rowsImpl_eq]; simp [Array.getD, i.2]

theorem owns_getD {n : USize} (own tags : Array Bool) (v : Bool) (i : Fin n.toNat) :
    ((Array.range n.toNat).map fun j => own.getD j true && tags.getD j false == v).getD i.1 true =
      (own.getD i.1 true && tags.getD i.1 false == v) := by
  simp [Array.getD, i.2]

/-- **`fillBad` that returned gives `ValsB.WFOn`** over the rows `own` owns, of a side whose cells and payloads are
`Shape`d. -/
theorem fillBad_wf (dir : String) : {o : Bool} → (A : Obj) → {n : USize} → (p : String) → (own : Array Bool) →
    (s : ValsB o A n) → ValsB.Shape s → ∀ {u : PUnit} {st st' : Void IO.RealWorld}, fillBad dir p own s st = .ok u st' →
    ∀ P : Fin n.toNat → Prop, (∀ i, P i ↔ own.getD i.1 true = true) → ValsB.WFOn s P
  | _, .atom _, _, p, own, x, _, _, st, st', h, P, hP => by
    rw [fillBad] at h
    exact colFill_ok h hP
  | _, .one, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .prod a b, _, p, own, x, hS, _, st, st', h, P, hP => by
    rw [fillBad] at h
    obtain ⟨u1, s1, h1, h⟩ := io_bind_ok h
    exact ⟨fillBad_wf dir a (p ++ ".1") own x.1 hS.1 h1 P hP, fillBad_wf dir b (p ++ ".2") own x.2 hS.2 h P hP⟩
  | _, .arr b, _, p, own, ⟨m, lo, hi, f⟩, hS, _, st, st', h, P, hP => by
    rw [fillBad] at h
    obtain ⟨u1, s1, h1, h⟩ := io_bind_ok h
    have hl := colFill_ok h1 hP
    have hh := colFill_ok h hP
    exact ⟨hl, hh, fun i hp => by rw [ColB.get_bound hl hp, ColB.get_bound hh hp]; exact hS.1 i, hS.2⟩
  | _, .sum a b, n, p, own, s, hS, _, st, st', h, P, hP => by
    rw [fillBad] at h
    simp only [ValsB.Shape] at hS
    cases hv : s.view with
    | opt hb x =>
      simp only [hv] at h
      simp only [ValsB.WFOn, hv]
      intro i hp
      refine (leafFill_ok h i).2 ?_
      cases e : own.getD i.1 true
      · rfl
      · exact absurd ((hP i).2 e) hp
    | gen hb tag x y =>
      simp only [hv] at h hS
      simp only [ValsB.WFOn, hv]
      obtain ⟨u1, s1, h1, h⟩ := io_bind_ok h
      obtain ⟨u2, s2, h2, h3⟩ := io_bind_ok h
      refine ⟨fun i hp => ?_, fillBad_wf dir a (p ++ ".l") _ x hS.1 h2 _ fun i => ?_,
        fillBad_wf dir b (p ++ ".r") _ y hS.2 h3 _ fun i => ?_⟩
      · have ht := rowsOk_ok h1 i.1 i.2
        have ho : own.getD i.1 true = false := by
          cases e : own.getD i.1 true
          · rfl
          · exact absurd ((hP i).2 e) hp
        refine Classical.byContradiction fun hn => ?_
        rw [tags_getD] at ht
        simp [ho, hn] at ht
      · rw [owns_getD, tags_getD, hP i]; simp
      · rw [owns_getD, tags_getD, hP i]; simp

theorem readValsB_wf : (o : Bool) → (A : Obj) → ∀ {dir p : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × ValsB o A n}, readValsB o A dir p s = .ok r s' →
    ValsB.Shape r.2.2 ∧ (o = false → ValsB.WFOn r.2.2 fun _ => True)
  | o, .atom t, dir, p, s, s', r, h => by
    rw [readValsB] at h
    obtain ⟨a, s1, -, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    exact ⟨trivial, fun ho => by subst ho; trivial⟩
  | o, .one, dir, p, s, s', r, h => ⟨trivial, fun _ => trivial⟩
  | o, .prod a b, dir, p, s, s', r, h => by
    rw [readValsB] at h
    obtain ⟨⟨fx, n, x⟩, s1, h1, h⟩ := io_bind_ok h
    obtain ⟨⟨fy, y⟩, s2, h2, h⟩ := io_bind_ok h
    obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    obtain ⟨hh, rfl⟩ := same_ok h3
    obtain ⟨m, y⟩ := y
    simp only at hh; subst hh
    have h1' := readValsB_wf o a h1
    have h2' := readValsB_wf o b h2
    exact ⟨⟨h1'.1, h2'.1⟩, fun ho => ⟨h1'.2 ho, h2'.2 ho⟩⟩
  | o, .arr b, dir, p, s, s', r, h => by
    rw [readValsB] at h
    obtain ⟨⟨n, lo⟩, s1, h1, h⟩ := io_bind_ok h
    obtain ⟨⟨k, hi⟩, s2, h2, h⟩ := io_bind_ok h
    obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
    obtain ⟨hh, rfl⟩ := same_ok h3
    simp only at hh; subst hh
    obtain ⟨⟨fe, m, e⟩, s4, h4, h⟩ := io_bind_ok h
    cases hc : cellBadB m lo hi with
    | some i =>
      simp only [hc] at h
      obtain ⟨y, s5, h5, -⟩ := io_bind_ok h
      exact (io_throw_ne h5).elim
    | none =>
      simp only [hc] at h
      obtain ⟨y, s5, h5, h⟩ := io_bind_ok h
      have := io_pure_ok h; subst this
      have hb := cellBadB_none.1 hc
      have h4' := (readValsB_wf false b h4).2 rfl
      exact ⟨⟨hb, h4'⟩, fun ho => by subst ho; exact ⟨trivial, trivial, fun i _ => hb i, h4'⟩⟩
  | o, .sum a b, dir, p, s, s', r, h => by
    rw [readValsB] at h
    cases hb : Obj.band a b with
    | some t =>
      rw [match17_some hb] at h
      obtain ⟨⟨n, x⟩, s1, h1, h⟩ := io_bind_ok h
      have := io_pure_ok h; subst this
      refine ⟨by simp only [ValsB.Shape, ValsB.view_ofOpt], fun _ => ?_⟩
      simp only [ValsB.WFOn, ValsB.view_ofOpt]
      exact fun i hi => absurd trivial hi
    | none =>
      rw [match17_none hb] at h
      obtain ⟨⟨n, tag⟩, s1, h1, h⟩ := io_bind_ok h
      obtain ⟨⟨fa, na, xa⟩, s2, h2, h⟩ := io_bind_ok h
      obtain ⟨⟨fb, nb, xb⟩, s3, h3, h⟩ := io_bind_ok h
      obtain ⟨x, s4, h4, h⟩ := io_bind_ok h
      obtain ⟨y, s5, h5, h⟩ := io_bind_ok h
      obtain ⟨ha, rfl⟩ := same_ok h4
      obtain ⟨hh, rfl⟩ := same_ok h5
      simp only at ha hh; subst ha; subst hh
      have hS : ValsB.Shape (ValsB.ofGen (o := o) hb tag xa xb) := by
        simp only [ValsB.Shape, ValsB.view_ofGen]
        exact ⟨(readValsB_wf true a h2).1, (readValsB_wf true b h3).1⟩
      cases o
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨u, s6, h6, h⟩ := io_bind_ok h
        have := io_pure_ok h; subst this
        exact ⟨hS, fun _ => fillBad_wf dir (.sum a b) p _ _ hS h6 _ fun i => iff_of_true trivial (by simp)⟩
      · simp only [↓reduceIte] at h
        obtain ⟨u, s6, h6, h⟩ := io_bind_ok h
        have := io_pure_ok h; subst this
        exact ⟨hS, fun ho => absurd ho (by simp)⟩


/-- `IO.ofExcept` that returns ran an `Except` that returned the same. -/
theorem ofExcept_ok {α : Type} {e : Except String α} {a : α} {s s' : Void IO.RealWorld}
    (h : IO.ofExcept e s = .ok a s') : e = .ok a := by
  unfold IO.ofExcept at h
  cases e with
  | error m => simp [throw, throwThe, MonadExceptOf.throw, EST.throw] at h
  | ok u => simp only [pure, EST.pure] at h; cases h; rfl

/-- `readCols` establishes `Vals.WF` of the columns it reads. -/
theorem readCols_wf : (R : Schema) → ∀ {dir : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × Vals (Schema.objR .long .prod R) n}, readCols dir R s = .ok r s' →
    ValsB.WFOn r.2.2 fun _ => True
  | [], dir, s, s', r, h => by rw [readCols] at h; exact (io_throw_ne h).elim
  | [f], dir, s, s', r, h => by
    rw [readCols] at h; exact (readValsB_wf false f.2 h).2 rfl
  | f :: g :: R, dir, s, s', r, h => by
    rw [readCols] at h
    obtain ⟨⟨fx, n, x⟩, s1, h1, h⟩ := io_bind_ok h
    obtain ⟨⟨fy, y⟩, s2, h2, h⟩ := io_bind_ok h
    obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    obtain ⟨hh, rfl⟩ := same_ok h3
    obtain ⟨m, y⟩ := y
    simp only at hh; subst hh
    exact ⟨readCols_wf (g :: R) h1,
      (readValsB_wf false f.2 h2).2 rfl⟩

/-- `readSide` establishes `Vals.WF` of the side it reads. -/
theorem readSide_wf {S : Schema} {dir : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × Vals S.obj n} (h : readSide S dir s = .ok r s') : ValsB.WFOn r.2.2 fun _ => True := by
  rw [readSide] at h
  obtain ⟨-, s1, -, h⟩ := io_bind_ok h
  obtain ⟨-, s2, -, h⟩ := io_bind_ok h
  exact readCols_wf S.reverse h

/-- `frame` of a side holds `Tab.WF` of it. -/
theorem frame_wf {B : Obj} {n : USize} {x : Vals B n} {t : Tab .long B} (h : frame x = .ok t) (hx : Vals.WF x) :
    Tab.WF t := by
  unfold frame at h
  cases hp : Arr.pos n with
  | error m => rw [hp] at h; cases h
  | ok P => rw [hp] at h; cases h; exact ⟨trivial, hx⟩

/-- **`Table.read` establishes `Tab.WF`**: the cell bounds of its arrays are
checked at load (`cellBadB`) and a dense sum's summands by `fillBad`. -/
theorem read_wf {S : Schema} {dir : String} {s s' : Void IO.RealWorld}
    {t : Tab .long S.obj} (h : read S dir s = .ok t s') : Tab.WF t := by
  rw [read] at h
  obtain ⟨⟨fe, m, x⟩, s1, h1, h⟩ := io_bind_ok h
  exact frame_wf (ofExcept_ok h) (readSide_wf h1)

/-- **`Table.readKeyed` establishes `Tab.WF`.** -/
theorem readKeyed_wf {K S : Schema} {dir : String}
    {s s' : Void IO.RealWorld} {t : Tab K.obj S.obj} (h : readKeyed K S dir s = .ok t s') : Tab.WF t := by
  rw [readKeyed] at h
  obtain ⟨⟨fk, n, k⟩, s1, h1, h⟩ := io_bind_ok h
  obtain ⟨⟨fv, v⟩, s2, h2, h⟩ := io_bind_ok h
  obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
  obtain ⟨hh, rfl⟩ := same_ok h3
  obtain ⟨m, v⟩ := v
  simp only at hh; subst hh
  have hc := ofExcept_ok h
  unfold canon at hc
  cases hq : Tab.canon ⟨m, k, v⟩ with
  | error e => simp [hq, Except.mapError] at hc
  | ok u => simp only [hq, Except.mapError] at hc; cases hc; exact Tab.canon_wf hq ⟨readSide_wf h1, readSide_wf h2⟩

/-- **`Table.readOwn` keeps `Tab.WF`** of the reader it wraps. -/
theorem readOwn_wf {A B : Obj} {D : Dict} {dir : String} {r : IO (Tab A B)}
    (hr : ∀ s s' t, r s = .ok t s' → Tab.WF t) {s s' : Void IO.RealWorld} {t : Tab A B}
    (h : readOwn D dir r s = .ok t s') : Tab.WF t := by
  rw [readOwn] at h
  obtain ⟨u, s1, h1, h⟩ := io_bind_ok h
  obtain ⟨-, s2, -, h⟩ := io_bind_ok h
  have := io_pure_ok h; subst this
  exact hr s s1 u h1

end Rel.Lang.Table
