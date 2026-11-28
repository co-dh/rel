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

/-- The sides of a table with no dense sum: every sum is a band column, so `readValsB` reads no summand. -/
def _root_.Rel.Obj.noGen : Obj → Prop
  | .atom _ | .one => True
  | .prod a b => a.noGen ∧ b.noGen
  | .arr b => b.noGen
  | .sum a b => (Obj.band a b).isSome

/-- A `match h : d with` on an option known to be `some t` takes its `some` alternative. -/
theorem match17_some {β : Sort u} {d : Option QAtomicType} {t : QAtomicType}
    {f : (t : QAtomicType) → d = some t → β} {g : d = none → β} (hd : d = some t) :
    readValsB.match_17 (fun _ => β) d f g = f t hd := by subst hd; rfl

theorem readValsB_wf : (A : Obj) → A.noGen → ∀ {dir p : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × ValsB false A n}, readValsB false A dir p s = .ok r s' →
    ValsB.WFOn r.2.2 fun _ => True
  | .atom t, _, dir, p, s, s', r, h => by
    rw [readValsB] at h
    obtain ⟨a, s1, -, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this; exact trivial
  | .one, _, dir, p, s, s', r, h => trivial
  | .prod a b, hA, dir, p, s, s', r, h => by
    rw [readValsB] at h
    obtain ⟨⟨fx, n, x⟩, s1, h1, h⟩ := io_bind_ok h
    obtain ⟨⟨fy, y⟩, s2, h2, h⟩ := io_bind_ok h
    obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    obtain ⟨hh, rfl⟩ := same_ok h3
    obtain ⟨m, y⟩ := y
    simp only at hh; subst hh
    exact ⟨readValsB_wf a hA.1 h1, readValsB_wf b hA.2 h2⟩
  | .arr b, hA, dir, p, s, s', r, h => by
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
      exact ⟨trivial, trivial, fun i _ => cellBad_none.1 hc i, readValsB_wf b hA h4⟩
  | .sum a b, hA, dir, p, s, s', r, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hA
    rw [readValsB] at h
    rw [match17_some ht] at h
    obtain ⟨⟨n, x⟩, s1, h1, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    simp only [ValsB.WFOn, ValsB.view_ofOpt]
    exact fun i hi => absurd trivial hi

/-- `IO.ofExcept` that returns ran an `Except` that returned the same. -/
theorem ofExcept_ok {α : Type} {e : Except String α} {a : α} {s s' : Void IO.RealWorld}
    (h : IO.ofExcept e s = .ok a s') : e = .ok a := by
  unfold IO.ofExcept at h
  cases e with
  | error m => simp [throw, throwThe, MonadExceptOf.throw, EST.throw] at h
  | ok u => simp only [pure, EST.pure] at h; cases h; rfl

/-- `readCols` of columns that hold no dense sum. -/
theorem readCols_wf : (R : Schema) → (∀ f ∈ R, f.2.noGen) → ∀ {dir : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × Vals (Schema.objR .long .prod R) n}, readCols dir R s = .ok r s' →
    ValsB.WFOn r.2.2 fun _ => True
  | [], _, dir, s, s', r, h => by rw [readCols] at h; exact (io_throw_ne h).elim
  | [f], hR, dir, s, s', r, h => by
    rw [readCols] at h; exact readValsB_wf f.2 (hR f (by simp)) h
  | f :: g :: R, hR, dir, s, s', r, h => by
    rw [readCols] at h
    obtain ⟨⟨fx, n, x⟩, s1, h1, h⟩ := io_bind_ok h
    obtain ⟨⟨fy, y⟩, s2, h2, h⟩ := io_bind_ok h
    obtain ⟨z, s3, h3, h⟩ := io_bind_ok h
    have := io_pure_ok h; subst this
    obtain ⟨hh, rfl⟩ := same_ok h3
    obtain ⟨m, y⟩ := y
    simp only at hh; subst hh
    exact ⟨readCols_wf (g :: R) (fun f hf => hR f (List.mem_cons_of_mem _ hf)) h1,
      readValsB_wf f.2 (hR f (by simp)) h2⟩

/-- `readSide` of a schema with no dense sum. -/
theorem readSide_wf {S : Schema} (hS : ∀ f ∈ S, f.2.noGen) {dir : String} {s s' : Void IO.RealWorld}
    {r : String × (n : USize) × Vals S.obj n} (h : readSide S dir s = .ok r s') : ValsB.WFOn r.2.2 fun _ => True := by
  rw [readSide] at h
  obtain ⟨-, s1, -, h⟩ := io_bind_ok h
  obtain ⟨-, s2, -, h⟩ := io_bind_ok h
  exact readCols_wf S.reverse (fun f hf => hS f (List.mem_reverse.1 hf)) h

/-- `frame` of a side holds `Tab.WF` of it. -/
theorem frame_wf {B : Obj} {n : USize} {x : Vals B n} {t : Tab .long B} (h : frame x = .ok t) (hx : Vals.WF x) :
    Tab.WF t := by
  unfold frame at h
  cases hp : Arr.pos n with
  | error m => rw [hp] at h; cases h
  | ok P => rw [hp] at h; cases h; exact ⟨trivial, hx⟩

/-- **`Table.read` establishes `Tab.WF`** for a schema with no dense sum (`Obj.noGen`): the cell bounds of its arrays are
checked at load (`cellBadB`), and a band sum has no clause. -/
theorem read_wf {S : Schema} (hS : ∀ f ∈ S, f.2.noGen) {dir : String} {s s' : Void IO.RealWorld}
    {t : Tab .long S.obj} (h : read S dir s = .ok t s') : Tab.WF t := by
  rw [read] at h
  obtain ⟨⟨fe, m, x⟩, s1, h1, h⟩ := io_bind_ok h
  exact frame_wf (ofExcept_ok h) (readSide_wf hS h1)

/-- **`Table.readKeyed` establishes `Tab.WF`** for key and value schemas with no dense sum. -/
theorem readKeyed_wf {K S : Schema} (hK : ∀ f ∈ K, f.2.noGen) (hS : ∀ f ∈ S, f.2.noGen) {dir : String}
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
  | ok u => simp only [hq, Except.mapError] at hc; cases hc; exact Tab.canon_wf hq ⟨readSide_wf hK h1, readSide_wf hS h2⟩

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
