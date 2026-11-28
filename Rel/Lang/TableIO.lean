module

public import Rel.Run.Table
import all Init.System.ST
import all Init.System.IO

/-! The `IO` monad's operations (`EST.pure`, `EST.throw`, `IO.ofExcept`) have no exposed body, so a `module` file
unfolds them only through `import all` of their modules. -/

namespace Rel.Lang.Table

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

end Rel.Lang.Table
