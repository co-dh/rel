module

public import Std.Data.HashSet
public import Rel.Kernel.Dep.Val
public import Rel.KernelSpec.Elementwise
public import Rel.Kernel.Eval.Val
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Dep.Monadic` the Rel kernels reach; `Rel.Dep.Monadic` imports it. -/


namespace Rel.Dep

open Rel Rel.Eval

/-- The null of a type, at the index. `Verify.nullAtom_type` is what makes it total: q's null
of `t` really is an atom of `t`. -/
def Carrier.null (t : QAtomicType) (hn : t ≠ .general := by first | decide | assumption) :
    Carrier t :=
  (Carrier.of? t (.atom (nullAtom t))).get (by
    have h := Carrier.of?_type (X := Empty) (nullAtom t)
    rwa [Verify.nullAtom_type] at h)

/-- Every carrier is inhabited: by its q null, which is also the right default for the
out-of-range reads below since that is what q answers for them, and a general list's element by
`default : QValue`, a general list's fill depending on its elements rather than on its type. -/
instance {t : QAtomicType} : Inhabited (Carrier t) :=
  if hg : t = .general then ⟨hg ▸ (default : QValue)⟩ else ⟨Carrier.null t hg⟩

end Rel.Dep

namespace Rel.Dep

end Rel.Dep
