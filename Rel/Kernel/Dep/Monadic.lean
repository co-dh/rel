import Std.Data.HashSet
import QLean.RelPart.Dep.Val
import QLean.RelPart.Verify.Elementwise
import QLean.RelPart.Eval.Val
import QLean.RelPart.Value

/-! The part of `QLean.Dep.Monadic` the Rel kernels reach; `QLean.Dep.Monadic` imports it. -/


namespace QLean.Dep

open QLean QLean.Eval

/-- The null of a type, at the index. `Verify.nullAtom_type` is what makes it total: q's null
of `t` really is an atom of `t`. -/
def Carrier.null (t : QAtomicType) (hn : t ≠ .general := by first | decide | assumption) :
    Carrier t :=
  (Carrier.of? t (.atom (nullAtom t))).get (by
    have h := Carrier.of?_type (nullAtom t)
    rwa [Verify.nullAtom_type] at h)

/-- Every carrier is inhabited: by its q null, which is also the right default for the
out-of-range reads below since that is what q answers for them, and a general list's element by
`default : QValue`, a general list's fill depending on its elements rather than on its type. -/
instance {t : QAtomicType} : Inhabited (Carrier t) :=
  if hg : t = .general then ⟨hg ▸ (default : QValue)⟩ else ⟨Carrier.null t hg⟩

end QLean.Dep

namespace QLean.Dep

end QLean.Dep
