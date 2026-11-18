import Rel.Run.Alg
import Rel.Run.Core

section
namespace Rel

/-- A relation, present where every op that built it ran within capacity. -/
abbrev CRel (k v : Obj) := Option (Tab k v)

/-- Whether every op that built it ran within capacity. -/
def CRel.ok {k v : Obj} (c : CRel k v) : Bool := c.isSome            -- temporary, removed in 3.12
/-- The table, `default` (`𝟘`) where a run stopped. -/
def CRel.rel {k v : Obj} (c : CRel k v) : Tab k v := c.getD default   -- temporary, removed in 3.12
/-- The table where `ok`, `none` otherwise. -/
def CRel.mk {k v : Obj} (r : Tab k v) (ok : Bool) : CRel k v := if ok then some r else none   -- temporary

@[simp] theorem CRel.mk_ok {k v : Obj} (r : Tab k v) (b : Bool) : (CRel.mk r b).ok = b := by cases b <;> rfl

/-- Where its bit is set, `mk`'s table is the one given. -/
@[simp] theorem CRel.mk_rel {k v : Obj} (r : Tab k v) : (CRel.mk r true).rel = r := rfl

theorem CRel.mk_rel_of {k v : Obj} {r : Tab k v} {b : Bool} (h : (CRel.mk r b).ok = true) :
    (CRel.mk r b).rel = r := by cases b <;> first | rfl | exact absurd h Bool.false_ne_true

namespace Alg

open Tab Rel.Dep Rel.Kernel

/-- `R` in canonical form: its rows ascending by `Obj.lt` on `(key, val)` (`sortByC` of the pair side, the order
    `sortsAsc_all` proves the kernels keep), then the first of each run of equal rows (`nubC`). The bit `&&`s the
    sort's, `R`'s two sides fitting at all its rows (`fitsN`), and `nubC`'s. -/
def canonC {k v : Obj} (R : Tab k v) : Tab k v × Bool :=
  let s := (Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)
  let N := nubC (R.rows s.1)
  (N.1, s.2 && Vals.fitsN k R.key R.n.toNat && Vals.fitsN v R.val R.n.toNat && N.2)

/-- A relation from its pairs of longs, in canonical form (`canonC`), so a literal is equal data to any op's
    answer with the same pairs; a `canonC` past capacity stops with its message, as `col` does. -/
def ofPairs (ps : List (Int64 × Int64)) : Tab .long .long :=
  let c := canonC (⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩ :
    Tab .long .long)
  need (c.2 = true) (fun _ => s!"ofPairs: canonC of {ps.length} pairs ran past capacity") (fun _ => zero) fun _ => c.1

end Alg

end Rel
end

section
namespace Rel
namespace CRel
open Tab Rel.Kernel Rel.Alg
variable {A B C : Obj}

/-- A twin's answer as a `CRel`, its rows in canonical form (`canonC`): ok where the twin's bit and `canonC`'s are. -/
def ofC (r : Tab A B × Bool) : CRel A B := let c := canonC r.1; mk c.1 (r.2 && c.2)

/-- Runs the op `k` only where its inputs' bits `b` are all set; otherwise stops at `default` (`none` for a `CRel`)
    without running it, since an op on a bad input answers nothing worth its cost. -/
def guard {α : Type} [Inhabited α] (b : Bool) (k : Unit → α) : α := if b then k () else default

/-- `R ≫ S`, ok where both inputs are and `compC` ran within capacity. -/
def comp (R : CRel A B) (S : CRel B C) : CRel A C := guard (R.ok && S.ok) fun _ => ofC (compC R.rel S.rel)

/-- `R ∩ S`, ok where both inputs are and `interC` ran within capacity. Its rows are a subsequence of `R`'s, canonical
    where `R` is (`canon_inter`), so it skips `canonC`. -/
def inter (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => let r := interC R.rel S.rel; mk r.1 r.2

/-- `R ∪ S`, ok where both inputs are and `unionC` ran within capacity. -/
def union (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => ofC (unionC R.rel S.rel)

end CRel
end Rel
end
