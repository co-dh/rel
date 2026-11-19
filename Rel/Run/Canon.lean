import Rel.Run.Core
import Rel.Kernel.Seen
import Rel.KernelSpec.Closure

/-! Duplicate removal and canonical form as a composition of the five kernels (PLAN 6.14 W2), at the `Tab → Tab`
boundary, on the encoded columns as they are: `kasc` sorts a side's atom columns and answers the permutation `p`,
`kseen` on the sorted columns answers the first row of each run of equal rows, `kgather` reads `p` there, and every
column is `kgather`ed at those rows. No column is decoded or re-encoded between the calls: each kernel's answer is the
next one's argument (`Rel.Verify.kgather_closed` and the other closure laws).

A side of `arr` or `sum` atoms, and an atom column the kernels do not read (any encoding but `foR`), is the error that
names it: those producers move to `foR` in the next package. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The source column of a successful `kgather` is one every kernel reads (`foRWords` accepted it). -/
theorem kgather_valid {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) : Kernel.Enc.Valid n e := by
  unfold kgather at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i ws hws
  exact (foRWords_valid _ _ _).2 _ hws

/-- **A gathered `Arr` is an `Arr` of its type**: the source is a valid column under `Enc.WF`, so a `foR` one at a type
with a width, whose words at `u1` are below `2`; the gathered words are some of them. -/
theorem Arr.kgather_wf {t : QAtomicType} {n m : USize} {ix o : Enc} (x : Arr t n) (h : kgather m ix n x.enc = .ok o) :
    Enc.WF t m o := by
  have hv := kgather_valid h
  obtain ⟨his, -, hlt, rfl⟩ := raw_kgather m ix n x.enc o h
  have hw := x.wf
  generalize x.enc = e at hv hw hlt ⊢
  cases e with
  | foR md pk =>
    have hw' : t.width.isSome = true ∧
        (t = .u1 → ∀ i < n.toNat, (Column.foRBits md pk (Column.blockStarts md) i).toNat < 2) := by
      cases t <;> simp only [Enc.WF] at hw <;>
        first | exact ⟨hw.1, hw.2.1⟩ | exact ⟨hw.1, fun _ => hw.2.1 trivial⟩ | exact ⟨hw.1, fun h => absurd h (by decide)⟩
    refine (wordsFoR_closed _ (by rw [Array.size_map, his])).2.2 hw'.1 fun hu k hk => ?_
    rw [Array.size_map] at hk
    have hi := hlt k (by omega)
    rw [Array.getElem?_eq_getElem hk, Option.getD_some] at hi
    simp only [Array.getElem_map, raw_foR .i64 8 rfl (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map,
      Array.getElem?_range, hi, if_true, Option.map_some, Option.getD_some, Nat.reduceMul, ofNat_toNat_mod64]
    exact UInt64.lt_iff_toNat_lt.2 (hw'.2 hu _ hi)
  | pos => cases t <;> simp only [Enc.WF] at hw
  | _ => all_goals simp only [Kernel.Enc.Valid] at hv

/-- The atom columns of a side, each with its type, in the order of `Vals.row`'s tuple; a side holding an `arr` or a
`sum` is the error, which no kernel reads as one column. -/
def Vals.cols : {A : Obj} → {n : USize} → Vals A n → Except String (List (QAtomicType × Enc))
  | .atom t, _, x => .ok [(t, Arr.enc (t := t) x)]
  | .prod _ _, _, x => do pure ((← Vals.cols x.1) ++ (← Vals.cols x.2))
  | .arr _, _, _ => .error "cols: an arr side is not atom columns"
  | .sum _ _, _, _ => .error "cols: a sum side is not atom columns"

/-- The rows `ix` (`m` positions) of the side `x`: each atom column `kgather`ed at `ix`, an `Arr` again by
`Arr.kgather_wf`. -/
def Vals.gather (m : USize) (ix : Enc) : {A : Obj} → {n : USize} → Vals A n → Except String (Vals A m)
  | .atom t, n, x => match h : kgather m ix n (Arr.enc (t := t) x) with
    | .ok o => .ok (Arr.mk o (Arr.kgather_wf x h))
    | .error s => .error s
  | .prod _ _, _, x => do pure (← Vals.gather m ix x.1, ← Vals.gather m ix x.2)
  | .arr _, _, _ => .error "gather: an arr side is not atom columns"
  | .sum _ _, _, _ => .error "gather: a sum side is not atom columns"

/-- **The side `x` without duplicate rows, ascending**: `kasc` over its atom columns (sorted columns `vs`, permutation
`p`), `kseen` over the sorted columns (the first row of each run of equal rows, `k` of them, ascending), `kgather` of
`p` at those rows (each run's first input row), and `x` gathered there. Rows are equal where their order codes are
(`kasc`'s equality). -/
def Vals.nub {A : Obj} {n : USize} (x : Vals A n) : Except String ((m : USize) × Vals A m) := do
  let es ← Vals.cols x
  let (vs, p) ← kasc n es
  let (k, _, f) ← kseen n ((es.map (·.1)).zip vs)
  let ix ← kgather k.toUSize f n p
  (⟨k.toUSize, ·⟩) <$> Vals.gather k.toUSize ix x

namespace Tab
variable {k v : Obj}

/-- **`R` in canonical form**: `Vals.nub` of the pair side `k × v`, whose columns are the key's and the value's. -/
def canon (R : Tab k v) : Except String (Tab k v) :=
  (fun y => ⟨y.1, y.2.1, y.2.2⟩) <$> Vals.nub (A := .prod k v) (R.key, R.val)

/-- **The range of `R`**, `𝟙 ∩ R° ≫ R°°`: the value side without duplicates (`Vals.nub`), each row paired with
itself. -/
def ran (R : Tab k v) : Except String (Tab v v) := (fun y => ⟨y.1, y.2, y.2⟩) <$> Vals.nub R.val

/-- **The domain of `R`**, `𝟙 ∩ R ≫ R°`: the key side without duplicates, each row paired with itself. -/
def dom (R : Tab k v) : Except String (Tab k k) := (fun y => ⟨y.1, y.2, y.2⟩) <$> Vals.nub R.key

end Tab

end Rel
