import Rel.Run.Core
import Rel.Kernel.Seen
import Rel.KernelSpec.Closure

/-! Duplicate removal and canonical form as a composition of the five kernels (PLAN 6.14 W2), at the `Tab → Tab`
boundary, on the encoded columns as they are: `kasc` sorts a side's atom columns and answers the permutation `p`,
`kseen` on the sorted columns answers the first row of each run of equal rows, `kgather` reads `p` there, and every
column is `kgather`ed at those rows. No column is decoded or re-encoded between the calls: each kernel's answer is the
next one's argument (`Rel.Verify.kgather_closed` and the other closure laws).

A side of `arr` atoms, and an atom column the kernels do not read (any encoding but `foR`), is the error that
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
  | pos =>
    -- `pos` is a column only at `i64` (`Enc.WF`), where the gathered words need no bound
    cases t <;> simp only [Enc.WF] at hw
    exact (wordsFoR_closed _ (by rw [Array.size_map, his])).2.2 rfl (fun h => absurd h (by decide))
  | _ => all_goals simp only [Kernel.Enc.Valid] at hv

/-- `n` cells holding the word `w`: `kscatter` of no rows. -/
def colConst (n : USize) (w : UInt64) : Except String Enc := kscatter .last 0 .pos .pos n w

/-- `op` row by row over the `n` words of `a` and `b`, `out[i] = op(a[i], b[i])` written at `t`: `kscan` with every row
starting a segment (`colConst n 1`). -/
def colMap (op : Op) (n : USize) (a b : Enc) (t : QAtomicType := .i64) : Except String Enc := do
  kscan op false .i64 t n (← colConst n 1) [a, b]

/-- `colMap`'s answer is a column every kernel reads, `Enc.WF` at `t` (`kscan_closed`). -/
theorem colMap_closed {op : Op} {n : USize} {a b o : Enc} {t : QAtomicType} (h : colMap op n a b t = .ok o) :
    Kernel.Enc.Valid n o ∧ Enc.WF t n o := by
  unfold colMap at h; simp only [bind, Except.bind] at h; split at h; · cases h
  exact kscan_closed h

/-- The rows `ix` (`m` positions) of the column `x`: `kgather` at `ix`, an `Arr` again by `Arr.kgather_wf`. -/
def Arr.gather {t : QAtomicType} {n : USize} (m : USize) (ix : Enc) (x : Arr t n) : Except String (Arr t m) :=
  match h : kgather m ix n x.enc with
  | .ok o => .ok (Arr.mk o (Arr.kgather_wf x h))
  | .error s => .error s

/-- The rows `ix` (`m` positions) of the side `x`: each atom column `Arr.gather`ed at `ix`; a `sum` side gathers its tag
and position columns and keeps both summands. -/
def Vals.gather (m : USize) (ix : Enc) : {A : Obj} → {n : USize} → Vals A n → Except String (Vals A m)
  | .atom _, _, x => Arr.gather m ix x
  | .prod _ _, _, x => do pure (← Vals.gather m ix x.1, ← Vals.gather m ix x.2)
  | .arr _, _, _ => .error "gather: an arr side is not atom columns"
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩ => do pure ⟨l, r, ← Arr.gather m ix tag, ← Arr.gather m ix idx, x, y⟩

/-- A summand's columns at its sum side's `n` rows: `cols` of the summand `y` gathered at the positions `p`; a summand
of no rows has no columns, and a position outside it is the error naming the `side`. -/
def Vals.summandCols {B : Obj} {n m : USize} (side : String) (cols : Vals B n → Except String (List (AscKey × Enc)))
    (p : Enc) (y : Vals B m) : Except String (List (AscKey × Enc)) :=
  if m.toNat = 0 then .ok [] else match Vals.gather n p y with
    | .ok g => cols g
    | .error s => .error s!"cols: a sum side's {side} position: {s}"

/-- The atom columns of a side, each with its type, in the order of `Vals.row`'s tuple. A `sum` side is its tag, then
the left summand's columns gathered at `idx * not(tag)`, then the right's at `idx * tag` (`Vals.summandCols`): a row of
the other summand reads that summand's row `0`, a constant, so equal codes are equal rows. A summand past `2^63` rows,
which an `Int64` position cannot reach, is the error, as is an `arr` side. -/
def Vals.cols : {A : Obj} → {n : USize} → Vals A n → Except String (List (AscKey × Enc))
  | .atom t, _, x => .ok [(.atom t, Arr.enc (t := t) x)]
  | .prod _ _, _, x => do pure ((← Vals.cols x.1) ++ (← Vals.cols x.2))
  | .arr _, _, _ => .error "cols: an arr side is not atom columns"
  | .sum _ _, n, ⟨l, r, tag, idx, x, y⟩ =>
    if 2 ^ 63 < l.toNat ∨ 2 ^ 63 < r.toNat then .error s!"cols: a sum side of {l} and {r} rows, past an Int64 position"
    else do
      let px ← colMap .mul n idx.enc (← colMap .not n tag.enc tag.enc)
      let py ← colMap .mul n idx.enc tag.enc
      pure ((.atom .u1, tag.enc) ::
        ((← Vals.summandCols (n := n) "left" Vals.cols px x) ++ (← Vals.summandCols (n := n) "right" Vals.cols py y)))

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
