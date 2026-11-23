module

public import Rel.Run.Gather

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! Duplicate removal and canonical form as a composition of the five kernels (PLAN 6.14 W2), at the `Tab → Tab`
boundary, on the encoded columns as they are: `kasc` sorts a side's atom columns and answers the permutation `p`,
`kseen` on the sorted columns answers the first row of each run of equal rows, `kgather` reads `p` there, and every
column is `kgather`ed at those rows. No column is decoded or re-encoded between the calls: each kernel's answer is the
next one's argument (`Rel.Verify.kgather_closed` and the other closure laws).

An `arr` side is one `cells` key (`AscKey`) over its payload's columns, gathered by its `lo` and `hi`. An atom column
the kernels do not read (any encoding but `foR`) is the error that names it: those producers move to `foR` in the next package. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- A summand's columns at its sum side's `n` rows: `cols` of the summand `y` gathered at the positions `p`; a summand
of no rows has no columns, and a position outside it is the error naming the `side`. -/
def Vals.summandCols {B : Obj} {n m : USize} (side : String) (cols : Vals B n → Except String (List (AscKey × Enc)))
    (p : Enc) (y : Vals B m) : Except String (List (AscKey × Enc)) :=
  if m.toNat = 0 then .ok [] else match Vals.gather n p y with
    | .ok g => cols g
    | .error s => .error s!"cols: a sum side's {side} position: {s}"

/-- The key columns of a side (`AscKey`), in the order of `Vals.row`'s tuple. An `arr` side is one `cells` key over its
`lo`, `hi` and its payload's columns, row `i` naming cell `i` (`.pos`), so equal codes are equal cells as lists. A
`sum` side is its tag negated (`¬tag`: `inr` first), then the left summand's columns gathered at `idx * not(tag)`, then the right's at `idx * tag`
(`Vals.summandCols`): a row of the other summand reads that summand's row `0`, a constant, so equal codes are equal
rows. A summand past `2^63` rows, which an `Int64` position cannot reach, is the error. -/
def Vals.cols : {A : Obj} → {n : USize} → Vals A n → Except String (List (AscKey × Enc))
  | .atom t, _, x => .ok [(.atom t, Arr.enc (t := t) x)]
  | .prod _ _, _, x => do pure ((← Vals.cols x.1) ++ (← Vals.cols x.2))
  | .arr _, n, ⟨c, lo, hi, f⟩ => do pure [(.cells n c lo.enc hi.enc (← Vals.cols f), .pos)]
  -- a band column is its own key: `kasc` codes its nulls first (`Asc.nulCodes`), as `Obj.key` puts `inr` first
  | .sum _ _, n, s => match s.view with
    | .opt (t := t) _ x => .ok [(.atom t, x.enc)]
    | .gen _ l r tag idx x y =>
    if 2 ^ 63 < l.toNat ∨ 2 ^ 63 < r.toNat then .error s!"cols: a sum side of {l} and {r} rows, past an Int64 position"
    -- `idx` is read here only by `colMap`, which takes more forms than `kgather` (`Vals.gather`); a side numbered
    -- here must be one every kernel reads; so must `tag`, which `kasc` no longer sees (it reads `¬tag`)
    else if !foROk n idx.enc then
      .error s!"cols: a sum side's idx column (constructor {idx.enc.ctorIdx}) is no foR column of {n} rows"
    else if !foROk n tag.enc then
      .error s!"cols: a sum side's tag column (constructor {tag.enc.ctorIdx}) is no foR column of {n} rows"
    else do
      -- the key is `¬tag`, so `inr` (tag `1`) sorts first (`Obj.key`): q's null before every value
      let nt ← colMap .not n tag.enc tag.enc .u1
      let px ← colMap .mul n idx.enc nt
      let py ← colMap .mul n idx.enc tag.enc
      pure ((.atom .u1, nt) ::
        ((← Vals.summandCols (n := n) "left" Vals.cols px x) ++ (← Vals.summandCols (n := n) "right" Vals.cols py y)))
  -- no column: every row of `1` is its one value
  | .one, _, _ => .ok []

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

/-- **`r` is canonical**: `canon`'s answer on some table, so sorted and duplicate-free (`canon_sorted`,
`canon_distinct`). A proof, decided where `r` is produced; a consumer that would `canon` its input has an `…Of` form
taking such an `r` (`lamOf`), so no kernel runs on a table known canonical. -/
def Canonical (r : Tab k v) : Prop := ∃ U : Tab k v, U.canon = .ok r

/-- **The range of `R`**, `𝟙 ∩ R° ≫ R°°`: the value side without duplicates (`Vals.nub`), each row paired with
itself. -/
def ran (R : Tab k v) : Except String (Tab v v) := (fun y => ⟨y.1, y.2, y.2⟩) <$> Vals.nub R.val

/-- **The domain of `R`**, `𝟙 ∩ R ≫ R°`: the key side without duplicates, each row paired with itself. -/
def dom (R : Tab k v) : Except String (Tab k k) := (fun y => ⟨y.1, y.2, y.2⟩) <$> Vals.nub R.key

end Tab

end Rel
