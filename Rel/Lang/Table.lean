import Rel.Run.Lang.Plan
import Rel.Run.Lang.Schema
import Rel.Kernel.Db.ObjectFile
import Rel.RepCols
import Rel.Kernel.Cast

/-! # A table directory (PLAN D.9, `doc/dataframe-design.zh.typ` F6)

A directory is a table and a file one column: an own-format file written by `Db.ownWrite` and mapped back by
`Db.ownMap`, its parts taken as they lie, so nothing is decoded, converted or copied. A side's files are the paths
`cols` gives its atom columns under a prefix, the column's name; a positions column has no file (`Db.ownParts`), so a
frame's key `0 … n-1` is not on disk.

A side is read and written by a `Schema`: each column's files under its name. A side that is not a record is the
one-column schema named by the side, `[("key", A)]` or `[("val", B)]`. The two forms of a table on disk:

- positional, `N ⟶ S`: the value side's columns in `dir`, rows in key order, renumbered `0 … n-1`; no key file
  (`write`, `read`, the renumbering `frame_holds`);
- keyed, `K ⟶ S` with `K` not the positions (q's keyed table, a dictionary from a key table to a value table): two
  positional tables of one length, `dir/key` and `dir/val` (`writeKeyed`, `readKeyed`).

Which form a result takes is decided by its key OBJECT where the program is elaborated (`Expand.emit`), never by
reading the key column. -/

namespace Rel.Lang.Table

open Rel Rel.Lang.Plan

/-- The file of the column `q` in the table directory `dir`. -/
def file (dir q : String) : String := (System.FilePath.mk dir / q).toString

/-- The one column writer of a side: each atom column of `x` (`cols` under the prefix `p`) to `file dir <path>`; a
    positions column has no file. -/
def writeVals {A : Obj} {n : USize} (dir p : String) (x : Vals A n) : IO Unit := do
  for (q, v) in cols A x p do
    if let some f ← IO.ofExcept (ownFile q v) then
      Db.ownWrite (file dir q) f.code f.attr f.kind f.count f.domain f.parts

/-- The bit pattern of a word of type `t` that is not in the canonical form `Obj.key` and the kernels assume (typed
    base design, R7 and decision D: a NaN has no row, `-0` is `+0`), `none` for a canonical word: the stored word
    (`QAtomicType.word`) where `QAtomicType.nonCanonical`, the one predicate, holds of it. -/
def nonCanonical (t : QAtomicType) (b : El t) : Option Nat :=
  if t.nonCanonical (t.word b) then some (t.word b).toNat else none

/-- The atom column of type `t` mapped from `path`: the header's type code and domain checked, the parts taken as
    they lie (`Db.ownEnc`) and entered through `Arr.of`, which decides `Enc.WF`; a float column's words checked to be
    canonical (`nonCanonical`), the first row that is not refused. The header's attribute is a promise nothing here
    re-checks, so it is not taken over. -/
def readArr (t : QAtomicType) (path : String) : IO ((n : USize) × Arr t n) := do
  if t matches .sym then
    throw (IO.userError s!"{path}: a symbol column, which waits for the own-format sym writer (D.9 step 6)")
  if t matches .general then throw (IO.userError s!"{path}: a general column, which the own format does not hold")
  let f ← Db.ownMap path
  unless f.code == t.code.toUInt8 do
    throw (IO.userError s!"{path}: atom type code {f.code}, the column is {repr t} (code {t.code})")
  unless f.domain.isEmpty do
    throw (IO.userError s!"{path}: an enumeration over `{f.domain}`, which waits for the own-format sym writer \
      (D.9 step 6)")
  let some e := Db.ownEnc f.kind f.parts
    | throw (IO.userError s!"{path}: constructor kind {f.kind}, which `Db.ownEnc` does not rebuild")
  let x ← IO.ofExcept (Arr.of t f.count (.vector t f.count e none) path)
  if t matches .f32 | .f64 then
    if let some (b, i) := x.toList.zipIdx.findSome? fun (v, i) => (nonCanonical t v).map (·, i) then
      throw (IO.userError s!"{path}: row {i} holds the {repr t} bit pattern 0x{String.mk (Nat.toDigits 16 b)}, \
        which is not canonical (a NaN or -0)")
  return ⟨f.count, x⟩

/-- `y`, read from `fy`, as a column of the side whose count `n` was read from `fx`: the two counts are equal. -/
def same {F : USize → Type} (fx : String) (n : USize) (fy : String) (y : (m : USize) × F m) : IO (F n) :=
  if h : y.1 = n then pure (h ▸ y.2)
  else throw (IO.userError s!"{fy} has {y.1} rows and {fx} has {n}: the columns of one side have one count")

/-- The inverse of `cols`: the side of object `A` mapped from the files `cols` names under the prefix `p` in `dir`,
    with its count and the file the count was read from. The columns of one side have its count; a list's payload
    and a sum's two payloads have their own. The paths are `cols`'s (`TestTable` round-trips each form). -/
def readVals : (A : Obj) → (dir p : String) → IO (String × (n : USize) × Vals A n)
  | .atom t, dir, p => do let ⟨n, x⟩ ← readArr t (file dir p); return (file dir p, ⟨n, x⟩)
  | .prod a b, dir, p => do
    let (fx, ⟨n, x⟩) ← readVals a dir (p ++ ".1")
    let (fy, y) ← readVals b dir (p ++ ".2")
    return (fx, ⟨n, x, ← same fx n fy y⟩)
  | .arr b, dir, p => do
    let ⟨n, lo⟩ ← readArr .i64 (file dir (p ++ ".lo"))
    let hi ← same (file dir (p ++ ".lo")) n (file dir (p ++ ".hi")) (← readArr .i64 (file dir (p ++ ".hi")))
    let (_, ⟨m, e⟩) ← readVals b dir (p ++ ".e")
    return (file dir (p ++ ".lo"), ⟨n, m, lo, hi, e⟩)
  | .sum a b, dir, p => do
    let ⟨n, tag⟩ ← readArr .u1 (file dir (p ++ ".tag"))
    let idx ← same (file dir (p ++ ".tag")) n (file dir (p ++ ".idx")) (← readArr .i64 (file dir (p ++ ".idx")))
    let (_, ⟨l, x⟩) ← readVals a dir (p ++ ".l")
    let (_, ⟨r, y⟩) ← readVals b dir (p ++ ".r")
    return (file dir (p ++ ".tag"), ⟨n, l, r, tag, idx, x, y⟩)

/-- The columns of `R`, a schema reversed (`Schema.objR`'s order), from `x`: each column's files under its name. -/
def writeCols {n : USize} (dir : String) : (R : Schema) → Vals (Schema.objR .long .prod R) n → IO Unit
  | [], _ => pure ()
  | [f], x => writeVals (A := f.2) dir f.1 x
  | f :: g :: R, x => do writeCols dir (g :: R) x.1; writeVals (A := f.2) dir f.1 x.2

/-- The columns of `R`, a schema reversed, read from their files under their names, with their one count and the file
    it was read from. -/
def readCols (dir : String) : (R : Schema) → IO (String × (n : USize) × Vals (Schema.objR .long .prod R) n)
  | [] => throw (IO.userError s!"{dir}: {Schema.noColumn}")
  | [f] => readVals f.2 dir f.1
  | f :: g :: R => do
    let (fx, ⟨n, x⟩) ← readCols dir (g :: R)
    let (fy, y) ← readVals f.2 dir f.1
    return (fx, ⟨n, x, ← same (F := Vals f.2) fx n fy y⟩)

/-- The side of schema `S` in the directory `dir`, one file per column (an atom column) or per atom of it (`cols`),
    named by the column. -/
def write {n : USize} (S : Schema) (dir : String) (x : Vals S.obj n) : IO Unit := do
  IO.ofExcept S.check; IO.FS.createDirAll dir; writeCols dir S.reverse x

/-- The side of schema `S` read from `dir`: the columns `S` names, each at its declared object, all of one count; a
    missing file, another atom type or another count is the error naming the file. -/
def readSide (S : Schema) (dir : String) : IO (String × (n : USize) × Vals S.obj n) := do
  IO.ofExcept S.check; readCols dir S.reverse

/-- The frame of the value side `x`: its key the positions `0 … n-1`, which are on no file. -/
def frame {B : Obj} {n : USize} (x : Vals B n) : Except String (Tab .long B) := (Arr.pos n).map fun P => ⟨n, P, x⟩

/-- The positional table of schema `S` in `dir`: its rows' key the positions. -/
def read (S : Schema) (dir : String) : IO (Tab .long S.obj) := do
  let (_, ⟨_, x⟩) ← readSide S dir; IO.ofExcept (frame x)

/-- A keyed table, q's dictionary from a key table to a value table: the key side's columns in `dir/key`, the value
    side's in `dir/val`, row `i` of each the pair `i` of `t`. -/
def writeKeyed (K S : Schema) (dir : String) (t : Tab K.obj S.obj) : IO Unit := do
  write K (file dir "key") t.key; write S (file dir "val") t.val

/-- The keyed table of key schema `K` and value schema `S` in `dir`: `dir/key` and `dir/val`, of one count. -/
def readKeyed (K S : Schema) (dir : String) : IO (Tab K.obj S.obj) := do
  let (fk, ⟨n, k⟩) ← readSide K (file dir "key")
  let (fv, v) ← readSide S (file dir "val")
  return ⟨n, k, ← same fk n fv v⟩

/-- **The renumbering of a positional write, as a relation**: reading back `write S dir t.val` gives `frame t.val`
    (per column the round trip `ownParse_ownImage`, `ownEnc_ownParts`; over files only `#guard`ed), and that frame is
    `ι ≫ t` for `ι = {(j, t.key.row j)}`, new position ↦ old key, when no two rows of `t` share a key. -/
theorem frame_holds {K B : Obj} {t : Tab K B} {r : Tab .long B} (h : frame t.val = .ok r)
    (hk : ∀ j j', t.key.row j = t.key.row j' → j = j') (i : Int64) (y : B.El) :
    r.Holds i y ↔ ∃ k, (∃ j : Fin t.n.toNat, j.1.toUInt64.toInt64 = i ∧ t.key.row j = k) ∧ t.Holds k y := by
  unfold frame at h
  cases hP : Arr.pos t.n with
  | error e => rw [hP] at h; cases h
  | ok P =>
    rw [hP] at h; cases h
    constructor
    · rintro ⟨j, hj, hy⟩
      exact ⟨_, ⟨j, (Arr.pos_get hP j).symm.trans hj, rfl⟩, j, rfl, hy⟩
    · rintro ⟨k, ⟨j, hj, rfl⟩, j', hj', hy⟩
      obtain rfl := hk _ _ hj'
      exact ⟨j', (Arr.pos_get hP j').trans hj, hy⟩

end Rel.Lang.Table
