import Rel.Run.Lang.Plan
import Rel.Kernel.Db.ObjectFile

/-! # A table directory (PLAN D.9, `doc/dataframe-design.zh.typ` F6)

A directory is a table and a file one column: an own-format file written by `Db.ownWrite` and mapped back by
`Db.ownMap`, its parts taken as they lie, so nothing is decoded, converted or copied. A side's files are the paths
`cols` gives its atom columns under a prefix, the column's name; a positions column has no file (`Db.ownParts`), so a
frame's key `0 … n-1` is not on disk. -/

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

/-- The atom column of type `t` mapped from `path`: the header's type code and domain checked, the parts taken as
    they lie (`Db.ownEnc`) and entered through `Arr.of`, which decides `Enc.WF`. The header's attribute is a promise
    nothing here re-checks, so it is not taken over. -/
def readArr (t : QAtomicType) (path : String) : IO ((n : USize) × Arr t n) := do
  if t matches .f32 | .f64 then throw (IO.userError s!"{path}: a {repr t} column, which a table is not read with: \
    whether a mapped float is checked to be canonical is not decided (PLAN.md, D.9 question 3)")
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
  return ⟨f.count, ← IO.ofExcept (Arr.of t f.count (.vector t f.count e none) path)⟩

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

end Rel.Lang.Table
