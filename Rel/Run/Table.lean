module

public import Rel.Run.Lang.Plan
public import Rel.Run.Lang.Schema
public import Rel.Run.Lang.Elab
public import Rel.Kernel.Db.ObjectFile
public import Rel.Kernel.Db.Csv
public import Rel.Kernel.Cast
public import Rel.Run.Canon
public import Rel.Run.Comp
public import Rel.Run.Lang.Lazy
public import Rel.Run.List
public import Rel.Run.Asc

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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
reading the key column. A CSV file is the same two forms in one file, key columns then value columns (IO design D),
read straight into encoded columns (`Db.csvRead`) and written straight from them (`Db.csvWrite`). This is the code `n.io` calls (lib `RelRun`); the laws about it
are in `Rel.Lang.Table`. -/

namespace Rel.Lang.Table

open Rel Rel.Lang.Plan

/-- The file of the column `q` in the table directory `dir`. -/
def file (dir q : String) : String := (System.FilePath.mk dir / q).toString

/-- The one column writer of a side: each atom column of `x` with its payloads cut to the cells' reach (`ValsB.pack 0`,
    the form that depends on the cells alone) (`cols` under the prefix `p`) to `file dir <path>`; a positions column has
    no file. -/
def writeVals {A : Obj} {n : USize} (dir p : String) (x : Vals A n) : IO Unit := do
  for (q, c) in cols A (← IO.ofExcept (ValsB.pack 0 x)) p do
    if let some f ← IO.ofExcept (ownFile q c) then
      Db.ownWrite (file dir q) f.code f.kind f.count f.parts

/-- The bit pattern of a word of type `t` that is not in the canonical form `Obj.key` and the kernels assume (typed
    base design, R7 and decision D: a NaN has no row, `-0` is `+0`), `none` for a canonical word: the stored word
    (`QAtomicType.word`) where `QAtomicType.nonCanonical`, the one predicate, holds of it. -/
def nonCanonical (t : QAtomicType) (b : El t) : Option Nat :=
  if t.nonCanonical (t.word b) then some (t.word b).toNat else none

/-- The atom column of type `t` mapped from `path`: the header's type code and domain checked, the parts taken as
    they lie (`Db.ownEnc`) and entered through `Arr.of`, which decides `Enc.WF`; a float column's words checked to be
    canonical (`nonCanonical`), the first row that is not refused. The header's attribute is a promise nothing here
    re-checks, so it is not taken over. -/
def readOpt (t : QAtomicType) (path : String) : IO ((n : USize) × Opt t n) := do
  if t matches .general then throw (IO.userError s!"{path}: a general column, which the own format does not hold")
  let f ← Db.ownMap path
  unless f.code == t.code.toUInt8 do
    throw (IO.userError s!"{path}: atom type code {f.code}, the column is {repr t} (code {t.code})")
  let some e := Db.ownEnc f.kind f.parts
    | throw (IO.userError s!"{path}: constructor kind {f.kind}, which `Db.ownEnc` does not rebuild")
  let some ⟨h⟩ := Ext.Enc.wf? t f.count e
    | throw (IO.userError s!"{path}: a payload that is not {f.count} well-formed elements of {repr t}")
  return ⟨f.count, Opt.mk e h⟩

/-- `readOpt` of a column that holds no null (an atom side's), its floats canonical. -/
def readArr (t : QAtomicType) (path : String) : IO ((n : USize) × Arr t n) := do
  let ⟨n, o⟩ ← readOpt t path
  let x ← if hN : Kernel.hasNul o.enc = false then pure (Arr.mk o.enc o.wf hN)
    else throw (IO.userError s!"{path}: a column holding a null, and its type {repr t} has none")
  if t matches .f32 | .f64 then
    for h : i in [0:n.toNat] do
      if let some b := nonCanonical t (x.get ⟨i, h.upper⟩) then
        throw (IO.userError s!"{path}: row {i} holds the {repr t} bit pattern 0x{String.mk (Nat.toDigits 16 b)}, \
          which is not canonical (a NaN or -0)")
  return ⟨n, x⟩

/-- `y`, read from `fy`, as a column of the side whose count `n` was read from `fx`: the two counts are equal. -/
def same {F : USize → Type} (fx : String) (n : USize) (fy : String) (y : (m : USize) × F m) : IO (F n) :=
  if h : y.1 = n then pure (h ▸ y.2)
  else throw (IO.userError s!"{fy} has {y.1} rows and {fx} has {n}: the columns of one side have one count")

/-- The first of the `n` cells `[lo, hi)` of columns at ownership `o` that is no slice of a payload of `m` rows: `cellBad`
    where every row is owned; where a row may be the in-band null (a summand's), the null row reads as the cell `[0, 0)`. -/
def cellBadB {o : Bool} {n : USize} (m : USize) (lo hi : ColB o .i64 n) : Option (Fin n.toNat) :=
  match o, lo, hi with
  | false, lo, hi => cellBad m lo hi
  | true, lo, hi => (List.finRange n.toNat).find? fun i =>
      let l := (Opt.get lo i).getD 0; let h := (Opt.get hi i).getD 0
      !decide (0 ≤ l.toInt ∧ l.toInt ≤ h.toInt ∧ h.toInt ≤ (m.toNat : Int))

/-- The bound of row `i` of a cell column at ownership `o`, a null row's `0` (as `cellBadB` reads it). -/
def ColB.bound : {o : Bool} → {n : USize} → ColB o .i64 n → Fin n.toNat → Int64
  | false, _, x, i => x.get i
  | true, _, x, i => (Opt.get x i).getD 0

/-- The atom column of type `t` at ownership `o` from `path`: `readArr` where every row is owned, `readOpt` where a row
    may be the in-band null. -/
def readCol : (o : Bool) → (t : QAtomicType) → (path : String) → IO ((n : USize) × ColB o t n)
  | false, t, path => readArr t path
  | true, t, path => readOpt t path

/-- The summand leaf `x` (named by `path`) holds `Opt.filler t` on every row `own` does not own: the null of its block
    (`Column.foRNul`, read per row off the flagged residual, never decoded); a general leaf's filler, its `default`, is
    in no file. A summand's
    unowned rows are `Opt.fill`'s, so two unowned rows read alike (`ColB.OwnedOn`). -/
def leafFill {t : QAtomicType} {n : USize} (path : String) (own : Array Bool) (x : Opt t n) : IO Unit := do
  let starts := x.enc.starts
  for h : i in [0:n.toNat] do
    unless own.getD i true do
      let bad : Option String := match x.enc with
        -- the one offending element is read through `Opt.get`, never the whole column decoded for a message
        | .foR md pk => if Column.foRNul md pk starts i then none
            else some (match Opt.get x ⟨i, h.2.1⟩ with
              | some y => s!"the {repr t} word {QAtomicType.word t y}"
              | none => "a null")
        -- `Opt.filler` of a general leaf is its `default`, which no own file holds (`readOpt` refuses the column), so a
        -- `.gen` payload reaching here is no read
        | .gen _ => some "a general payload, which the own format does not hold"
        | .pos => some s!"the position {i}"
      if let some v := bad then
        throw (IO.userError s!"{path}: row {i} is a row the other summand owns and holds {v}, not null: a summand of a \
          dense sum is `Opt.fill` where its tag names the other summand")

/-- `leafFill` of the atom column `x` at ownership `o`: an `Arr` (`false`) has no unowned row. -/
def colFill : {o : Bool} → {t : QAtomicType} → {n : USize} → String → Array Bool → ColB o t n → IO Unit
  | false, _, _, _, _, _ => pure ()
  | true, _, _, path, own, x => leafFill path own x

/-- Every summand of the dense sum (or of one inside a summand) in `x`, over the rows `own` owns, holds the filler off
    the rows it owns (`leafFill`; `ValsB.WFOn`'s `OwnedOn` clauses), the tag `false` off `own`, and a summand owns the
    rows of `own` its tag names. `p` is the side's prefix, the paths as in `readValsB`. -/
def fillBad (dir : String) : {o : Bool} → {A : Obj} → {n : USize} → String → Array Bool → ValsB o A n → IO Unit
  | _, .atom _, _, p, own, x => colFill (file dir p) own x
  | _, .prod _ _, _, p, own, x => do fillBad dir (p ++ ".1") own x.1; fillBad dir (p ++ ".2") own x.2
  | _, .arr _, _, p, own, ⟨_, lo, hi, _⟩ => do
    colFill (file dir (p ++ ".lo")) own lo; colFill (file dir (p ++ ".hi")) own hi
  | _, .one, _, _, _, _ => pure ()
  | _, .sum _ _, n, p, own, s => match ValsB.view s with
    | .opt _ x => leafFill (file dir p) own x
    | .gen _ tag x y => do
      let tags := Arr.rowsImpl tag
      for i in [0:n.toNat] do
        if !own.getD i true && tags.getD i false then
          throw (IO.userError s!"{file dir (p ++ ".tag")}: row {i} is not owned by the side and its tag is `true`, \
            not `false`: a dense sum's tag is `false` where its side owns no row")
      let owns (v : Bool) := (Array.range n.toNat).map fun i => own.getD i true && tags.getD i false == v
      fillBad dir (p ++ ".l") (owns false) x; fillBad dir (p ++ ".r") (owns true) y

/-- The inverse of `cols`: the side of object `A` at ownership `o` mapped from the files `cols` names under the prefix `p`
    in `dir`, with its count and the file the count was read from. The columns of one side have its count; a list's
    payload has its own (every row owned). A general sum is a tag and two summands of the sum's count, read at `o = true`
    (a summand's other rows hold the in-band null); a band sum is one `Opt` column. The paths are `cols`'s
    (`TestTable` round-trips each form). -/
def readValsB : (o : Bool) → (A : Obj) → (dir p : String) → IO (String × (n : USize) × ValsB o A n)
  | o, .atom t, dir, p => do let ⟨n, x⟩ ← readCol o t (file dir p); return (file dir p, ⟨n, x⟩)
  | o, .prod a b, dir, p => do
    let (fx, ⟨n, x⟩) ← readValsB o a dir (p ++ ".1")
    let (fy, y) ← readValsB o b dir (p ++ ".2")
    return (fx, ⟨n, x, ← same (F := ValsB o b) fx n fy y⟩)
  | o, .arr b, dir, p => do
    let ⟨n, lo⟩ ← readCol o .i64 (file dir (p ++ ".lo"))
    let hi ← same (F := ColB o .i64) (file dir (p ++ ".lo")) n (file dir (p ++ ".hi")) (← readCol o .i64 (file dir (p ++ ".hi")))
    let (_, ⟨m, e⟩) ← readValsB false b dir (p ++ ".e")
    -- the one place a cell's bounds are checked (PLAN 8.5): past here every cell is a slice of its payload
    if let some i := cellBadB m lo hi then
      throw (IO.userError s!"{file dir (p ++ ".lo")}: row {i} is the cell [{ColB.bound lo i}, {ColB.bound hi i}), not a slice of the {m} rows of \
        {file dir (p ++ ".e")}: a cell [lo, hi) needs 0 ≤ lo ≤ hi ≤ {m}")
    return (file dir (p ++ ".lo"), ⟨n, m, lo, hi, e⟩)
  -- the summands' filler is checked once, from the outermost sum (`fillBad` descends into the nested ones)
  | o, .sum a b, dir, p => match h : Obj.band a b with
    | some t => do let ⟨n, x⟩ ← readOpt t (file dir p); return (file dir p, ⟨n, ValsB.ofOpt h x⟩)
    | none => do
    let ft := file dir (p ++ ".tag")
    let ⟨n, tag⟩ ← readArr .u1 ft
    let (_, x) ← readValsB true a dir (p ++ ".l")
    let (_, y) ← readValsB true b dir (p ++ ".r")
    let s : ValsB o (.sum a b) n := ValsB.ofGen h tag (← same (F := ValsB true a) ft n (file dir (p ++ ".l")) x)
      (← same (F := ValsB true b) ft n (file dir (p ++ ".r")) y)
    unless o do fillBad dir p (Array.replicate n.toNat true) s
    return (ft, ⟨n, s⟩)
  -- a side of `1`: its file holds its count and no part (`Plan.oneKind`)
  | _, .one, dir, p => do
    let f ← Db.ownMap (file dir p)
    unless f.kind == oneKind && f.parts.isEmpty do
      throw (IO.userError s!"{file dir p}: constructor kind {f.kind} with {f.parts.size} parts, a side of `1` is kind {oneKind} with none")
    return (file dir p, ⟨f.count, ()⟩)

/-- `readValsB` of a side every row of which is owned: the sides of a table. -/
abbrev readVals (A : Obj) (dir p : String) := readValsB false A dir p

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

/-- The texts `ts` as a column of `[C]` (`writeDict`'s form), each a cell of its UTF-8 bytes. -/
def textCol (ts : List String) : (n : USize) × Vals (.arr (.atom .char)) n :=
  let bs := ts.toArray.map String.toUTF8
  -- the cells' bounds: `ends[i]` the bytes before cell `i`
  let ends : Array Nat := bs.foldl (fun e b => e.push (e.back?.getD 0 + b.size)) #[0]
  let cs := bs.foldl (· ++ ·) ByteArray.empty
  ⟨bs.size.toUSize, cs.size.toUSize, Arr.ofFn .i64 _ (fun i => (ends[i.val]?.getD 0).toUInt64),
    Arr.ofFn .i64 _ (fun i => (ends[i.val + 1]?.getD 0).toUInt64), Arr.ofFn .char _ (fun i => (cs[i.val]?.getD 0).toUInt64)⟩

/-- The name of a side's column order in its directory, q's `.d`: the schema's names as a text column (`textCol`). -/
def dName : String := ".d"

/-- The side of schema `S` in the directory `dir`, one file per column (an atom column) or per atom of it (`cols`),
    named by the column; the names in order as `.d` (`dName`), from which `readSchema` reads `S` back. -/
def write {n : USize} (S : Schema) (dir : String) (x : Vals S.obj n) : IO Unit := do
  IO.ofExcept S.check; IO.FS.createDirAll dir
  writeVals (A := .arr (.atom .char)) dir dName (textCol S.names).2; writeCols dir S.reverse x

/-- `objOf?` with `k` more steps: each step is a part, and a part that is found is a file of `dir`, so the entries of
    `dir` bound the depth and the recursion is on `k`, never on the growing name. -/
def objOfK (dir : String) : Nat → String → IO (Option Obj)
  | 0, _ => pure none
  | k + 1, p => do
    -- a directory is no column file, whatever name (`""`) reaches it
    let has (q : String) : IO Bool := do return (← System.FilePath.pathExists (file dir q)) && !(← System.FilePath.isDir (file dir q))
    let need (q : String) : IO Obj := do
      let some a ← objOfK dir k q | throw (IO.userError s!"{file dir q}: no column file, a part of the side {file dir p}")
      pure a
    if ← has p then
      let f ← Db.ownMap (file dir p)
      if f.kind == oneKind then return some .one
      let some (_, t) := atomNames.find? (·.2.code.toUInt8 == f.code)
        | throw (IO.userError s!"{file dir p}: atom type code {f.code}, the code of no atom")
      return some (.atom t)
    if ← has (p ++ ".lo") then return some (.arr (← need (p ++ ".e")))
    if ← has (p ++ ".tag") then return some (.sum (← need (p ++ ".l")) (← need (p ++ ".r")))
    match ← objOfK dir k (p ++ ".1") with
    | some a => return some (.prod a (← need (p ++ ".2")))
    | none => return none

/-- The object of the side stored under `p` in `dir`, read back from its files, the converse of `cols`'s paths: a file
    at `p` is an atom (its header's type code) or a side of `1` (`oneKind`); `p.lo` a list, `p.tag` a sum, `p.1` a
    pair; `none` when no file of `dir` is stored under `p`, and always ends: the depth is bounded by the entries of
    `dir` (`objOfK`). -/
def objOf? (dir p : String) : IO (Option Obj) := do
  unless ← System.FilePath.isDir dir do return none
  objOfK dir ((← System.FilePath.readDir dir).size + 1) p


/-- The frame of the value side `x`: its key the positions `0 … n-1`, which are on no file. -/
def frame {B : Obj} {n : USize} (x : Vals B n) : Except String (Tab .long B) := (Arr.pos n).map fun P => ⟨n, P, x⟩

/-- A database's one symbol dictionary `D : ℕ ⟶ [C]` (design §0.2, §4.3), q's sym file: distinct texts, row `i` the
    text of id `i`, append-only, so a new text takes the next id and an id never changes. Being distinct, id equality
    is text equality; text order is `rank`'s. -/
abbrev Dict := Tab .long (.arr (.atom .char))

/-- The dictionary of no text. -/
def Dict.empty : Except String Dict :=
  frame (⟨0, Arr.ofFn .i64 0 (·.elim0), Arr.ofFn .i64 0 (·.elim0), Arr.ofFn .char 0 (·.elim0)⟩ :
    Vals (.arr (.atom .char)) 0)


/-- intern the texts `x` into `D` (design §0.2), no kernel of its own: `R : ℕ ⟶ [C]` the texts by row, the new texts
    `N = ran R − ran D`, each to its first row `F = Λ((R ≫ N)°) ≫ uncons ≫ π₁ : [C] ⟶ ℕ`; `D'` is `D` then the texts of
    `F°` (first-row order), renumbered; each row's id `R ≫ D'°`. `D`'s rows are kept, so no stored id changes. -/
def intern {n : USize} (what : String) (D : Dict) (x : Vals (.arr (.atom .char)) n) :
    Except String (Dict × Arr .sym n) := do
  let R ← frame x
  let N ← (← R.ran).diff (← D.ran)
  let L ← Tab.lamOf N.key (← (← R.comp N).conv)
  let F ← L.comp (← Tab.uncons L.val)
  let D' ← frame (← D.concat (← (⟨F.n, F.key, F.val.1⟩ : Tab (.arr (.atom .char)) .long).conv)).val
  let I ← R.comp (← D'.conv)
  unless I.n = n do .error s!"{what}: {I.n} ids for {n} texts"
  pure (D', ← Arr.of .sym n I.val.1 what)

/-- `rank = iasc(D)° : ℕ ⟶ ℕ`, an id to its text's position in text order: `iasc(D) = asc(ran D) ≫ D°`, so
    `rank = D ≫ asc(ran D)°`. It reads `D` alone: when `D` grows only `rank` is recomputed, never a data column. -/
def rank (D : Dict) : Except String (Tab .long .long) := do D.comp (← (← Tab.asc (← D.ran)).conv)

/-- The symbol relation `I : A ⟶ sym` as its ids `A ⟶ ℕ`: a `sym` column is its ids (`Enc.WF`), so the payload is
    taken as it lies and its well-formedness carried over by proof, never re-decided (`Arr.of`) or read. -/
def symIds {A : Obj} (I : Tab A (.atom .sym)) : Tab A .long :=
  ⟨I.n, I.key, Arr.mk (Arr.enc (t := .sym) I.val) (by
    have h := I.val.wf; generalize Arr.enc (t := .sym) I.val = e at h ⊢; cases e <;> simp_all [Ext.Enc.WF, QAtomicType.width])
    I.val.plain⟩

/-- The dictionary `D : ℕ ⟶ [C]` as the relation `sym ⟶ [C]`: row `i` is the text of id `i` (`Dict`), so the ids `0 … n-1`
    are the key as a `sym` column (a frame's `pos` key is no `sym` payload). The one term of the language for the
    program's dictionary (`dictionary D : S ⟶ [C]`), so `unenum(I) = I ≫ D` composes language terms. -/
def dictRel (D : Dict) : Tab (.atom .sym) (.arr (.atom .char)) := ⟨D.n, Arr.ofFn .sym D.n (·.val.toUInt64), D.val⟩

/-- q's unenumerate: `unenum(I) = I ≫ D`, the symbol relation `I : A ⟶ sym` with each id replaced by its text in its
    library's dictionary `D`, a composition and no kernel of its own. A symbol column meets only columns of its own
    library (`progLib`); its texts meet any text and intern into any library. An id past `D` has no text, so the
    answer is short and refused. -/
def unenum {A V : Obj} (what : String) (D : Tab .long V) (I : Tab A (.atom .sym)) : Except String (Tab A V) := do
  let T ← (symIds I).comp D
  if T.n = I.n then pure T
  else .error s!"{what}: {I.n.toNat - T.n.toNat} of {I.n} ids are past the dictionary of {D.n} texts"

/-- `K ≫ rank : sym ⟶ ℕ`, each symbol of the column `K` to the position of its text in text order (owner decision J),
    the one place order enters a symbol. An id past the dictionary has no rank, so the answer is short and refused;
    ranks are `Int64`, so a dictionary of `2^63` texts is refused. -/
def symRanked (what : String) (D : Dict) {n : USize} (K : Vals (.atom .sym) n) :
    Except String (Tab (.atom .sym) .long) := do
  let P ← (symIds (⟨n, K, K⟩ : Tab (.atom .sym) (.atom .sym))).comp (← rank D)
  unless P.n = n do .error s!"{what}: {n.toNat - P.n.toNat} of {n} ids are past the dictionary of {D.n} texts"
  unless D.n.toNat < 2 ^ 63 do .error s!"{what}: the dictionary of {D.n} texts has ranks past Int64"
  pure P

/-- **`asc(P)` on `sym` by text order**, `asc(R° ≫ R) ≫ R°` with `R = K ≫ rank` for the set `K = dom P` (design
    §4.3): the ranks of the set numbered by `asc` at `i64`, each read back as its symbol, so `j ↦ a` with `a` the `j`-th
    smallest text. -/
def symAsc (D : Dict) (P : Tab (.atom .sym) (.atom .sym)) : Except String (Tab .long (.atom .sym)) := do
  let R ← symRanked "asc" D (← P.dom).key
  let C ← R.conv
  (← Tab.asc (← C.comp R)).comp C

/-- The texts of the ids `y` through the dictionary `D`: `unenum` of the frame of `y`, row `i` its id. -/
def decode {n : USize} (what : String) (D : Dict) (y : Arr .sym n) : Except String (Vals (.arr (.atom .char)) n) := do
  let T ← unenum what D (← frame y)
  if h : T.n = n then pure (h ▸ T.val) else .error s!"{what}: internal: `unenum` answered {T.n} rows for {n} ids"

/-- The schema of the side in `dir`, for a program that declares none (`schema S from "dir"`, `dataframe-design` F1):
    the names from its `.d`, each column's object from its files (`objOf?`). -/
def readSchema (dir : String) : IO Schema := do
  let (fd, ⟨_, x⟩) ← readVals (.arr (.atom .char)) dir dName
  let S ← (← IO.ofExcept (frame x)).toArray.foldrM (init := []) fun (_, b) S => do
    let some n := String.fromUTF8? ⟨(b.map fun c => c.toNat.toUInt8).toArray⟩
      | throw (IO.userError s!"{fd}: a column name that is no UTF-8 text")
    let some o ← objOf? dir n | throw (IO.userError s!"{dir}: no file of the column '{n}' that {fd} names")
    pure ((n, o) :: S)
  IO.ofExcept ((Schema.check S).mapError (s!"{fd}: " ++ ·)); pure S

/-- The object `objOf?` reads back from the files of `A`: an in-band sum (`Obj.band`) is its one nullable column, a file of
    the atom `t` (`cols`), so it is stored as `t`; the rest as it is. -/
def stored : Obj → Obj
  | .atom t => .atom t
  | .prod a b => .prod (stored a) (stored b)
  | .arr b => .arr (stored b)
  | .sum a b => match Obj.band a b with
    | some t => .atom t
    | none => .sum (stored a) (stored b)
  | .one => .one

/-- The declared schema `S` against the `.d` of `dir` (`readSchema`): a column declared and not on disk, on disk and
    not declared, or at another object is the error naming the column and both objects. The columns are compared by
    name, never by position, as `readCols` finds each by its name. A directory with no `.d` (data written before
    `Table.write` wrote one) is not checked and reads as it always did. -/
def checkDisk (S : Schema) (dir : String) : IO Unit := do
  unless (← objOf? dir dName).isSome do return
  let fd := file dir dName
  let D ← readSchema dir
  for (c, o) in S do
    match D.lookup c with
    | none => throw (IO.userError s!"{fd}: column {c} is not on disk, declared {(oexpOf o).1.show}")
    | some d => unless d == stored o do throw (IO.userError s!"{fd}: column {c} is {(oexpOf d).1.show}, declared {(oexpOf o).1.show}")
  for (c, d) in D do
    unless S.any (·.1 == c) do throw (IO.userError s!"{fd}: column {c} is {(oexpOf d).1.show} on disk, not declared")

/-- The side of schema `S` read from `dir`: the columns `S` names, each at its declared object, all of one count; a
    missing file, another atom type or another count is the error naming the file, and a `.d` that differs from `S`
    the error `checkDisk` names. Every reader of a declared table (`read`, `readKeyed`) comes through here. -/
def readSide (S : Schema) (dir : String) : IO (String × (n : USize) × Vals S.obj n) := do
  IO.ofExcept S.check; checkDisk S dir; readCols dir S.reverse

/-- The positional table of schema `S` in `dir`: its rows' key the positions. -/
def read (S : Schema) (dir : String) : IO (Tab .long S.obj) := do
  let (_, ⟨_, x⟩) ← readSide S dir; IO.ofExcept (frame x)

/-- A keyed table, q's dictionary from a key table to a value table: the key side's columns in `dir/key`, the value
    side's in `dir/val`, row `i` of each the pair `i` of `t`. -/
def writeKeyed (K S : Schema) (dir : String) (t : Tab K.obj S.obj) : IO Unit := do
  write K (file dir "key") t.key; write S (file dir "val") t.val

/-- A keyed table's rows sorted by key with equal rows merged (`Tab.canon`), as every kernel takes a table: a file's
    row order and duplicates are not kept, a relation being a set; its error after `what`. -/
def canon {K B : Obj} (what : String) (t : Tab K B) : Except String (Tab K B) := t.canon.mapError (s!"{what}: " ++ ·)

/-- The keyed table of key schema `K` and value schema `S` in `dir`: `dir/key` and `dir/val`, of one count. -/
def readKeyed (K S : Schema) (dir : String) : IO (Tab K.obj S.obj) := do
  let (fk, ⟨n, k⟩) ← readSide K (file dir "key")
  let (fv, v) ← readSide S (file dir "val")
  IO.ofExcept (canon dir ⟨n, k, ← same fk n fv v⟩)

/-- The database directory `db`'s dictionary: the ordinary text column `sym` (`writeVals` at `[C]`) and its `rank`
    the long column `sym.rank`; the own format has no kind of its own for either. -/
def writeDict (db : String) (D : Dict) : IO Unit := do
  writeVals (A := .arr (.atom .char)) db "sym" D.val
  writeVals (A := .long) db "sym.rank" (← IO.ofExcept (rank D)).val

/-- The converse of `writeDict`: the texts refused unless distinct (`ran` keeps every row), the rank file unless it is
    `rank` of them. -/
def readDict (db : String) : IO (Dict × Tab .long .long) := do
  let (fd, ⟨d, x⟩) ← readVals (.arr (.atom .char)) db "sym"
  let D ← IO.ofExcept (frame x)
  let u ← IO.ofExcept D.ran
  unless u.n = d do throw (IO.userError s!"{fd}: {d.toNat - u.n.toNat} of {d} texts repeat one before them")
  let K ← IO.ofExcept (rank D)
  let (fr, ⟨m, r⟩) ← readVals .long db "sym.rank"
  -- both keyed by the ids `0 …`, so equal iff of one count and `frame r ∩ K` keeps all of `K`, met encoded
  unless m == K.n && (← IO.ofExcept ((← IO.ofExcept (frame r)).inter K)).n == K.n do
    throw (IO.userError s!"{fr}: not the rank of the dictionary {fd}")
  return (D, K)

/-- A symbol column in `dir` under `p`: its ids, the column `p`; the texts are the database's one dictionary
    (`writeDict`). -/
def writeSym {n : USize} (dir p : String) (y : Arr .sym n) : IO Unit := writeVals (A := .atom .sym) dir p y

/-- The symbol columns of the side `x` (`cols` under `p`), each refused unless every id has a text in `D`: its ids
    `unenum` through `dom D` (the ids alone, no text gathered), the column named as its file in `dir`. -/
def checkSyms {A : Obj} {n : USize} (dir p : String) (D : Dict) (x : Vals A n) : Except String Unit := do
  let E ← D.dom
  for (q, c) in cols A x p do
    if let .inr ⟨.sym, k, y⟩ := c then
      let _ ← unenum (file dir q) E (← frame (B := .atom .sym) (← Arr.of .sym k y.enc (file dir q)))

/-- The converse of `writeSym`: the ids at `p`, refused unless each has a text in `D` (`checkSyms`). -/
def readSym (D : Dict) (dir p : String) : IO ((n : USize) × Arr .sym n) := do
  let (_, ⟨n, y⟩) ← readVals (.atom .sym) dir p
  IO.ofExcept (checkSyms (A := .atom .sym) dir p D y)
  return ⟨n, y⟩

/-- Whether `A` has a symbol atom: a side of it then holds ids into a library's dictionary. -/
def symIn : Obj → Bool
  | .atom t => decide (t = .sym)
  | .prod a b | .sum a b => symIn a || symIn b
  | .arr a => symIn a
  | .one => false

/-- The library of the table directory `dir` (§0.2, q's database root): the directory holding it, where the one
    dictionary of every table in it lies (`writeDict`, the files `sym` and `sym.rank`). Where a table lies is the one
    record of its library. -/
def lib (dir : String) : String :=
  match ((System.FilePath.mk dir).components.reverse.dropWhile (·.isEmpty)).drop 1 with
  | [] => "."
  | [""] => "/"
  | cs =>(System.mkFilePath cs.reverse).toString

/-- The dictionary of the library `L` (`readDict`), empty in a library with none yet; a dictionary with some of its
    files missing is refused, naming them. -/
def libDict (L : String) : IO Dict := do
  let E ← IO.ofExcept Dict.empty
  let ps := (cols (.arr (.atom .char)) E.val "sym").filterMap fun | (q, .inr _) => some (file L q) | _ => none
  let gone ← ps.filterM fun f => return !(← System.FilePath.pathExists f)
  if gone.length == ps.length then return E
  unless gone.isEmpty do throw (IO.userError s!"{L}: the library's dictionary lacks the files {gone}")
  return (← readDict L).1

/-- `D` as the dictionary of the library `L`, append-only (§0.2, q's sym file): `L`'s dictionary must be the first
    rows of `D`, so no id stored in `L` changes and `D`'s texts past them are appended; else the first id where the two
    differ is named. -/
def writeLib (L : String) (D : Dict) : IO Unit := do
  let old ← libDict L
  -- the first rows of `D` iff `old ⊑ D` (both keyed by the ids `0 …`), met on the encoded tables
  let X ← IO.ofExcept (old.diff D)
  if h : 0 < X.n.toNat then
    throw (IO.userError s!"{L}: the library's dictionary of {old.n} texts and the program's of {D.n} \
      differ at id {X.key.get ⟨0, h⟩}; a dictionary is append-only, so these ids are not of this library")
  unless old.n == D.n do IO.FS.createDirAll L; writeDict L D

/-- An own table a program reads, `r` reading it from `dir`: its symbol columns' ids taken as they lie, the program's
    dictionary `D` being its library's (`progLib`), and refused unless each has a text in `D` (`checkSyms`). -/
def readOwn {A B : Obj} (D : Dict) (dir : String) (r : IO (Tab A B)) : IO (Tab A B) := do
  let t ← r
  IO.ofExcept (do checkSyms dir "key" D t.key; checkSyms dir "val" D t.val)
  return t

/-- An own table a program writes to `dir` with the schemas `K` and `S`, `w` writing it: when a column is a symbol
    column, the program's dictionary `D` first appended to the library's (`writeLib`), so no stored id is ever without
    its text; the ids then written as they lie. -/
def writeOwn (D : Dict) (K S : Schema) (dir : String) (w : IO Unit) : IO Unit := do
  if (K ++ S).any (symIn ·.2) then writeLib (lib dir) D
  w

/-- The library of a program (§0.2): the one library (`lib`) of every own table it reads or writes with a symbol
    column, `ts` each table's name, directory and schemas; `none` when no own table has one. Two of them in two
    libraries are refused, naming both: their ids are of two dictionaries and the program holds one, so their symbol
    columns cannot meet. -/
def progLib (ts : List (String × String × Schema × Schema)) : Except String (Option String) := do
  let r ← ts.foldlM (init := (none : Option (String × String))) fun acc (x, p, K, S) =>
    if !(K ++ S).any (symIn ·.2) then pure acc else match acc with
      | none => pure (some (x, lib p))
      | some (y, L) => if L == lib p then pure acc else .error s!"the symbol columns of `{y}` are ids in the \
          library {L} and those of `{x}` in the library {lib p}, two dictionaries, so they cannot meet; convert one \
          to its texts with `unenum` (`I ≫ D`)"
  pure (r.map (·.2))

/-- The first part of `es` as an atom column of type `t`, entered through `Arr.of` as `readArr` enters a mapped one;
    its count, and the parts left over. -/
def encArr (path : String) (t : QAtomicType) : List (USize × Enc) →
    Except String ((n : USize) × Arr t n × List (USize × Enc))
  | (k, e) :: es => do pure ⟨k, ← Arr.of t k e s!"{path}: a {repr t} column part of {k} rows", es⟩
  | [] => .error s!"{path}: no column part left for a {repr t} column"

/-- The first part of `es` as a nullable column of type `t`, its blocks checked by `Ext.Enc.wf?` (the whole check: a writer
    takes the block's least key from the atom, `QAtomicType.least`, so a part it refuses is malformed, never decoded
    element by element to find out); its count, and the parts left over. -/
def encOpt (path : String) (t : QAtomicType) : List (USize × Enc) →
    Except String ((n : USize) × Opt t n × List (USize × Enc))
  | (k, e) :: es => match Ext.Enc.wf? t k e with
    | some ⟨h⟩ => pure ⟨k, Opt.mk e h, es⟩
    | none => .error s!"{path}: a {repr t} column part of {k} rows whose blocks are not well-formed (`Ext.Enc.wf?` refuses it)"
  | [] => .error s!"{path}: no column part left for a {repr t} column"

/-- The first part of `es` as an atom column of type `t` at ownership `o`: `encArr` where every row is owned, `encOpt`
    where a row may be the in-band null. -/
def encCol : (o : Bool) → (t : QAtomicType) → (path : String) → List (USize × Enc) →
    Except String ((n : USize) × ColB o t n × List (USize × Enc))
  | false, t, path, es => encArr path t es
  | true, t, path, es => encOpt path t es

/-- A side of object `A` at ownership `o` from its atom columns' encodings `es`, each with its count, in `cols`' order (a
    sum's tag and two summands of the sum's count, a band sum's one nullable column, a list's bounds and payload), the
    converse of `csvEncs`: each entered as `readValsB` enters a mapped one; the side's count, and the parts left over. -/
def encValsB (path : String) : (o : Bool) → (A : Obj) → List (USize × Enc) →
    Except String ((n : USize) × ValsB o A n × List (USize × Enc))
  | o, .atom t, es => encCol o t path es
  | o, .prod a b, es => do
    let ⟨n, x, es⟩ ← encValsB path o a es
    let ⟨m, y, es⟩ ← encValsB path o b es
    if h : m = n then pure ⟨n, (x, h ▸ y), es⟩ else .error s!"{path}: columns of {n} and {m} rows on one side"
  | o, .arr b, es => do
    let ⟨n, lo, es⟩ ← encCol o .i64 path es
    let ⟨m, hi, es⟩ ← encCol o .i64 path es
    let ⟨k, f, es⟩ ← encValsB path false b es
    if h : m = n then pure ⟨n, ⟨k, lo, h ▸ hi, f⟩, es⟩ else .error s!"{path}: list bounds of {n} and {m} rows"
  | _, .sum a b, es => match hb : Obj.band a b, es with
    | some t, es => do let ⟨k, x, es⟩ ← encOpt path t es; pure ⟨k, ValsB.ofOpt hb x, es⟩
    | none, es => do
    let ⟨n, tag, es⟩ ← encArr path .u1 es
    let ⟨l, x, es⟩ ← encValsB path true a es
    let ⟨r, y, es⟩ ← encValsB path true b es
    if h : l = n then
      if h' : r = n then pure ⟨n, ValsB.ofGen hb tag (h ▸ x) (h' ▸ y), es⟩
      else .error s!"{path}: sum tags of {n} and a right summand of {r} rows"
    else .error s!"{path}: sum tags of {n} and a left summand of {l} rows"
  -- a side of `1`: its part (a CSV column of its one element's code, or a sum's empty right side) gives the count
  | _, .one, (n, _) :: es => pure ⟨n, (), es⟩
  | _, .one, [] => .error s!"{path}: no column part left for a side of `1`"

/-- `encValsB` of a side every row of which is owned: the sides of a table. -/
abbrev encVals (path : String) (A : Obj) (es : List (USize × Enc)) := encValsB path false A es

/-- The atom types of `A` when it is a product of atoms (the `S` of a CSV `1+S`), in column order; none for any other object. -/
def atomTypes : Obj → Option (List QAtomicType)
  | .atom t => some [t]
  | .prod a b => return (← atomTypes a) ++ (← atomTypes b)
  | _ => none

/-- The tags of a sum's `n` rows swapped between its two sides (`A+B ≅ B+A`, positions and payloads unchanged): the
    CSV extern lays a nullable field out as `V+1` (tag `1` at a null), the language's nullable is `1+V` (`Obj.opt`). -/
def swapTag : USize × Enc → Except String (USize × Enc)
  | (n, t) => return (n, ← colMap .first n t t .u1 .i64 [] [(.not, 0)])

/-- The CSV shape of each nullable column of a `1+S` (`Obj.opt S`): the one column `opt` where `1+S` is in-band
    (`Obj.band`), else one `null` column per atom of `S`. The one decision every CSV reader and writer reads
    (`Expand.ioCols`, `toCsv`, `ofCsv`), so the header and the parts cannot disagree. -/
def nullShape (S : Obj) : Db.CsvShape := if (Obj.band .one S).isSome then .opt else .null

/-- The parts of a side of object `A`, `ps` in `cols`' order, as its CSV columns' parts (`Db.CsvShape.atoms`), with
    the parts left over. A nullable `1+S` (`Obj.opt`, `Expand.csvLeaves`) is one nullable column per atom of `S`, each
    with its own copy of the sum's tags (`swapTag`), positions and null values; every other part as it lies. -/
def toCsv (path : String) : Obj → List (USize × Enc) → Except String (List (USize × Enc) × List (USize × Enc))
  | .atom _, x :: ps => pure ([x], ps)
  | .prod a b, ps => do let (x, ps) ← toCsv path a ps; let (y, ps) ← toCsv path b ps; pure (x ++ y, ps)
  | .arr (.atom _), lo :: hi :: e :: ps => pure ([lo, hi, e], ps)
  -- the column of a `1` is its one element's name in every row
  | .one, x :: ps => pure ([x], ps)
  -- the in-band `1+V` (`Obj.band`) is its one `Opt` part, the CSV column of shape `opt` as it lies; any other `1+S`
  -- drops its left side's `1` part: a null is an empty field
  | .opt a, ps => match nullShape a, ps with
    | .opt, x :: ps => pure ([x], ps)
    -- the parts are the dense sum's (`cols`: tag, the left `1`, `n`-row summands with a null at the other rows); each atom
    -- becomes the extern's (tag swapped, position, non-null values), `denseVals`' converse: the position is the count
    -- of rows of the row's own side before it, the values are the summand at the `where` of the tag's `1` rows
    | .null, tg :: _ :: ps => do
      let some ts := atomTypes a | .error s!"{path}: a `1+S` whose `S` is no product of atoms has no CSV columns"
      unless ts.length ≤ ps.length do .error s!"{path}: too few parts for a `1+S`"
      let n := tg.1
      let e ← swapTag tg
      let own ← colPrefix .add n tg.2
      let oth ← colPrefix .add n e.2
      let own ← colMap .sub n own tg.2
      let oth ← colMap .sub n oth e.2
      let i ← colMap .add n (← colMap .mul n e.2 oth) (← colMap .mul n tg.2 own)
      let (m, w) ← whereCol n tg.2
      let vs ← (ps.take ts.length).mapM fun (_, y) => do pure (m, ← Kernel.kgather m w n y)
      pure (vs.flatMap fun v => [e, (n, i), v], ps.drop ts.length)
    | .null, _ => .error s!"{path}: too few parts for a `1+S`"
    | _, _ => .error s!"{path}: too few parts for a `1+S`"
  | _, _ => .error s!"{path}: a side whose object is no CSV column set (a list of no atom, a sum of no `1+S`), or too few parts"

/-- `k` groups of three parts from the front of `cs` (one CSV nullable column's tags, positions, values), and the
    parts left. -/
def triples {α : Type} : Nat → List α → Option (List (α × α × α) × List α)
  | 0, cs => some ([], cs)
  | k + 1, t :: i :: v :: cs => (triples k cs).map fun (g, cs) => ((t, i, v) :: g, cs)
  | _ + 1, _ => none

/-- The values `(m, v)` of one CSV nullable atom column (`ofCsv`: the `m` non-null rows only) as the dense summand column of
    `n` rows (`ValsB true`): row `j` holds the value at position `i j` of its side where the extern's tag `e` (`1` at a
    null) is `0`, and the in-band null where it is `1`. One `kgather` at `i + m·e` over `v` followed by as many nulls as
    `e` has: a null row's position is the count of nulls before it, so it lands in the nulls after the `m` values. -/
def denseVals (path : String) (t : QAtomicType) {n : USize} (e : Arr .u1 n) (i : USize × Enc) (m : USize) (v : Enc) :
    Except String (USize × Enc) := do
  unless i.1 = n do .error s!"{path}: positions of {i.1} rows beside tags of {n}"
  let ⟨_, x, _⟩ ← encOpt path t [(m, v)]
  let nn := (← tagCount n true e).toUSize
  let y ← Opt.concat (n := (← catRows m nn)) x (← Opt.nuls t nn)
  let ix ← colMap .add n i.2 (← colMap .first n e.enc e.enc .i64 .i64 [] [(.mul, m.toUInt64)])
  pure (n, (← Opt.gather n ix y).enc)

/-- The converse of `toCsv`: the side `A`'s parts in `cols`' order from its CSV columns' parts `cs`, the header names
    of those columns `ns` in step, with what is left of both. The nullable columns of one `1+S` are null in the same
    rows (the `1` is every field of `S` empty): their tags must agree, else the first row where two differ is named. -/
def ofCsv (path : String) : Obj → List (USize × Enc) → List String →
    Except String (List (USize × Enc) × List (USize × Enc) × List String)
  | .atom _, x :: cs, _ :: ns => pure ([x], cs, ns)
  | .prod a b, cs, ns => do
    let (x, cs, ns) ← ofCsv path a cs ns; let (y, cs, ns) ← ofCsv path b cs ns; pure (x ++ y, cs, ns)
  | .arr (.atom _), lo :: hi :: e :: cs, _ :: ns => pure ([lo, hi, e], cs, ns)
  | .opt a, cs, ns => if nullShape a = .opt then match cs, ns with
      | x :: cs, _ :: ns => pure ([x], cs, ns)
      | _, _ => .error s!"{path}: no column part or header name left for a nullable column"
    else do
    let some ts := atomTypes a | .error s!"{path}: a `1+S` whose `S` is no product of atoms has no CSV columns"
    let some ((t, i, v) :: g, cs) := triples ts.length cs | .error s!"{path}: too few column parts for {ts.length} nullable columns"
    let some c := ns.head? | .error s!"{path}: no header name left for a nullable column"
    let ⟨n, x, _⟩ ← encArr path .u1 [t]
    for ((t', _), c') in g.zip ns.tail do
      let ⟨m, y, _⟩ ← encArr path .u1 [t']
      unless m = n do .error s!"{path}: nullable columns '{c}' of {n} rows and '{c'}' of {m}"
      for j in [0:n.toNat] do
        if hj : j < n.toNat ∧ j < m.toNat then
          let (a, b) := (x.get ⟨j, hj.1⟩, y.get ⟨j, hj.2⟩)
          let s (z : Bool) := if z then "empty (null)" else "not empty"
          unless a == b do
            .error s!"{path}: data row {j + 1}: column '{c}' is {s a} and column '{c'}' is {s b}; the columns of one \
              `1+S` are empty together, and all of them empty is the `1`"
    -- the dense sum's parts (`cols`): the tag, swapped as the extern's is `1` at a null (`V+1`, `swapTag`); the left `1` of
    -- `n` rows, no column; each atom of `S` as `n` rows with a null where the tag is (`denseVals`), the extern's
    -- positions `i` and non-null values dropped
    let ds ← (ts.zip (v :: g.map (·.2.2))).mapM fun (ty, (m, ve)) => denseVals path ty x i m ve
    pure ([← swapTag t, (n, .pos)] ++ ds, cs, ns.drop ts.length)
  | .one, x :: cs, _ :: ns => pure ([x], cs, ns)
  | _, _, _ => .error s!"{path}: a side whose object is no CSV column set (a list of no atom, a sum of no `1+S`), or too few parts"

/-- The parts `es` read under `Db.Csv.symText cols`, each symbol column's three text parts replaced by its ids' one part
    (`intern`) into the one dictionary `D`, left to right; the grown dictionary. -/
def internCsv (path : String) (D : Dict) : Db.CsvCols → List (USize × Enc) → Except String (List (USize × Enc) × Dict)
  | [], es => pure (es, D)
  | (c, s, t, _) :: cols, es =>
    if t = .sym then do
      let ⟨n, x, es⟩ ← encVals path (.arr (.atom .char)) es
      let (D, y) ← intern s!"{path}: column '{c}'" D x
      let (es, D) ← internCsv path D cols es
      pure ((n, y.enc) :: es, D)
    else do
      let (rest, D) ← internCsv path D cols (es.drop s.encs)
      pure (es.take s.encs ++ rest, D)

/-- The CSV file `path` as the table `K ⟶ S`, its symbol columns interned into the database's dictionary `D`, its
    header `cols` (the key's columns then the value's, `Db.CsvCols`), its fields split at `sep` (`,` CSV, `\t` TSV), each column read straight into its encoding
    (`Db.csvRead`, `ofCsv`, `encVals`), a symbol column as its texts then interned (`internCsv`); `K = []`: positions,
    the frame of its rows (`frame`), else keyed, its rows canonical (`canon`). The answer carries the grown `D`. A
    program's CSV inputs (`n.io`) are each read into the `D` the one before grew, so two files' equal texts are one id
    (§0.2) and `∪`, `∩`, join meet on ids. -/
def readCsvDict (D : Dict) (K S : Schema) (cols : Db.CsvCols) (path : String) (sep : UInt8 := 44) :
    IO (Tab K.obj S.obj × Dict) := do
  let (n, es) ← Db.csvRead path (← IO.ofExcept ((Db.Csv.symText cols).mapError (s!"{path}: " ++ ·))) sep
  let (es, ds) ← IO.ofExcept (internCsv path D cols es)
  let side (R : Schema) (es : List (USize × Enc)) (ns : List String) :
      Except String (Vals R.obj n × List (USize × Enc) × List String) := do
    let (ps, es, ns) ← ofCsv path R.obj es ns
    let ⟨m, x, rest⟩ ← encVals path R.obj ps
    unless rest.isEmpty do .error s!"{path}: {rest.length} column parts past a side"
    if h : m = n then pure (h ▸ x, es, ns) else .error s!"{path}: a side of {m} rows in a file of {n}"
  let done (es : List (USize × Enc)) : Except String Unit :=
    unless es.isEmpty do .error s!"{path}: {es.length} column parts past the schema"
  let ns := cols.map (·.1)
  match K with
  | [] => IO.ofExcept (do let (v, es, _) ← side S es ns; done es; pure (← frame v, ds))
  | K => IO.ofExcept (do
    let (k, es, ns) ← side K es ns
    let (v, es, _) ← side S es ns
    done es; pure (← canon path ⟨n, k, v⟩, ds))

/-- The encodings of the side `x`'s CSV columns' parts with their counts (`toCsv` of `cols`' order), as
    `Db.CsvShape.atoms` lists them; which objects a CSV column may be is `Db.Csv.schema`'s to say. -/
def csvEncs {A : Obj} {n : USize} (path : String) (x : Vals A n) : Except String (List (USize × Enc)) := do
  -- a side of `1` stores no column; its CSV part is its one element's code `0` in each of its rows
  let ps ← (cols A x "").mapM fun
    | (_, .inl k) => return (k, ← colConst k 0)
    | (_, .inr ⟨_, k, y⟩) => return (k, y.enc)
  let (cs, rest) ← toCsv path A ps
  unless rest.isEmpty do .error s!"{path}: {rest.length} column parts past a side"
  pure cs

/-- The converse of `internCsv`: each symbol column's ids part replaced by its texts' three parts, decoded through
    the database's dictionary `D` (`decode`); a symbol column with no dictionary is refused. -/
def decodeCsv (path : String) (ds : Option Dict) : Db.CsvCols → List (USize × Enc) → Except String (List (USize × Enc))
  | [], es => pure es
  | (c, s, t, _) :: cols, es =>
    if t = .sym then do
      let (k, e) :: es := es | .error s!"{path}: no part left for the symbol column '{c}'"
      let some D := ds | .error s!"{path}: the symbol column '{c}' and no dictionary"
      let x ← decode s!"{path}: column '{c}'" D (← Arr.of .sym k e s!"{path}: column '{c}'")
      pure ((← csvEncs path x) ++ (← decodeCsv path ds cols es))
    else do pure (es.take s.encs ++ (← decodeCsv path ds cols (es.drop s.encs)))

/-- The table `t : K ⟶ S` as the CSV file `path`, the converse of `readCsvDict`: its header `cols`, then each row's
    key columns and value columns, written from their encodings (`Db.csvWrite`), a symbol column as its texts through
    the database's dictionary `ds` (`decodeCsv`); `K = []`: positions, the value columns only, rows renumbered by their
    order, as `write` drops the key. -/
def writeCsv (ds : Option Dict) (K S : Schema) (cols : Db.CsvCols) (path : String) (t : Tab K.obj S.obj)
    (sep : UInt8 := 44) : IO Unit := do
  let ks ← match K with | [] => pure [] | _ => IO.ofExcept (csvEncs path t.key)
  let es ← IO.ofExcept (decodeCsv path ds cols (ks ++ (← IO.ofExcept (csvEncs path t.val))))
  Db.csvWrite path (← IO.ofExcept ((Db.Csv.symText cols).mapError (s!"{path}: " ++ ·))) sep t.n es

/-- The table of the run-time definition `x` (IO design B): its code run closed, as a closed definition's is
    (`Expand.emit`), its error the op's message after `x`. -/
def ofRun {A B : Obj} (x : String) (r : Rel.Rel A B) : IO (Tab A B) :=
  IO.ofExcept ((r.runE {}).mapError (s!"{x}: " ++ ·))

end Rel.Lang.Table
