import Rel.Kernel.Db.Csv

/-! The CSV case table (IO design C.5): the model `csvWords`/`csvText` on every row of C.3, every rule of C.2 and every
refusal of C.4, each by `decide +kernel`; then the extern `csvRead` (Rust) beside its body on every file the table reads,
as `decide` beside `#guard` for a pure kernel. The atoms' cases are one `match` over `QAtomicType`, so a new atom has no
case until one is written, and `atom_cases` is proved constructor by constructor. -/

namespace Rel.Db.CsvTest
open Rel Rel.Db Rel.Db.Csv

/-- An answer in a type with decidable equality. -/
def said {α : Type} : Except String α → String ⊕ α
  | .ok a => .inr a
  | .error e => .inl e

/-- The one-column file `x` with the data records `rs`. -/
def one (rs : String) : List UInt8 := bytes s!"x\n{rs}"

/-- Each atom's case: a text read, its word, the text the writer gives for the word, and a text refused. None at
    `sym` and `general`, which the schema refuses. -/
def atomCase : QAtomicType → Option (String × UInt64 × String × String)
  | .u1 => some ("1", 1, "1", "2")
  | .u8 => some ("Fe", 0xfe, "fe", "f")
  | .i8 => some ("-128", 0x80, "-128", "128")
  | .i16 => some ("007", 7, "7", "-32769")
  | .i32 => some ("-1", 0xffffffff, "-1", " 1")
  | .i64 => some ("-9223372036854775808", 0x8000000000000000, "-9223372036854775808", "9223372036854775808")
  | .f32 => some ("3.4028235e38", 0x7f7fffff, "3.4028235e38", "3.5e38")
  | .f64 => some ("0.10", 0x3fb999999999999a, "0.1", "1.")
  | .char => some ("\"\"\"\"", 34, "\"\"\"\"", "ab")
  | .date => some ("1969-12-31", 0xffffffff, "1969-12-31", "2023-02-29")
  | .datetime => some ("1970-01-02D00:00:00.5", 86400500000000, "1970-01-02D00:00:00.500000000",
      "1970-01-01D24:00:00")
  | .sym | .general => none

/-- An atom's case holds: the text reads as the word, the word writes as the text, the refused text is refused at
    row 0, line 2, naming the column's form. -/
def atomOk (t : QAtomicType) : Bool :=
  match atomCase t with
  | some (good, w, back, bad) =>
    said (csvWords [("x", t, [])] (one s!"{good}\n")) == .inr (1, [#[w]]) &&
    said (csvText [("x", t, [])] 1 [#[w]]) == .inr (one s!"{back}\n") &&
    said (csvWords [("x", t, [])] (one s!"{bad}\n")) ==
      .inl s!"row 0 (line 2), column 'x': expected {form t []}, found {shown (bytes bad)}"
  | none => true

theorem atom_cases (t : QAtomicType) : atomOk t = true := by cases t <;> decide +kernel

/-- Every atom, for the files the extern reads; `atoms_all` makes a new constructor a missing obligation. -/
def atoms : List QAtomicType := [.u1, .u8, .i16, .i32, .i64, .f32, .f64, .char, .i8, .sym, .date, .datetime, .general]

theorem atoms_all (t : QAtomicType) : t ∈ atoms := by cases t <;> decide

/-- The writer refuses `general` before any word, as the reader does (`readCases`). -/
example : said (csvText [("g", .general, [])] 0 [#[]]) =
    .inl "column 'g' is a general column, which the own format does not hold" := by decide +kernel

/-! ### Floats -/

/-- Shortest text, next to a power of two and at both ends of the range; the exponent form outside `[1e-5, 1e17)`. -/
example : ([0x3ff0000000000000, 0x3fefffffffffffff, 0x4340000000000000, 0x0010000000000000, 1, 0x7fefffffffffffff,
    0x3ee4f8b588e368f1, 0x3ee4f8b588e368f0, 0x4376345785d8a000, 0xc00c000000000000, 0x7ff0000000000000,
    0xfff0000000000000].map (fmtFloat 52 11)) =
    ["1", "0.9999999999999999", "9007199254740992", "2.2250738585072014e-308", "5e-324", "1.7976931348623157e308",
     "0.00001", "9.999999999999999e-6", "1e17", "-3.5", "0w", "-0w"].map (some ∘ bytes) := by
  decide +kernel

/-- Ties to even; a zero of either sign reads as `+0`; underflow to `+0`; beyond the largest finite value refused. -/
def floatReads : List (String × Option UInt64) :=
  [("9007199254740993", some 0x4340000000000000), ("-0", some 0), ("-0.0e5", some 0), ("2.4e-324", some 0),
   ("2.5e-324", some 1), ("1e-99999", some 0), ("1.7976931348623158e308", some 0x7fefffffffffffff),
   ("1.7976931348623159e308", none), ("1e99999", none), ("1E+2", some 0x4059000000000000), (".5", none), ("+1", none),
   ("1e", none), ("0w", some 0x7ff0000000000000), ("-0w", some 0xfff0000000000000)]

example : floatReads.all (fun (s, w) => readFloat 52 11 (bytes s) == w) = true := by decide +kernel

/-- A NaN and `-0` have no text: the column is not canonical (ruling 6). -/
example : said (csvText [("f", .f64, [])] 2 [#[0, 0x8000000000000000]]) =
    .inl "row 1, column 'f': the word 9223372036854775808 has no text as f64: a finite decimal, 0w or -0w" := by
  decide +kernel
example : said (csvText [("f", .f32, [])] 1 [#[0x7fc00000]]) =
    .inl "row 0, column 'f': the word 2143289344 has no text as f32: a finite decimal, 0w or -0w" := by decide +kernel

/-! ### Named elements, records and the epoch: the writer -/

def kcols : CsvCols := [("k", .u8, ["A", "B,x", "C\"D"])]
def ab : CsvCols := [("a", .i64, []), ("b", .char, [])]

/-- 10000-01-01 is a word of `date` with no text (years 0001–9999). -/
example : said (csvText [("d", .date, [])] 1 [#[2932897]]) =
    .inl "row 0, column 'd': the word 2932897 has no text as date: YYYY-MM-DD in years 0001-9999" := by decide +kernel
example : said (csvText kcols 3 [#[0, 1, 2]]) = .inr (bytes "k\nA\n\"B,x\"\n\"C\"\"D\"\n") := by decide +kernel
example : said (csvText kcols 1 [#[3]]) =
    .inl "row 0, column 'k': the word 3 has no text as one of A, B,x, C\"D" := by decide +kernel
example : said (csvText ab 2 [#[1, 2], #[10, 13]]) = .inr (bytes "a,b\n1,\"\n\"\n2,\"\r\"\n") := by decide +kernel
example : said (csvText ab 0 [#[], #[]]) = .inr (bytes "a,b\n") := by decide +kernel
/-- Columns of unequal length, or not one per schema column, are refused by the writer. -/
example : said (csvText ab 2 [#[1, 2], #[120]]) = .inl "column 'b' holds 1 words, not 2" := by decide +kernel
example : said (csvText ab 1 [#[1]]) = .inl "1 word columns, the schema [a, b] has 2" := by decide +kernel

/-! ### The reader's case table -/

/-- A reader's case: the schema, the file's bytes, and the model's answer. -/
abbrev ReadCase := CsvCols × List UInt8 × (String ⊕ (Nat × List (Array UInt64)))

def readCases : List ReadCase := [
  -- `sym` and `general` columns, and no column, are refused before any byte is read
  ([("s", .sym, [])], [], .inl "column 's' is a symbol column, which waits for the own-format sym writer (D.9 step 6)"),
  ([("g", .general, [])], one "1\n", .inl "column 'g' is a general column, which the own format does not hold"),
  ([], bytes "\n", .inl "the schema has no column, and a CSV record has at least one field"),
  -- the epoch, 1970-01-01 (owner, question F.3: N), and the ends of the range
  ([("d", .date, [])], bytes "d\n1969-12-31\n1970-01-01\n1970-01-02\n", .inr (3, [#[0xffffffff, 0, 1]])),
  ([("t", .datetime, [])],
    bytes "t\n1969-12-31D23:59:59.999999999\n1970-01-01D00:00:00\n1970-01-01D00:00:00.000000001\n",
    .inr (3, [#[0xffffffffffffffff, 0, 1]])),
  ([("d", .date, [])], bytes "d\n0001-01-01\n9999-12-31\n2000-02-29\n", .inr (3, [#[4294248134, 2932896, 11016]])),
  ([("t", .datetime, [])], bytes "t\n2262-04-12D00:00:00\n",
    .inl "row 0 (line 2), column 't': expected datetime: YYYY-MM-DDDhh:mm:ss, up to 9 fraction digits, within i64 nanoseconds of 1970-01-01, found '2262-04-12D00:00:00'"),
  -- named elements: a field equal to a name, quoted where it holds `,` or `"`
  (kcols, bytes "k\nA\n\"B,x\"\n\"C\"\"D\"\n", .inr (3, [#[0, 1, 2]])),
  (kcols, bytes "k\nB\n", .inl "row 0 (line 2), column 'k': expected one of A, B,x, C\"D, found 'B'"),
  -- `\r\n` and `\n` give the same words, the last record with or without its end; a quoted field holds `,` `"` and
  -- both record ends
  (ab, bytes "a,b\r\n1,x\r\n2,\",\"\r\n", .inr (2, [#[1, 2], #[120, 44]])),
  (ab, bytes "a,b\n1,x\n2,\",\"", .inr (2, [#[1, 2], #[120, 44]])),
  (ab, bytes "a,\"b\"\r\n\"1\",\"\n\"\n2,\"\r\"\n", .inr (2, [#[1, 2], #[10, 13]])),
  -- no record at all: the header is missing; a byte-order mark is not skipped
  (ab, [], .inl "line 1: the header has 0 fields, the schema [a, b] has 2"),
  (ab, bytes "a,b\n", .inr (0, [#[], #[]])),
  (ab, [0xef, 0xbb, 0xbf] ++ bytes "a,b\n", .inl "line 1: header field 0 is '\\xef\\xbb\\xbfa', the schema [a, b] has 'a'"),
  (ab, bytes "a,c\n", .inl "line 1: header field 1 is 'c', the schema [a, b] has 'b'"),
  (ab, bytes "a,b,c\n", .inl "line 1: the header has 3 fields, the schema [a, b] has 2"),
  -- the refusals of C.4, each at its line: a line after a quoted `\n` counts it
  (ab, bytes "a,b\n1,\"\n\"\n2\n", .inl "row 1 (line 4): 1 fields, the schema [a, b] has 2"),
  (ab, bytes "a,b\n1,x,\n", .inl "row 0 (line 2): 3 fields, the schema [a, b] has 2"),
  (ab, bytes "a,b\n,x\n",
    .inl "row 0 (line 2), column 'a': expected i64: an integer from -9223372036854775808 to 9223372036854775807, found ''"),
  (ab, bytes "a,b\n1,x\"y\n", .inl "line 2: a '\"' inside an unquoted field"),
  (ab, bytes "a,b\n1,\"x\n", .inl "a quoted field opened at line 2 is not closed"),
  (ab, bytes "a,b\n1,\"x\"y\n", .inl "line 2: after a closing '\"' comes 'y', not ',' or a record end"),
  (ab, bytes "a,b\n1,\"x\"\rx\n", .inl "line 2: after a closing '\"' comes '\\x0d' with no '\\x0a' after it"),
  -- the structure of the whole file is checked before the header, the header before the rows
  (ab, bytes "a,c\n1,x\"\n", .inl "line 2: a '\"' inside an unquoted field"),
  (ab, bytes "a,c\n1,xx\n", .inl "line 1: header field 1 is 'c', the schema [a, b] has 'b'"),
  -- a long field is cut at 40 bytes in a refusal
  (ab, bytes "a,b\n12345678901234567890123456789012345678901234567890,x\n",
    .inl "row 0 (line 2), column 'a': expected i64: an integer from -9223372036854775808 to 9223372036854775807, found '1234567890123456789012345678901234567890' (the first 40 of 50 bytes)")]

theorem readCases_model : readCases.all (fun (c, b, a) => decide (said (csvWords c b) = a)) = true := by decide +kernel

/-! ### The extern beside its body -/

/-- `ab` over `n` rows, row `i` being `f i`: files of several blocks of `2^lgEnc` rows, for the block-wise reader. -/
def rowsOf (n : Nat) (f : Nat → String) : List UInt8 := bytes (String.join ("a,b\n" :: (List.range n).map f))

/-- Every file the extern reads: each case of the table, each atom's text read and refused, each float text at both
    widths, and files over several blocks, whose first refusal lies past the first block — a cell before a short
    record, a short record before a cell, two columns refused in one row. -/
def files : List (CsvCols × List UInt8) :=
  readCases.map (fun (c, b, _) => (c, b)) ++
  atoms.flatMap (fun t => match atomCase t with
    | some (good, _, _, bad) => [([("x", t, [])], one s!"{good}\n"), ([("x", t, [])], one s!"{bad}\n")]
    | none => [([("x", t, [])], one "1\n")]) ++
  [QAtomicType.f64, .f32].flatMap (fun t => floatReads.map fun (s, _) => ([("x", t, [])], one s!"{s}\n")) ++
  [(ab, rowsOf 2500 fun i => s!"{i},\"{Char.ofNat (97 + i % 26)}\"\n"),
   (ab, rowsOf 2500 fun i => if i = 1400 then "z,x\n" else if i = 1500 then "1\n" else s!"{i},x\n"),
   (ab, rowsOf 2500 fun i => if i = 1300 then "1\n" else if i = 2000 then "z,x\n" else s!"{i},x\n"),
   (ab, rowsOf 2500 fun i => if i = 2100 then "z,xy\n" else if i = 2200 then "1,xy\n" else s!"{i},x\n"),
   (ab, rowsOf 2048 fun i => s!"{i},\"\n\"\r\n"),
   (kcols, bytes ("k\n" ++ String.join ((List.range 3000).map fun i => ["A\n", "\"B,x\"\n", "\"C\"\"D\"\n"].getD (i % 3) "")))]

/-- An answer as compared: the row count and each column's `foR` parts, any other constructor by its index, or the
    error's text. -/
def key (r : Except IO.Error (USize × List Enc)) : String ⊕ (USize × List ((List UInt8 × List UInt8) ⊕ Nat)) :=
  match r with
  | .ok (n, es) => .inr (n, es.map fun | .foR m p => .inl (m.data.toList, p.data.toList) | e => .inr e.ctorIdx)
  | .error e => .inl (toString e)

/-- The file at `p` read by the extern `csvRead` and by its body: the same answer, else an error naming both. -/
def agrees (p : System.FilePath) (cols : CsvCols) : IO Unit := do
  let rust ← (csvRead p.toString cols).toBaseIO
  let body ← (do
    let (n, ws) ← IO.ofExcept ((csvWords cols (← IO.FS.readBinFile p).data.toList).mapError (s!"{p}: {·}"))
    return (n.toUSize, ws.map Kernel.wordsFoR) : IO (USize × List Enc)).toBaseIO
  unless decide (key rust = key body) do
    let say := fun | Sum.inl e => e | Sum.inr (n, ks) => s!"{n} rows, {ks.length} columns"
    throw (IO.userError s!"csvRead {names cols} on {p}: the extern answers {say (key rust)}, the body {say (key body)}")

/-- Each file written to a temporary and read by both; then a path that does not exist (the OS error of both). -/
def run : IO Nat := do
  for (c, b) in files do
    let (h, p) ← IO.FS.createTempFile
    h.flush
    IO.FS.writeBinFile p ⟨b.toArray⟩
    agrees p c
    IO.FS.removeFile p
  let (h, p) ← IO.FS.createTempFile
  h.flush
  IO.FS.removeFile p
  agrees p ab
  return files.length + 1

/-- info: csvRead agrees with its body on 88 files -/
#guard_msgs in
#eval do IO.println s!"csvRead agrees with its body on {← run} files"

end Rel.Db.CsvTest
