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
  | .date => some ("1969.12.31", 0xffffffff, "1969.12.31", "2023.02.29")
  | .datetime => some ("1970.01.02D00:00:00.5", 86400500000000, "1970.01.02D00:00:00.500000000",
      "1970.01.01D24:00:00")
  | .sym | .general => none

/-- An atom's case holds: the text reads as the word, the word writes as the text, the refused text is refused at
    row 0, line 2, naming the column's form. -/
def atomOk (t : QAtomicType) : Bool :=
  match atomCase t with
  | some (good, w, back, bad) =>
    said (csvWords [("x", .atom, t, [])] (one s!"{good}\n")) == .inr (1, [#[w]]) &&
    said (csvText [("x", .atom, t, [])] 1 [#[w]]) == .inr (one s!"{back}\n") &&
    said (csvWords [("x", .atom, t, [])] (one s!"{bad}\n")) ==
      .inl s!"row 0 (line 2), column 'x': expected {form t []}, found {shown (bytes bad)}"
  | none => true

theorem atom_cases (t : QAtomicType) : atomOk t = true := by cases t <;> decide +kernel

/-- Every atom, for the files the extern reads; `atoms_all` makes a new constructor a missing obligation. -/
def atoms : List QAtomicType := [.u1, .u8, .i16, .i32, .i64, .f32, .f64, .char, .i8, .sym, .date, .datetime, .general]

theorem atoms_all (t : QAtomicType) : t ∈ atoms := by cases t <;> decide

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

/-! ### The writer's case table -/

def kcols : CsvCols := [("k", .atom, .u8, ["A", "B,x", "C\"D"])]
def ab : CsvCols := [("a", .atom, .i64, []), ("b", .atom, .char, [])]
/-- A nullable `i64` column (`V+1`) and a text column (`[C]`), IO step I8. -/
def vs : CsvCols := [("v", .null, .i64, []), ("s", .text, .char, [])]
def v1 : CsvCols := [("v", .null, .i64, [])]
def s1 : CsvCols := [("s", .text, .char, [])]

/-- By hand: rows `(1, "ab")`, `(null, "")`, `(-3, "x,\"")`. `v`: tags `0 1 0`, each row's position in its side
    `0 0 1`, the values `1 -3`, one null; `s`: spans `[0,2) [2,2) [2,5)`, the bytes `a b x , "`. -/
def vsParts : List (Array UInt64) :=
  [#[0, 1, 0], #[0, 0, 1], #[1, 0xfffffffffffffffd], #[0], #[0, 2, 2], #[2, 2, 5], #[97, 98, 120, 44, 34]]
def vsText : String := "v,s\n1,ab\n,\n-3,\"x,\"\"\"\n"

/-- A writer's case: the schema, the row count, each column's words, and the model's answer. -/
abbrev WriteCase := CsvCols × Nat × List (Array UInt64) × (String ⊕ List UInt8)

/-- Every refusal of C.6, each by the one rule `cell` (the word's text must read back), and the accepted forms. -/
def writeCases : List WriteCase := [
  -- a schema CSV does not hold is refused before any word, as the reader refuses it (`readCases`)
  ([("g", .atom, .general, [])], 0, [#[]], .inl "column 'g' is a general column, which the own format does not hold"),
  ([("s", .atom, .sym, [])], 0, [#[]], .inl "column 's' is a symbol column, read and written as its text through its dictionary (Table.readCsvDict, Table.writeCsv)"),
  ([], 0, [], .inl "the schema has no column, and a CSV record has at least one field"),
  -- a NaN and `-0` have no text: the column is not canonical (ruling 6)
  ([("f", .atom, .f64, [])], 2, [#[0, 0x8000000000000000]],
    .inl "row 1, column 'f': the word 9223372036854775808 has no text as f64: a finite decimal, 0w or -0w"),
  ([("f", .atom, .f64, [])], 1, [#[0x7ff8000000000000]],
    .inl "row 0, column 'f': the word 9221120237041090560 has no text as f64: a finite decimal, 0w or -0w"),
  ([("f", .atom, .f32, [])], 1, [#[0x7fc00000]],
    .inl "row 0, column 'f': the word 2143289344 has no text as f32: a finite decimal, 0w or -0w"),
  ([("f", .atom, .f32, [])], 1, [#[0x80000000]],
    .inl "row 0, column 'f': the word 2147483648 has no text as f32: a finite decimal, 0w or -0w"),
  -- the plain form ends at `1e-5` and `1e17`
  ([("f", .atom, .f64, [])], 3, [#[0x3ee4f8b588e368f1, 0x3ee4f8b588e368f0, 0x4376345785d8a000]],
    .inr (bytes "f\n0.00001\n9.999999999999999e-6\n1e17\n")),
  -- a date outside years 0001–9999: 10000.01.01, 0000.12.31, the ends of `i32`
  ([("d", .atom, .date, [])], 1, [#[2932897]],
    .inl "row 0, column 'd': the word 2932897 has no text as date: yyyy.mm.dd in years 0001-9999"),
  ([("d", .atom, .date, [])], 1, [#[4294248133]],
    .inl "row 0, column 'd': the word 4294248133 has no text as date: yyyy.mm.dd in years 0001-9999"),
  ([("d", .atom, .date, [])], 2, [#[1, 0x7fffffff]],
    .inl "row 1, column 'd': the word 2147483647 has no text as date: yyyy.mm.dd in years 0001-9999"),
  ([("d", .atom, .date, [])], 1, [#[0x80000000]],
    .inl "row 0, column 'd': the word 2147483648 has no text as date: yyyy.mm.dd in years 0001-9999"),
  ([("d", .atom, .date, [])], 3, [#[4294248134, 2932896, 0xffffffff]], .inr (bytes "d\n0001.01.01\n9999.12.31\n1969.12.31\n")),
  -- every `i64` of nanoseconds is a datetime of years 1677–2262, so a datetime word is never refused
  ([("t", .atom, .datetime, [])], 3, [#[0x8000000000000000, 0x7fffffffffffffff, 86400500000000]],
    .inr (bytes "t\n1677.09.21D00:12:43.145224192\n2262.04.11D23:47:16.854775807\n1970.01.02D00:00:00.500000000\n")),
  -- a word that is no index of the names, or wider than its atom
  (kcols, 3, [#[0, 1, 2]], .inr (bytes "k\nA\n\"B,x\"\n\"C\"\"D\"\n")),
  (kcols, 1, [#[3]], .inl "row 0, column 'k': the word 3 has no text as one of A, B,x, C\"D"),
  ([("x", .atom, .u1, [])], 2, [#[1, 2]], .inl "row 1, column 'x': the word 2 has no text as u1: 0 or 1"),
  ([("x", .atom, .u8, [])], 1, [#[0x100]], .inl "row 0, column 'x': the word 256 has no text as u8: two hex digits"),
  ([("x", .atom, .char, [])], 1, [#[0x141]], .inl "row 0, column 'x': the word 321 has no text as char: one byte"),
  ([("x", .atom, .i8, [])], 2, [#[0x80, 0x180]], .inl "row 1, column 'x': the word 384 has no text as i8: an integer from -128 to 127"),
  ([("x", .atom, .i16, [])], 1, [#[0x10000]],
    .inl "row 0, column 'x': the word 65536 has no text as i16: an integer from -32768 to 32767"),
  ([("x", .atom, .i32, [])], 1, [#[0x100000000]],
    .inl "row 0, column 'x': the word 4294967296 has no text as i32: an integer from -2147483648 to 2147483647"),
  ([("d", .atom, .date, [])], 1, [#[0x100000000]],
    .inl "row 0, column 'd': the word 4294967296 has no text as date: yyyy.mm.dd in years 0001-9999"),
  -- the first refusal in row order, then column order
  (ab, 2, [#[1, 2], #[0x100, 0x100]], .inl "row 0, column 'b': the word 256 has no text as char: one byte"),
  -- records: a field holding `,` `"` `\r` `\n` is quoted, a header name too; no row is the header alone
  (ab, 2, [#[1, 2], #[10, 13]], .inr (bytes "a,b\n1,\"\n\"\n2,\"\r\"\n")),
  (ab, 0, [#[], #[]], .inr (bytes "a,b\n")),
  ([("a,b", .atom, .i64, []), ("\"", .atom, .u1, [])], 1, [#[5], #[0]], .inr (bytes "\"a,b\",\"\"\"\"\n5,0\n")),
  -- columns of unequal length, or not one per schema column
  (ab, 2, [#[1, 2], #[120]], .inl "column 'b' holds 1 words, not 2"),
  (ab, 1, [#[1]], .inl "1 word columns, the schema [a, b] is stored as 2"),
  (ab, 1, [#[1], #[120], #[1]], .inl "3 word columns, the schema [a, b] is stored as 2"),
  -- a nullable and a text column: the null is the empty field, a cell its bytes quoted as any field
  (vs, 3, vsParts, .inr (bytes vsText)),
  (vs, 3, vsParts.take 6, .inl "6 word columns, the schema [v, s] is stored as 7"),
  -- any layout of the same rows: positions out of order, a value no row reaches
  (v1, 3, [#[0, 1, 0], #[1, 0, 0], #[7, 5, 9], #[0, 0]], .inr (bytes "v\n5\n\n7\n")),
  -- a position outside its payload, a tag other than 0/1, a span outside the bytes, a byte past 255
  (v1, 1, [#[0], #[3], #[1], #[]], .inl "row 0, column 'v': position 3 past the 1 values of its left side"),
  (v1, 1, [#[1], #[0], #[], #[]], .inl "row 0, column 'v': position 0 past the 0 values of its right side"),
  (v1, 1, [#[2], #[0], #[1], #[1]], .inl "row 0, column 'v': tag 2, not 0 or 1"),
  (s1, 1, [#[1], #[0], #[]], .inl "row 0, column 's': cell [1, 0) outside the 0 bytes"),
  (s1, 1, [#[0], #[1], #[300]], .inl "row 0, column 's': the word 300 has no text as text: any bytes"),
  (v1, 2, [#[0], #[0], #[1], #[]], .inl "column 'v' holds 1 words, not 2"),
  -- every row's positions before any text: row 1's position before row 0's byte
  (s1 ++ v1, 2, [#[0, 0], #[1, 0], #[300], #[0, 0], #[0, 5], #[1], #[]],
    .inl "row 1, column 'v': position 5 past the 1 values of its left side"),
  -- schemas refused: a list of no char, a null that is also a text of the atom
  ([("s", .text, .i64, [])], 0, [#[], #[], #[]],
    .inl "column 's' is a list of i64: an integer from -9223372036854775808 to 9223372036854775807; a CSV field holds a list of char only (text)"),
  ([("v", .null, .u8, ["A", ""])], 0, [#[], #[], #[], #[]],
    .inl "column 'v' is nullable, and the empty field, its null, is also a text of one of A, ")]

theorem writeCases_model : writeCases.all (fun (c, n, ws, a) => decide (said (csvText c n ws) = a)) = true := by
  decide +kernel

/-! ### The reader's case table -/

/-- A reader's case: the schema, the file's bytes, and the model's answer. -/
abbrev ReadCase := CsvCols × List UInt8 × (String ⊕ (Nat × List (Array UInt64)))

def readCases : List ReadCase := [
  -- `sym` and `general` columns, and no column, are refused before any byte is read
  ([("s", .atom, .sym, [])], [], .inl "column 's' is a symbol column, read and written as its text through its dictionary (Table.readCsvDict, Table.writeCsv)"),
  ([("g", .atom, .general, [])], one "1\n", .inl "column 'g' is a general column, which the own format does not hold"),
  ([], bytes "\n", .inl "the schema has no column, and a CSV record has at least one field"),
  -- the epoch, 1970.01.01 (owner, question F.3: N), and the ends of the range
  ([("d", .atom, .date, [])], bytes "d\n1969.12.31\n1970.01.01\n1970.01.02\n", .inr (3, [#[0xffffffff, 0, 1]])),
  ([("t", .atom, .datetime, [])],
    bytes "t\n1969.12.31D23:59:59.999999999\n1970.01.01D00:00:00\n1970.01.01D00:00:00.000000001\n",
    .inr (3, [#[0xffffffffffffffff, 0, 1]])),
  ([("d", .atom, .date, [])], bytes "d\n0001.01.01\n9999.12.31\n2000.02.29\n", .inr (3, [#[4294248134, 2932896, 11016]])),
  ([("t", .atom, .datetime, [])], bytes "t\n2262.04.12D00:00:00\n",
    .inl "row 0 (line 2), column 't': expected datetime: yyyy.mm.ddDhh:mm:ss, up to 9 fraction digits, within i64 nanoseconds of 1970-01-01, found '2262.04.12D00:00:00'"),
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
    .inl "row 0 (line 2), column 'a': expected i64: an integer from -9223372036854775808 to 9223372036854775807, found '1234567890123456789012345678901234567890' (the first 40 of 50 bytes)"),
  -- a nullable and a text column (IO step I8); a quoted empty field is the null too, its bytes being none
  (vs, bytes vsText, .inr (3, vsParts)),
  (vs, bytes "v,s\r\n1,ab\r\n\"\",\"\"\r\n-3,\"x,\"\"\"", .inr (3, vsParts)),
  (vs, bytes "v,s\n", .inr (0, [#[], #[], #[], #[], #[], #[], #[]])),
  (v1, bytes "v\nx\n",
    .inl "row 0 (line 2), column 'v': expected i64: an integer from -9223372036854775808 to 9223372036854775807, or the empty field (the null), found 'x'"),
  (s1, bytes "s\n\" a\n\"\n", .inr (1, [#[0], #[3], #[32, 97, 10]])),
  ([("s", .text, .u8, [])], bytes "s\n",
    .inl "column 's' is a list of u8: two hex digits; a CSV field holds a list of char only (text)"),
  ([("v", .null, .u8, ["A", ""])], bytes "v\n",
    .inl "column 'v' is nullable, and the empty field, its null, is also a text of one of A, ")]

theorem readCases_model : readCases.all (fun (c, b, a) => decide (said (csvWords c b) = a)) = true := by decide +kernel

/-! ### The extern beside its body -/

/-- `ab` over `n` rows, row `i` being `f i`: files of several blocks of `2^lgEnc` rows, for the block-wise reader. -/
def rowsOf (n : Nat) (f : Nat → String) : List UInt8 := bytes (String.join ("a,b\n" :: (List.range n).map f))

/-- `vs` over `n` rows, row `i` being `bad i` where that is some: every third row null with an empty cell, the others
    the value `i` and a cell of `i % 5` bytes, every seventh quoted with `,` and `"` in it. -/
def vsCell (i : Nat) : String :=
  if i % 7 = 0 then s!"\"q,\"\"{i % 5}\"" else String.ofList (List.replicate (i % 5) (Char.ofNat (97 + i % 26)))
def vsRows (n : Nat) (bad : Nat → Option String) : List UInt8 :=
  bytes (String.join ("v,s\n" :: (List.range n).map fun i =>
    (bad i).getD (if i % 3 = 1 then ",\n" else s!"{i},{vsCell i}\n")))

/-- Every file the extern reads:each case of the table, each atom's text read and refused, each float text at both
    widths, and files over several blocks, whose first refusal lies past the first block — a cell before a short
    record, a short record before a cell, two columns refused in one row. -/
def files : List (CsvCols × List UInt8) :=
  readCases.map (fun (c, b, _) => (c, b)) ++
  atoms.flatMap (fun t => match atomCase t with
    | some (good, _, _, bad) => [([("x", .atom, t, [])], one s!"{good}\n"), ([("x", .atom, t, [])], one s!"{bad}\n")]
    | none => [([("x", .atom, t, [])], one "1\n")]) ++
  [QAtomicType.f64, .f32].flatMap (fun t => floatReads.map fun (s, _) => ([("x", .atom, t, [])], one s!"{s}\n")) ++
  [(ab, rowsOf 2500 fun i => s!"{i},\"{Char.ofNat (97 + i % 26)}\"\n"),
   (ab, rowsOf 2500 fun i => if i = 1400 then "z,x\n" else if i = 1500 then "1\n" else s!"{i},x\n"),
   (ab, rowsOf 2500 fun i => if i = 1300 then "1\n" else if i = 2000 then "z,x\n" else s!"{i},x\n"),
   (ab, rowsOf 2500 fun i => if i = 2100 then "z,xy\n" else if i = 2200 then "1,xy\n" else s!"{i},x\n"),
   (ab, rowsOf 2048 fun i => s!"{i},\"\n\"\r\n"),
   (kcols, bytes ("k\n" ++ String.join ((List.range 3000).map fun i => ["A\n", "\"B,x\"\n", "\"C\"\"D\"\n"].getD (i % 3) ""))),
   (vs, vsRows 2500 fun _ => none), (vs, vsRows 2500 fun i => if i = 2100 then some "z,ab\n" else none)]

/-- An answer as compared: the row count and each part's count and `foR` parts, any other constructor by its index,
    or the error's text. -/
abbrev Key := String ⊕ (USize × List (USize × ((List UInt8 × List UInt8) ⊕ Nat)))

def key (r : Except IO.Error (USize × List (USize × Enc))) : Key :=
  match r with
  | .ok (n, es) => .inr (n, es.map fun | (k, .foR m p) => (k, .inl (m.data.toList, p.data.toList)) | (k, e) => (k, .inr e.ctorIdx))
  | .error e => .inl (toString e)

/-- Two keys equal, compared side by side: instance search finds no `DecidableEq` for `Key` as a whole (the product of
    the count and the list is too deep for it), and does for each component. -/
def Key.same : Key → Key → Bool
  | .inl a, .inl b => decide (a = b)
  | .inr (n, ks), .inr (m, ls) => decide (n = m) && decide (ks = ls)
  | _, _ => false

/-- A key as the error names it. -/
def Key.say : Key → String | .inl e => e | .inr (n, ks) => s!"{n} rows, {ks.length} parts"

/-- The file at `p` read by the extern `csvRead` and by its body: the same answer, else an error naming both. -/
def agrees (p : System.FilePath) (cols : CsvCols) : IO Unit := do
  let rust ← (csvRead p.toString cols).toBaseIO
  let body ← (do
    let (n, ws) ← IO.ofExcept ((csvWords cols (← IO.FS.readBinFile p).data.toList).mapError (s!"{p}: {·}"))
    return (n.toUSize, ws.map fun a => (a.size.toUSize, Kernel.wordsFoR a)) : IO (USize × List (USize × Enc))).toBaseIO
  unless (key rust).same (key body) do
    throw (IO.userError s!"csvRead {names cols} on {p}: the extern answers {(key rust).say}, the body {(key body).say}")

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

/-- info: csvRead agrees with its body on 97 files -/
#guard_msgs in
#eval do IO.println s!"csvRead agrees with its body on {← run} files"

/-! ### The writer extern beside its body -/

/-- Words `a` encoded from a dense payload at `t`'s width (8 bytes at an atom of none), little-endian. -/
def dense (t : QAtomicType) (a : Array UInt64) : Enc :=
  Ext.Enc.ofBytes (t.width.getD 8) ⟨(a.toList.flatMap fun x => (List.range (t.width.getD 8)).map fun k => (x >>> (8 * k).toUInt64).toUInt8).toArray⟩

/-- A word that follows no pattern: `i`'s hash. -/
def mix (i : Nat) : UInt64 := let x := (i.toUInt64 + 1) * 0x9E3779B97F4A7C15; x ^^^ (x >>> 31)

/-- `ends` of both signs, `0`, then hashed words: `k` with any exponent but the infinities' (`all`), `k` in the plain
    form's range (`plain + x % span`). -/
def floats (ends : List UInt64) (sign all plain span : UInt64) (k : Nat) : Array UInt64 :=
  (ends ++ ends.map (· ||| sign) ++ [0] ++ (List.range k).map (fun i => mix i &&& all) ++
    (List.range k).map (fun i => plain + mix (i + 7 * k) % span)).toArray

/-- f64 words at both forms' ends (`1e-5`, `1e16`, `1e17`), next to powers of two and of ten (`1e23` is a tie), the
    subnormals' ends, the largest finite value, the infinities; then hashed words. -/
def f64s : Array UInt64 :=
  floats [1, 3, 0xfffffffffffff, 0x10000000000000, 0x7fefffffffffffff, 0x3ee4f8b588e368f0, 0x3ee4f8b588e368f1,
    0x3ee4f8b588e368f2, 0x4341c37937e07fff, 0x4341c37937e08000, 0x4376345785d89fff, 0x4376345785d8a000,
    0x4376345785d8a001, 0x44b52d02c7e14af5, 0x44b52d02c7e14af6, 0x44b52d02c7e14af7, 0x3fb999999999999a,
    0x3fd3333333333333, 0x433fffffffffffff, 0x4340000000000000, 0x4340000000000001, 0x3fefffffffffffff,
    0x3ff0000000000000, 0x3ff0000000000001, 0x4059000000000000, 0x7ff0000000000000]
    0x8000000000000000 0xffefffffffffffff 0x3ee0000000000000 0xa0000000000000 400

/-- The same at f32: `1e-5`, `1e16`, `1e17`, `2 ^ 24`, `0.1`, the subnormals' ends, the largest finite value. -/
def f32s : Array UInt64 :=
  floats [1, 3, 0x7fffff, 0x800000, 0x7f7fffff, 0x3727c5ab, 0x3727c5ac, 0x3727c5ad, 0x5a0e1bc6, 0x5a0e1bc7,
    0x5a0e1bc8, 0x5bb1a2f2, 0x5bb1a2f3, 0x5bb1a2f4, 0x4b7fffff, 0x4b800000, 0x4b800001, 0x3dcccccd, 0x3f7fffff,
    0x3f800000, 0x3f800001, 0x7f800000] 0x80000000 0xff7fffff 0x37000000 0x24800000 400

/-- A column of every atom, for files of several blocks. -/
def mcols : CsvCols := [("i", .atom, .i64, []), ("f", .atom, .f64, []), ("d", .atom, .date, []), ("t", .atom, .datetime, []), kcols.getD 0 ("", .atom, .u8, []),
  ("c", .atom, .char, []), ("b", .atom, .u1, []), ("s", .atom, .i8, []), ("h", .atom, .u8, []), ("g", .atom, .f32, []), ("w", .atom, .i16, []), ("v", .atom, .i32, [])]

/-- Column `j` of `mcols` at row `i`: a hashed word its text holds. -/
def mword (j i : Nat) : UInt64 :=
  let x := mix (13 * i + j)
  match j with
  | 1 => x &&& 0xffefffffffffffff
  | 2 => wordOf 4 (((x % 3652059).toNat : Int) - 719162)
  | 4 => x % 3
  | 5 | 7 | 8 => x % 256
  | 6 => x % 2
  | 9 => x % 0x100000000 &&& 0xff7fffff
  | 10 => x % 0x10000
  | 11 => x % 0x100000000
  | _ => x

/-- `n` rows of `mcols`, the word at column `j`, row `i` replaced by `bad j i` where that is some. -/
def mwords (n : Nat) (bad : Nat → Nat → Option UInt64 := fun _ _ => none) : List (Array UInt64) :=
  (List.range mcols.length).map fun j => ((List.range n).map fun i => (bad j i).getD (mword j i)).toArray

/-- `vs`'s parts over `n` rows as `vsRows` reads them (`layout`); `rev`: the values payload reversed and each value
    row's position with it, the same rows in another layout, so the writer reads its payload from the far end. -/
def vsParts' (n : Nat) (rev : Bool) : List (Array UInt64) :=
  let fs := (List.range n).map fun i =>
    if i % 3 = 1 then [[], []] else [[i.toUInt64], (bytes (if i % 7 = 0 then s!"q,\"{i % 5}" else
      String.ofList (List.replicate (i % 5) (Char.ofNat (97 + i % 26))))).map (·.toUInt64)]
  let ps := wordsOf vs fs
  let l := (ps.getD 2 #[]).size
  if !rev then ps else
  (ps.set 1 ((ps.getD 0 #[]).zipWith (fun t k => if t = 0 then (l - 1 - k.toNat).toUInt64 else k) (ps.getD 1 #[]))).set 2
    (ps.getD 2 #[]).reverse

/-- `ps` with part `p`'s word `i` set to `w`. -/
def poke (ps : List (Array UInt64)) (p i : Nat) (w : UInt64) : List (Array UInt64) :=
  ps.set p ((ps.getD p #[]).setIfInBounds i w)

/-- Every writer's case: the table's, the floats, and files of several blocks (`2 ^ lgEnc` rows a block), whole or
    refused past the first block — two refusals in one row, a refusal at a block's first row. -/
def writes : List (CsvCols × Nat × List (Array UInt64)) :=
  [([("f", .atom, .f64, [])], f64s.size, [f64s]), ([("f", .atom, .f32, [])], f32s.size, [f32s])] ++
  writeCases.map (fun (c, n, ws, _) => (c, n, ws)) ++
  [(mcols, 2100, mwords 2100), (mcols, 1024, mwords 1024),
   (mcols, 2100, mwords 2100 fun j i => if i = 1500 ∧ j = 9 then some 0x7fc00000 else if i = 1500 ∧ j = 4 then some 7
     else if i = 2000 ∧ j = 1 then some 0x8000000000000000 else none),
   (mcols, 2100, mwords 2100 fun j i => if i = 1024 ∧ j = 2 then some 0x7fffffff else none)] ++
  [(vs, 2500, vsParts' 2500 false), (vs, 2500, vsParts' 2500 true),
   (vs, 2500, poke (vsParts' 2500 true) 1 2050 4000),
   (vs, 2500, poke (poke (vsParts' 2500 false) 1 2050 4000) 6 1500 300)]

/-- A case's parts as `Enc`s with their counts: `foR` (`wordsFoR`), and dense payloads at each part's atom, a `u1` part
    as `foR` (a dense `u1` payload has no raw words, `Enc.raw`). -/
def encs (c : CsvCols) (ws : List (Array UInt64)) : List (List (USize × Enc)) :=
  [ws.map fun a => (a.size.toUSize, Kernel.wordsFoR a),
   ((c.flatMap fun (_, s, t, _) => s.atoms t).zip ws).map fun (t, a) =>
     (a.size.toUSize, if t = some .u1 then Kernel.wordsFoR a else dense (t.getD .i64) a)]

/-- The writer's cases no word table gives: positions, a dense `u1` payload and a `gen` column (no raw words). -/
def others : List (CsvCols × Nat × List (USize × Enc)) :=
  [([("p", .atom, .i64, [])], 3, [(3, .pos)]), ([("b", .atom, .u1, [])], 1, [(1, dense .u1 #[1])]),
   ([("g", .atom, .i64, [])], 1, [(1, .gen #[])]), ([("g", .atom, .i64, [])], 0, [(0, .gen #[])])]

/-- `csvWrite`'s body, called without the extern. -/
def body (path : String) (cols : CsvCols) (n : USize) (es : List (USize × Enc)) : IO Unit := do
  if let some d := (System.FilePath.mk path).parent then IO.FS.createDirAll d
  let b ← IO.ofExcept ((do csvText cols n.toNat (← raws cols es) : Except String (List UInt8)).mapError (s!"{path}: {·}"))
  IO.FS.writeBinFile path ⟨b.toArray⟩

/-- `w` run on `p`, which holds `old\n` where it is a file: the refusal's text or none, and the bytes at `p` after. -/
def outcome (p : System.FilePath) (w : IO Unit) : IO (Option String × List UInt8) := do
  let file := fun (_ : Unit) => do return (← p.pathExists) && !(← p.isDir)
  if ← file () then IO.FS.writeBinFile p ⟨(bytes "old\n").toArray⟩
  let r ← w.toBaseIO
  let b ← if ← file () then pure (← IO.FS.readBinFile p).data.toList else pure []
  return (match r with | .ok () => none | .error e => some (toString e), b)

/-- The extern `csvWrite` and its body leave the same bytes at `p`, or refuse with the same text; and what the extern
    wrote, `csvRead` reads back as the rows written (`fieldsOf`: a layout is not given back word for word). -/
def writeAgrees (p : System.FilePath) (cols : CsvCols) (n : Nat) (es : List (USize × Enc)) : IO Unit := do
  let rust ← outcome p (csvWrite p.toString cols n.toUSize es)
  let model ← outcome p (body p.toString cols n.toUSize es)
  let say := fun (r : Option String × List UInt8) => match r.1 with | some e => s!"refuses: {e}" | none => s!"writes {r.2.length} bytes"
  -- as arrays: `List`'s `DecidableEq` recurses once per byte and overflows the stack on a file of several blocks
  unless rust.1 == model.1 && rust.2.toArray == model.2.toArray do
    -- the record holding the first byte where the two differ
    let i := ((rust.2.zip model.2).findIdx? fun (a, b) => a != b).getD 0
    let rec_ := fun (b : List UInt8) => shown (((b.take i).reverse.takeWhile (· != 10)).reverse ++ (b.drop i).takeWhile (· != 10))
    throw (IO.userError s!"csvWrite {names cols} of {n} rows on {p}: the extern {say rust}, the body {say model}; at byte {i} the extern has {rec_ rust.2}, the body {rec_ model.2}")
  if rust.1.isNone then
    IO.FS.writeBinFile p ⟨rust.2.toArray⟩
    let (m, back) ← csvRead p.toString cols
    let rows := fun (es : List (USize × Enc)) => said (do fieldsOf cols n (← raws cols es))
    unless m.toNat = n ∧ decide (rows back = rows es) do
      throw (IO.userError s!"csvRead of what csvWrite {names cols} wrote on {p}: {m} rows, not the rows written")

/-- Each case at one path; then a directory as the path, and a path whose parent directories are missing. -/
def runWrites : IO Unit := do
  let (h, p) ← IO.FS.createTempFile
  h.flush
  let cases := writes.flatMap (fun (c, n, ws) => (encs c ws).map ((c, n, ·))) ++ others
  for (c, n, es) in cases do writeAgrees p c n es
  IO.FS.removeFile p
  let d : System.FilePath := p.toString ++ ".d"
  let one := [((1 : USize), Kernel.wordsFoR #[1]), (1, Kernel.wordsFoR #[120])]
  IO.FS.createDirAll d
  writeAgrees d ab 1 one
  writeAgrees (d / "a" / "x.csv") ab 1 one
  IO.FS.removeDirAll d

/-- info: csvWrite agrees with its body on every case -/
#guard_msgs in
#eval do runWrites; IO.println "csvWrite agrees with its body on every case"

end Rel.Db.CsvTest
