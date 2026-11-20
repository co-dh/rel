import Rel.Kernel.Db.Csv

/-! The CSV case table (IO design C.5): the model `csvWords`/`csvText` on every row of C.3, every rule of C.2 and every
refusal of C.4, each by `decide +kernel`. The atoms' cases are one `match` over `QAtomicType`, so a new atom has no
case until one is written, and `atom_cases` is proved constructor by constructor. Step I6 adds the extern beside each
case (`csvRead` on the same bytes gives the same answer). -/

namespace Rel.Db.CsvTest
open Rel Rel.Db Rel.Db.Csv

/-- An answer in a type with decidable equality. -/
def said {α : Type} : Except String α → String ⊕ α
  | .ok a => .inr a
  | .error e => .inl e

/-- The one-column file `x` with the data records `rs`. -/
def one (rs : String) : List UInt8 := bytes s!"x\n{rs}"

/-- Each atom's case: a text read, its word, the text the writer gives for the word, and a text refused. None at
    `sym` and `general`, which the schema refuses (`sym_general`). -/
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

/-- `sym` and `general` columns are refused before any byte is read, by reader and writer. -/
example : said (csvWords [("s", .sym, [])] []) =
    .inl "column 's' is a symbol column, which waits for the own-format sym writer (D.9 step 6)" := by decide +kernel
example : said (csvText [("g", .general, [])] 0 [#[]]) =
    .inl "column 'g' is a general column, which the own format does not hold" := by decide +kernel
example : said (csvWords [] (bytes "\n")) =
    .inl "the schema has no column, and a CSV record has at least one field" := by decide +kernel

/-! ### The epoch, 1970-01-01 (owner, question F.3: N) -/

example : said (csvWords [("d", .date, [])] (bytes "d\n1969-12-31\n1970-01-01\n1970-01-02\n")) =
    .inr (3, [#[0xffffffff, 0, 1]]) := by decide +kernel
example : said (csvWords [("t", .datetime, [])]
    (bytes "t\n1969-12-31D23:59:59.999999999\n1970-01-01D00:00:00\n1970-01-01D00:00:00.000000001\n")) =
    .inr (3, [#[0xffffffffffffffff, 0, 1]]) := by decide +kernel
example : said (csvWords [("d", .date, [])] (bytes "d\n0001-01-01\n9999-12-31\n2000-02-29\n")) =
    .inr (3, [#[4294248134, 2932896, 11016]]) := by decide +kernel
/-- 10000-01-01 is a word of `date` with no text (years 0001–9999). -/
example : said (csvText [("d", .date, [])] 1 [#[2932897]]) =
    .inl "row 0, column 'd': the word 2932897 has no text as date: YYYY-MM-DD in years 0001-9999" := by decide +kernel
example : said (csvWords [("t", .datetime, [])] (bytes "t\n2262-04-12D00:00:00\n")) =
    .inl "row 0 (line 2), column 't': expected datetime: YYYY-MM-DDDhh:mm:ss, up to 9 fraction digits, within i64 nanoseconds of 1970-01-01, found '2262-04-12D00:00:00'" := by
  decide +kernel

/-! ### Floats -/

/-- Shortest text, next to a power of two and at both ends of the range; the exponent form outside `[1e-5, 1e17)`. -/
example : ([0x3ff0000000000000, 0x3fefffffffffffff, 0x4340000000000000, 0x0010000000000000, 1, 0x7fefffffffffffff,
    0x3ee4f8b588e368f1, 0x3ee4f8b588e368f0, 0x4376345785d8a000, 0xc00c000000000000, 0x7ff0000000000000,
    0xfff0000000000000].map (fmtFloat 52 11)) =
    ["1", "0.9999999999999999", "9007199254740992", "2.2250738585072014e-308", "5e-324", "1.7976931348623157e308",
     "0.00001", "9.999999999999999e-6", "1e17", "-3.5", "0w", "-0w"].map (some ∘ bytes) := by
  decide +kernel
/-- Ties to even; a zero of either sign reads as `+0`; underflow to `+0`; beyond the largest finite value refused. -/
example : (["9007199254740993", "-0", "-0.0e5", "2.4e-324", "2.5e-324", "1e-99999", "1.7976931348623158e308",
    "1.7976931348623159e308", "1e99999", "1E+2", ".5", "+1", "1e", "0w", "-0w"].map fun s => readFloat 52 11 (bytes s)) =
    [some 0x4340000000000000, some 0, some 0, some 0, some 1, some 0, some 0x7fefffffffffffff, none, none,
     some 0x4059000000000000, none, none, none, some 0x7ff0000000000000, some 0xfff0000000000000] := by
  decide +kernel
/-- A NaN and `-0` have no text: the column is not canonical (ruling 6). -/
example : said (csvText [("f", .f64, [])] 2 [#[0, 0x8000000000000000]]) =
    .inl "row 1, column 'f': the word 9223372036854775808 has no text as f64: a finite decimal, 0w or -0w" := by
  decide +kernel
example : said (csvText [("f", .f32, [])] 1 [#[0x7fc00000]]) =
    .inl "row 0, column 'f': the word 2143289344 has no text as f32: a finite decimal, 0w or -0w" := by decide +kernel

/-! ### Named elements -/

def kcols : CsvCols := [("k", .u8, ["A", "B,x", "C\"D"])]

example : said (csvWords kcols (bytes "k\nA\n\"B,x\"\n\"C\"\"D\"\n")) = .inr (3, [#[0, 1, 2]]) := by decide +kernel
example : said (csvText kcols 3 [#[0, 1, 2]]) = .inr (bytes "k\nA\n\"B,x\"\n\"C\"\"D\"\n") := by decide +kernel
example : said (csvWords kcols (bytes "k\nB\n")) =
    .inl "row 0 (line 2), column 'k': expected one of A, B,x, C\"D, found 'B'" := by decide +kernel
example : said (csvText kcols 1 [#[3]]) =
    .inl "row 0, column 'k': the word 3 has no text as one of A, B,x, C\"D" := by decide +kernel

/-! ### Records (C.2) -/

def ab : CsvCols := [("a", .i64, []), ("b", .char, [])]

/-- `\r\n` and `\n` give the same words, the last record with or without its end; a quoted field holds `,` `"` and
    both record ends. -/
example : said (csvWords ab (bytes "a,b\r\n1,x\r\n2,\",\"\r\n")) = .inr (2, [#[1, 2], #[120, 44]]) := by decide +kernel
example : said (csvWords ab (bytes "a,b\n1,x\n2,\",\"")) = .inr (2, [#[1, 2], #[120, 44]]) := by decide +kernel
example : said (csvWords ab (bytes "a,\"b\"\r\n\"1\",\"\n\"\n2,\"\r\"\n")) = .inr (2, [#[1, 2], #[10, 13]]) := by
  decide +kernel
example : said (csvText ab 2 [#[1, 2], #[10, 13]]) = .inr (bytes "a,b\n1,\"\n\"\n2,\"\r\"\n") := by decide +kernel
/-- No record at all: the header is missing. A byte-order mark is not skipped. -/
example : said (csvWords ab []) = .inl "line 1: the header has 0 fields, the schema [a, b] has 2" := by decide +kernel
example : said (csvWords ab (bytes "a,b\n")) = .inr (0, [#[], #[]]) := by decide +kernel
example : said (csvText ab 0 [#[], #[]]) = .inr (bytes "a,b\n") := by decide +kernel
example : said (csvWords ab ([0xef, 0xbb, 0xbf] ++ bytes "a,b\n")) =
    .inl "line 1: header field 0 is '\\xef\\xbb\\xbfa', the schema [a, b] has 'a'" := by decide +kernel
example : said (csvWords ab (bytes "a,c\n")) = .inl "line 1: header field 1 is 'c', the schema [a, b] has 'b'" := by
  decide +kernel
example : said (csvWords ab (bytes "a,b,c\n")) = .inl "line 1: the header has 3 fields, the schema [a, b] has 2" := by
  decide +kernel
/-- The refusals of C.4, each at its line: a line after a quoted `\n` counts it. -/
example : said (csvWords ab (bytes "a,b\n1,\"\n\"\n2\n")) = .inl "row 1 (line 4): 1 fields, the schema [a, b] has 2" := by
  decide +kernel
example : said (csvWords ab (bytes "a,b\n1,x,\n")) = .inl "row 0 (line 2): 3 fields, the schema [a, b] has 2" := by
  decide +kernel
example : said (csvWords ab (bytes "a,b\n,x\n")) =
    .inl "row 0 (line 2), column 'a': expected i64: an integer from -9223372036854775808 to 9223372036854775807, found ''" := by
  decide +kernel
example : said (csvWords ab (bytes "a,b\n1,x\"y\n")) = .inl "line 2: a '\"' inside an unquoted field" := by decide +kernel
example : said (csvWords ab (bytes "a,b\n1,\"x\n")) = .inl "a quoted field opened at line 2 is not closed" := by
  decide +kernel
example : said (csvWords ab (bytes "a,b\n1,\"x\"y\n")) =
    .inl "line 2: after a closing '\"' comes 'y', not ',' or a record end" := by decide +kernel
example : said (csvWords ab (bytes "a,b\n1,\"x\"\rx\n")) =
    .inl "line 2: after a closing '\"' comes '\\x0d' with no '\\x0a' after it" := by decide +kernel
/-- The structure of the whole file is checked before the header, the header before the rows. -/
example : said (csvWords ab (bytes "a,c\n1,x\"\n")) = .inl "line 2: a '\"' inside an unquoted field" := by decide +kernel
example : said (csvWords ab (bytes "a,c\n1,xx\n")) = .inl "line 1: header field 1 is 'c', the schema [a, b] has 'b'" := by
  decide +kernel
/-- A long field is cut at 40 bytes in a refusal. -/
example : said (csvWords ab (bytes "a,b\n12345678901234567890123456789012345678901234567890,x\n")) =
    .inl "row 0 (line 2), column 'a': expected i64: an integer from -9223372036854775808 to 9223372036854775807, found '1234567890123456789012345678901234567890' (the first 40 of 50 bytes)" := by
  decide +kernel
/-- Columns of unequal length, or not one per schema column, are refused by the writer. -/
example : said (csvText ab 2 [#[1, 2], #[120]]) = .inl "column 'b' holds 1 words, not 2" := by decide +kernel
example : said (csvText ab 1 [#[1]]) = .inl "1 word columns, the schema [a, b] has 2" := by decide +kernel

end Rel.Db.CsvTest
