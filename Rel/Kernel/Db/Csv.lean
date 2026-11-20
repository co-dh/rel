import Rel.Kernel.Value

/-! CSV both ways, the model of the IO exports `qlean_csv_read` and `qlean_csv_write` (IO design C): `csvWords` reads
a file's bytes into each declared column's raw words, `csvText` writes them. One dialect, RFC 4180 and strict (C.2);
one text form per atom (C.3); one error shape (C.4). Every function recurses structurally over `List UInt8` or uses
fuel, so `decide +kernel` evaluates the case table (`Rel.Kernel.Db.CsvTest`); `Rel.KernelSpec.Csv` proves
`csvWords ∘ csvText` the identity on every input the writer accepts.

A word is the atom's raw word as `Enc.raw` reads it: a `w`-byte element as its `8 * w` bits zero-extended; `date` is
`i32` days and `datetime` `i64` nanoseconds since 1970-01-01 (owner, question F.3: N). -/

namespace Rel.Db

open Rel

/-- A column as the file names and types it: header name, atom, and the names of a named-element object in declared
order (empty for every other object). -/
abbrev CsvCols := List (String × QAtomicType × List String)

namespace Csv

/-- The UTF-8 bytes of `s`. -/
def bytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The physical line byte `p` of `all` is on, from 1. -/
def lineAt (all : List UInt8) (p : Nat) : Nat := (all.take p).count 10 + 1

/-- A lower-case hex digit's byte. -/
def hexd (d : Nat) : UInt8 := (if d < 10 then 48 + d else 87 + d).toUInt8

/-- A field as an error shows it, in quotes: printable ASCII as itself, every other byte `\xNN` (no encoding is
    interpreted, C.2); cut at 40 bytes, with its length when cut. -/
def shown (f : List UInt8) : String :=
  let s := String.join ((f.take 40).map fun c =>
    if 32 ≤ c.toNat ∧ c.toNat < 127 then (Char.ofNat c.toNat).toString
    else String.ofList ['\\', 'x', Char.ofNat (hexd (c.toNat / 16)).toNat, Char.ofNat (hexd (c.toNat % 16)).toNat])
  if f.length ≤ 40 then s!"'{s}'" else s!"'{s}' (the first 40 of {f.length} bytes)"

/-! ### Records -/

/-- Where the lexer is: in an unquoted field (`plain`, also the start of a field), in a quoted field opened at byte
    `o`, after its closing `"`, or after that and a `\r`. -/
inductive Lx | plain | quoted (o : Nat) | closed | closedCr
  deriving DecidableEq

/-- The records of `all` with the byte each starts at, from the rest `bs` at byte `p`: the field so far `fld`, the
    record's fields so far `row`, the record's first byte `st`, the records before `acc`. A record ends at `\n` or
    `\r\n`; the last one may lack it. A refusal names the line (C.4). -/
def lex (all : List UInt8) : List UInt8 → Lx → Nat → List UInt8 → List (List UInt8) → Nat →
    List (Nat × List (List UInt8)) → Except String (List (Nat × List (List UInt8)))
  | [], .quoted o, _, _, _, _, _ => .error s!"a quoted field opened at line {lineAt all o} is not closed"
  | [], .closedCr, p, _, _, _, _ =>
    .error s!"line {lineAt all p}: after a closing '\"' comes '\\x0d' with no '\\x0a' after it"
  | [], s, _, fld, row, st, acc =>
    if s = .plain ∧ fld = [] ∧ row = [] then .ok acc else .ok (acc ++ [(st, row ++ [fld])])
  | c :: r, .quoted o, p, fld, row, st, acc =>
    if c = 34 then match r with
      | d :: r' => if d = 34 then lex all r' (.quoted o) (p + 2) (fld ++ [34]) row st acc
        else lex all (d :: r') .closed (p + 1) fld row st acc
      | [] => lex all [] .closed (p + 1) fld row st acc
    else lex all r (.quoted o) (p + 1) (fld ++ [c]) row st acc
  | c :: r, .closedCr, p, fld, row, st, acc =>
    if c = 10 then lex all r .plain (p + 1) [] [] (p + 1) (acc ++ [(st, row ++ [fld])])
    else .error s!"line {lineAt all p}: after a closing '\"' comes '\\x0d' with no '\\x0a' after it"
  | c :: r, .closed, p, fld, row, st, acc =>
    if c = 44 then lex all r .plain (p + 1) [] (row ++ [fld]) st acc
    else if c = 10 then lex all r .plain (p + 1) [] [] (p + 1) (acc ++ [(st, row ++ [fld])])
    else if c = 13 then lex all r .closedCr (p + 1) fld row st acc
    else .error s!"line {lineAt all p}: after a closing '\"' comes {shown [c]}, not ',' or a record end"
  | c :: r, .plain, p, fld, row, st, acc =>
    if c = 44 then lex all r .plain (p + 1) [] (row ++ [fld]) st acc
    -- an unquoted field's last `\r` before `\n` is the `\r\n` record end, not data
    else if c = 10 then lex all r .plain (p + 1) [] [] (p + 1)
      (acc ++ [(st, row ++ [if fld.getLast? = some 13 then fld.dropLast else fld])])
    else if c = 34 then
      if fld = [] then lex all r (.quoted p) (p + 1) [] row st acc
      else .error s!"line {lineAt all p}: a '\"' inside an unquoted field"
    else lex all r .plain (p + 1) (fld ++ [c]) row st acc

/-- Whether a field is written quoted: it holds `,` `"` `\r` or `\n` (C.2). -/
def special (c : UInt8) : Bool := c = 44 || c = 34 || c = 13 || c = 10

/-- A byte inside a quoted field as written: `"` doubled. -/
def quote (c : UInt8) : List UInt8 := if c = 34 then [34, 34] else [c]

/-- A field as written. -/
def field (f : List UInt8) : List UInt8 := if f.any special then 34 :: f.flatMap quote ++ [34] else f

/-- A record's fields as written, without its end. -/
def record : List (List UInt8) → List UInt8
  | [] => []
  | [f] => field f
  | f :: fs => field f ++ 44 :: record fs

/-- Records as written, each ending in `\n`. -/
def records (rs : List (List (List UInt8))) : List UInt8 := rs.flatMap (record · ++ [10])

/-! ### Atoms -/

def isDig (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The number the decimal digits `ds` spell. -/
def natOf (ds : List UInt8) : Nat := ds.foldl (fun a d => 10 * a + (d.toNat - 48)) 0

/-- `n` in decimal, left-padded with `0` to `k` digits. -/
def pad (k n : Nat) : List UInt8 := let s := bytes (toString n); List.replicate (k - s.length) 48 ++ s

/-- An integer `-`? digits. -/
def intOf (f : List UInt8) : Option Int :=
  let (neg, d) := if f.head? = some 45 then (true, f.tail) else (false, f)
  if d ≠ [] ∧ d.all isDig then some (if neg then -(natOf d : Int) else natOf d) else none

/-- The float of `mb` fraction and `eb` exponent bits nearest `num / den > 0`, ties to even: its bits without the
    sign; none beyond the largest finite one. Exact integer arithmetic, so `decide` evaluates it. -/
def nearest (mb eb num den : Nat) : Option Nat :=
  let bias : Int := 2 ^ (eb - 1) - 1
  let emin : Int := 1 - bias - mb
  let emax : Int := 2 ^ eb - 2 - bias - mb
  let scaled (E : Int) : Nat × Nat := if 0 ≤ E then (num, den * 2 ^ E.toNat) else (num * 2 ^ (-E).toNat, den)
  -- `num / den / 2 ^ e0` lies in `(2 ^ (mb - 1), 2 ^ (mb + 1))`; one step down puts it in `[2 ^ mb, 2 ^ (mb + 1))`
  let e0 : Int := (num.log2 : Int) - den.log2 - mb
  let E := max (if (scaled e0).1 < (scaled e0).2 * 2 ^ mb then e0 - 1 else e0) emin
  let (a, b) := scaled E
  let q := a / b
  let M := if 2 * (a % b) > b ∨ (2 * (a % b) = b ∧ q % 2 = 1) then q + 1 else q
  let (M, E) := if M = 2 ^ (mb + 1) then (M / 2, E + 1) else (M, E)
  if E > emax then none else if M < 2 ^ mb then some M else some ((E - emin + 1).toNat * 2 ^ mb + (M - 2 ^ mb))

/-- A decimal `-`? digits (`.` digits)? (`e`/`E` sign? digits)?: its sign, digits `m`, exponent `e` (the value
    `m * 10 ^ e`) and digit count. -/
def decimal (f : List UInt8) : Option (Bool × Nat × Int × Nat) := do
  let (neg, f) := if f.head? = some 45 then (true, f.tail) else (false, f)
  let (ip, r) := f.span isDig
  if ip = [] then none
  let (fp, r) ← if r.head? = some 46 then
      (let (fp, r) := r.tail.span isDig; if fp = [] then none else some (fp, r)) else some ([], r)
  let x ← if r.head? = some 101 ∨ r.head? = some 69 then intOf (if r.tail.head? = some 43 then r.tail.tail else r.tail)
    else if r = [] then some 0 else none
  pure (neg, natOf (ip ++ fp), x - fp.length, ip.length + fp.length)

/-- A float of `mb` fraction and `eb` exponent bits read (C.3): a decimal to its nearest value, a zero to `+0`,
    `0w`/`-0w` the infinities; none beyond the largest finite value. The two shortcuts only skip a computation whose
    answer they give: below `10 ^ -400` every float rounds to zero, from `10 ^ 400` none is finite. -/
def readFloat (mb eb : Nat) (f : List UInt8) : Option UInt64 :=
  let inf := (2 ^ eb - 1) * 2 ^ mb
  if f = bytes "0w" then some inf.toUInt64 else if f = bytes "-0w" then some (2 ^ (mb + eb) + inf).toUInt64 else do
  let (neg, m, e, L) ← decimal f
  if m = 0 ∨ (L : Int) + e ≤ -400 then some 0 else if 400 ≤ e then none else
  let b ← nearest mb eb (m * 10 ^ e.toNat) (10 ^ (-e).toNat)
  some (if neg ∧ b ≠ 0 then 2 ^ (mb + eb) + b else b).toUInt64

/-- `ge q`: the float `M * 2 ^ E` is at least `10 ^ q`. -/
def atLeast (M : Nat) (E q : Int) : Bool := 10 ^ q.toNat * 2 ^ (-E).toNat ≤ M * 2 ^ E.toNat * 10 ^ (-q).toNat

/-- `q` moved, at most `k` steps, to the `q` with `10 ^ q ≤ M * 2 ^ E < 10 ^ (q + 1)`. -/
def settle (M : Nat) (E : Int) : Nat → Int → Int
  | 0, q => q
  | k + 1, q => if !atLeast M E q then settle M E k (q - 1) else if atLeast M E (q + 1) then settle M E k (q + 1) else q

/-- `(d, p)` with the trailing zeros of `d` moved into `p`. -/
def strip : Nat → Nat × Int → Nat × Int
  | 0, x => x
  | k + 1, (d, p) => if d ≠ 0 ∧ d % 10 = 0 then strip k (d / 10, p + 1) else (d, p)

/-- The decimal `d * 10 ^ p` as written (C.3): plain for `1e-5 ≤ |v| < 1e17`, else `d.ddde±x`. -/
def sci (d : Nat) (p : Int) : List UInt8 :=
  let s := bytes (toString d)
  let x : Int := s.length - 1 + p
  if -5 ≤ x ∧ x < 17 then
    if 0 ≤ p then s ++ List.replicate p.toNat 48
    else if 0 < s.length + p then s.take (s.length + p).toNat ++ 46 :: s.drop (s.length + p).toNat
    else bytes "0." ++ List.replicate (-(s.length + p)).toNat 48 ++ s
  else s.take 1 ++ (if 1 < s.length then 46 :: s.drop 1 else []) ++ 101 :: bytes (toString x)

/-- A float word of `mb` fraction and `eb` exponent bits written (C.3): the shortest decimal whose nearest float is the
    word (of `k ≤ 17` digits; the nearer of the two `k`-digit neighbours, ties to the even one), `0w`, `-0w`; none at a
    NaN. A `-0` is written `0`, which `readFloat` reads as `+0`, so `cell` refuses it. -/
def fmtFloat (mb eb : Nat) (w : UInt64) : Option (List UInt8) :=
  let x := w.toNat
  let neg := x / 2 ^ (mb + eb) % 2 = 1
  let (ex, fr) := (x / 2 ^ mb % 2 ^ eb, x % 2 ^ mb)
  let sign (s : List UInt8) := if neg then 45 :: s else s
  let emin : Int := 2 - 2 ^ (eb - 1) - mb
  let mag := ex * 2 ^ mb + fr
  if ex = 2 ^ eb - 1 then (if fr = 0 then some (sign (bytes "0w")) else none)
  else if mag = 0 then some (bytes "0") else
  let (M, E) : Nat × Int := if ex = 0 then (fr, emin) else (fr + 2 ^ mb, ex - 1 + emin)
  let q := settle M E 4 (((M.log2 : Int) + E) * 30103 / 100000)
  let back (d : Nat) (p : Int) := d ≠ 0 ∧ nearest mb eb (d * 10 ^ p.toNat) (10 ^ (-p).toNat) = some mag
  let pick (k : Nat) : Option (Nat × Int) :=
    let p := q - k + 1
    let (a, b) := (M * 2 ^ E.toNat * 10 ^ (-p).toNat, 2 ^ (-E).toNat * 10 ^ p.toNat)
    let (lo, r) := (a / b, a % b)
    let hi := if r = 0 then lo else lo + 1
    if back lo p ∧ back hi p then
      some (if r < b - r ∨ (r = b - r ∧ lo % 2 = 0) then lo else hi, p)
    else if back lo p then some (lo, p) else if back hi p then some (hi, p) else none
  ((List.range 17).findSome? (pick ·.succ)).map fun dp => let (d, p) := strip 20 dp; sign (sci d p)

/-- Days since 1970-01-01 of a proleptic Gregorian day (H. Hinnant's `days_from_civil`). -/
def daysFrom (y m d : Nat) : Int :=
  let y : Int := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let doy : Int := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468

/-- The day `z` days after 1970-01-01 as year, month, day (`civil_from_days`). -/
def civil (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := (doy - (153 * mp + 2) / 5 + 1).toNat
  let m := if mp < 10 then (mp + 3).toNat else (mp - 9).toNat
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

/-- The days of month `m` of year `y`. -/
def mdays (y m : Nat) : Nat :=
  if m = 2 then (if y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31

/-- `YYYY-MM-DD`, a valid day of years 0001–9999, as days since 1970-01-01. -/
def ymd (f : List UInt8) : Option Int :=
  match f with
  | [a, b, c, d, s, e, g, s', h, i] =>
    let (y, m, dd) := (natOf [a, b, c, d], natOf [e, g], natOf [h, i])
    if s = 45 ∧ s' = 45 ∧ [a, b, c, d, e, g, h, i].all isDig ∧ 1 ≤ y ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ dd ∧ dd ≤ mdays y m
    then some (daysFrom y m dd) else none
  | _ => none

/-- Nothing, or `.` and 1–9 digits: nanoseconds. -/
def frac : List UInt8 → Option Nat
  | [] => some 0
  | c :: fr => if c = 46 ∧ fr ≠ [] ∧ fr.length ≤ 9 ∧ fr.all isDig then some (natOf fr * 10 ^ (9 - fr.length)) else none

/-- `YYYY-MM-DDDhh:mm:ss` with an optional `.` and 1–9 fraction digits, as nanoseconds since 1970-01-01 in `i64`. -/
def stamp (f : List UInt8) : Option Int :=
  match ymd (f.take 10), f.drop 10 with
  | some d, t :: h1 :: h2 :: c1 :: m1 :: m2 :: c2 :: s1 :: s2 :: r =>
    let (hh, mm, ss) := (natOf [h1, h2], natOf [m1, m2], natOf [s1, s2])
    if t = 68 ∧ c1 = 58 ∧ c2 = 58 ∧ [h1, h2, m1, m2, s1, s2].all isDig ∧ hh < 24 ∧ mm < 60 ∧ ss < 60 then
      (frac r).bind fun ns =>
        let x : Int := (((d * 24 + hh) * 60 + mm) * 60 + ss) * 1000000000 + ns
        if -2 ^ 63 ≤ x ∧ x < 2 ^ 63 then some x else none
    else none
  | _, _ => none

/-- The value of a hex digit's byte. -/
def hexv (c : UInt8) : Option Nat :=
  if isDig c then some (c.toNat - 48) else if 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55) else none

/-- The integer `x` as a word of `w` bytes, two's complement. -/
def wordOf (w : Nat) (x : Int) : UInt64 := (x % 2 ^ (8 * w)).toNat.toUInt64

/-- A word of `w` bytes read as a signed integer. -/
def signed (w : Nat) (x : UInt64) : Int :=
  let v := x.toNat % 2 ^ (8 * w); if v < 2 ^ (8 * w - 1) then v else (v : Int) - 2 ^ (8 * w)

/-- A field read at an atom (C.3, column "read"); none where it is no text of the atom. -/
def readAtom : QAtomicType → List UInt8 → Option UInt64
  | .u1, f => if f = [48] then some 0 else if f = [49] then some 1 else none
  | .u8, [a, b] => do pure (16 * (← hexv a) + (← hexv b)).toUInt64
  | .u8, _ => none
  | .char, [c] => some c.toUInt64
  | .char, _ => none
  | .f32, f => readFloat 23 8 f
  | .f64, f => readFloat 52 11 f
  | .date, f => (ymd f).map (wordOf 4)
  | .datetime, f => (stamp f).map (wordOf 8)
  | .sym, _ | .general, _ => none
  | t, f => do
    let w ← t.width
    let x ← intOf f
    if -2 ^ (8 * w - 1) ≤ x ∧ x < 2 ^ (8 * w - 1) then some (wordOf w x) else none

/-- A word written at an atom (C.3, column "written"), before `cell` checks that it reads back. -/
def fmtAtom : QAtomicType → UInt64 → Option (List UInt8)
  | .u1, w => some (if w = 0 then [48] else [49])
  | .u8, w => some [hexd (w.toNat / 16 % 16), hexd (w.toNat % 16)]
  | .char, w => some [w.toUInt8]
  | .f32, w => fmtFloat 23 8 w
  | .f64, w => fmtFloat 52 11 w
  | .date, w => let (y, m, d) := civil (signed 4 w); some (pad 4 y.toNat ++ 45 :: pad 2 m ++ 45 :: pad 2 d)
  | .datetime, w =>
    let x := signed 8 w
    let (y, m, d) := civil (x / 86400000000000)
    let r := (x % 86400000000000).toNat
    some (pad 4 y.toNat ++ 45 :: pad 2 m ++ 45 :: pad 2 d ++ 68 :: pad 2 (r / 3600000000000) ++ 58 ::
      pad 2 (r / 60000000000 % 60) ++ 58 :: pad 2 (r / 1000000000 % 60) ++ 46 :: pad 9 (r % 1000000000))
  | .sym, _ | .general, _ => none
  | t, w => t.width.map fun k => bytes (toString (signed k w))

/-- A column's field read: one of its names (the word is the name's index), or else a text of its atom. -/
def readCell : QAtomicType × List String → List UInt8 → Option UInt64
  | (_, n :: ns), f => ((n :: ns).findIdx? (bytes · == f)).map (·.toUInt64)
  | (t, []), f => readAtom t f

/-- A column's word written: its name or its atom's text, and only if that reads back as the word. This one check is
    each refusal of C.6 — a NaN or `-0`, a date outside years 0001–9999, a word that is no index of the names, a
    word wider than its atom — and it makes the round trip hold cell by cell. -/
def cell (c : QAtomicType × List String) (w : UInt64) : Option (List UInt8) :=
  (match c.2 with | [] => fmtAtom c.1 w | ns => (ns[w.toNat]?).map bytes).bind
    fun s => if readCell c s = some w then some s else none

/-- What a column's field must be, as an error names it. -/
def form : QAtomicType → List String → String
  | _, n :: ns => s!"one of {", ".intercalate (n :: ns)}"
  | .u1, [] => "u1: 0 or 1"
  | .u8, [] => "u8: two hex digits"
  | .char, [] => "char: one byte"
  | .i8, [] => "i8: an integer from -128 to 127"
  | .i16, [] => "i16: an integer from -32768 to 32767"
  | .i32, [] => "i32: an integer from -2147483648 to 2147483647"
  | .i64, [] => "i64: an integer from -9223372036854775808 to 9223372036854775807"
  | .f32, [] => "f32: a finite decimal, 0w or -0w"
  | .f64, [] => "f64: a finite decimal, 0w or -0w"
  | .date, [] => "date: YYYY-MM-DD in years 0001-9999"
  | .datetime, [] => "datetime: YYYY-MM-DDDhh:mm:ss, up to 9 fraction digits, within i64 nanoseconds of 1970-01-01"
  | .sym, [] | .general, [] => "no text"

/-! ### Files -/

/-- The schema's names as the errors list them. -/
def names (cols : CsvCols) : String := s!"[{", ".intercalate (cols.map (·.1))}]"

/-- The refusals of a schema, before any byte: no column, or a column CSV does not hold (C.3). -/
def schema (cols : CsvCols) : Except String Unit :=
  if cols = [] then .error "the schema has no column, and a CSV record has at least one field" else
  cols.forM fun (c, t, _) =>
    if t = .sym then .error s!"column '{c}' is a symbol column, which waits for the own-format sym writer (D.9 step 6)"
    else if t = .general then .error s!"column '{c}' is a general column, which the own format does not hold"
    else .ok ()

/-- The header: its fields are the schema's names, in order. Refused at the first field that differs, else (one is a
    prefix of the other) by the field count. -/
def header (cols : CsvCols) (h : List (List UInt8)) : Except String Unit :=
  if h = cols.map (bytes ·.1) then .ok () else
  match (cols.zip h).zipIdx.find? fun (((c, _), f), _) => f ≠ bytes c with
  | some (((c, _), f), j) => .error s!"line 1: header field {j} is {shown f}, the schema {names cols} has '{c}'"
  | none => .error s!"line 1: the header has {h.length} fields, the schema {names cols} has {cols.length}"

/-- Data record `r` starting at byte `p`: its words, one per column. -/
def row (cols : CsvCols) (all : List UInt8) (r p : Nat) (fs : List (List UInt8)) : Except String (List UInt64) :=
  if fs.length ≠ cols.length then
    .error s!"row {r} (line {lineAt all p}): {fs.length} fields, the schema {names cols} has {cols.length}"
  else (cols.zip fs).mapM fun ((c, t, ns), f) => match readCell (t, ns) f with
    | some w => .ok w
    | none => .error s!"row {r} (line {lineAt all p}), column '{c}': expected {form t ns}, found {shown f}"

/-- The data records from row `r`: each one's words. -/
def rows (cols : CsvCols) (all : List UInt8) : Nat → List (Nat × List (List UInt8)) → Except String (List (List UInt64))
  | _, [] => .ok []
  | r, (p, fs) :: rest => do pure ((← row cols all r p fs) :: (← rows cols all (r + 1) rest))

end Csv

open Csv in
/-- The reader's model (C.1): the file's bytes read under the schema `cols`, as the row count and each column's words,
    or the first refusal in C.4's order — the schema, the records (quotes), the header, then the first failing row:
    its field count, then its first failing column. -/
def csvWords (cols : CsvCols) (b : List UInt8) : Except String (Nat × List (Array UInt64)) := do
  schema cols
  let recs ← lex b b .plain 0 [] [] 0 []
  header cols (recs.head?.map (·.2) |>.getD [])
  let ws ← rows cols b 0 recs.tail
  pure (recs.tail.length, (List.range cols.length).map fun c => (ws.map (·.getD c 0)).toArray)

open Csv in
/-- The writer's model (C.1): `n` rows of the columns' words `ws` as a file, the header first, each record ending in
    `\n`; or the first word with no text (`cell`), named by row and column. -/
def csvText (cols : CsvCols) (n : Nat) (ws : List (Array UInt64)) : Except String (List UInt8) := do
  schema cols
  if ws.length ≠ cols.length then .error s!"{ws.length} word columns, the schema {names cols} has {cols.length}"
  (cols.zip ws).forM fun ((c, _), a) => if a.size = n then .ok () else .error s!"column '{c}' holds {a.size} words, not {n}"
  let rs ← (List.range n).mapM fun r => (cols.zip ws).mapM fun ((c, t, ns), a) => match cell (t, ns) (a.getD r 0) with
    | some s => .ok s
    | none => .error s!"row {r}, column '{c}': the word {a.getD r 0} has no text as {form t ns}"
  pure (records (cols.map (bytes ·.1) :: rs))

end Rel.Db
