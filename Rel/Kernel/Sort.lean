import Rel.Kernel.Need
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Kernel.Sort` the Rel kernels reach; `Rel.Kernel.Sort` imports it. -/


open Rel.Ext
namespace Rel.Kernel.Order

open Rel.Kernel.Scan (Kind)

/-- q's order on a `float`'s bits, as an unsigned key. Three folds and a monotone map:

* any NaN answers `0`, which is q's null sorting below everything and every NaN equal to every
  other. `0` is not reachable otherwise — the only `b` with `~~~b = 0` is `0xffffffffffffffff`,
  which is itself a NaN;
* `-0.0` answers `+0.0`'s key;
* a negative answers `~~~b`, which reverses the magnitude ordering IEEE gives it, and a non-negative
  answers `b` with the sign bit set, which lifts every positive above every negative. -/
def rank64 (b : UInt64) : UInt64 :=
  if Bits.f64IsNaN b then 0
  else if b == 0x8000000000000000 then 0x8000000000000000
  else if b >>> 63 == 1 then ~~~b
  else b ||| 0x8000000000000000

/-- `rank64` at four bytes. Written out rather than widening through `Float32.toFloat`, which is a
native function and would stop `decide` on every proposition that mentions a `real`. -/
def rank32 (b : UInt32) : UInt32 :=
  if Bits.f32IsNaN b then 0
  else if b == 0x80000000 then 0x80000000
  else if b >>> 31 == 1 then ~~~b
  else b ||| 0x80000000

/-- The unsigned key these raw bits sort by, at each layout. The integral widths flip their sign bit
*within their own width*, which turns q's two's-complement payload order into unsigned order and
puts `0N` — the minimum payload — at key `0`; `byte` and `char` are q's unsigned types and are
already their own key; the float widths rank. A `.bit` is `0` or `1` and needs neither. -/
def rank (k : Kind) (v : UInt64) : UInt64 :=
  match k with
  | .bit | .u8 | .c8 => v
  | .i16 => v ^^^ 0x8000
  | .i32 => v ^^^ 0x80000000
  | .i64 => v ^^^ 0x8000000000000000
  | .f32 => (rank32 v.toUInt32).toUInt64
  | .f64 => rank64 v

/-- Element `i`'s key. `Kind.bitsAt` is the one place that says what element `i`'s raw bits are, so
a boolean payload and a dense one are read here by the same expression they are read by everywhere
else. -/
def keyAt (k : Kind) (b : ByteArray) (i : Nat) : UInt64 := rank k (k.bitsAt b i)

/-- Indices as the little-endian `Int64`s every answer here is a vector of. -/
def indices (is : List Nat) : ByteArray :=
  is.foldl (init := ByteArray.empty) fun acc i => Column.pushBits acc (Int64.ofNat i).toUInt64 8

/-- q's `<` and `>` — `iasc` and `idesc` — over a fixed-width or boolean payload: the indices
`0 .. n-1` ordered by key, ties left in the order they came in. `List.mergeSort` is stable and a
`≤` test makes a tie satisfy the comparison both ways round, so the specification says "stable"
without a second clause; the descending case compares the keys the other way round for the same
reason, which is q's `idesc 9 1 9 1 9` = `0 2 4 1 3` and not the reverse of its `iasc`.

`n` is clamped to what the payload holds, as `Scan.scan` clamps it and for its reason: three bytes
hold between 17 and 24 booleans, so the size does not determine the count, and reading past the
array is the one failure worse than a wrong answer. -/
@[extern "qlean_sort_grade"]
def grade (k : Kind) (desc : Bool) (n : USize) (b : @& ByteArray) : ByteArray :=
  let m := min n.toNat (k.avail b)
  indices ((List.range m).mergeSort fun i j =>
    if desc then keyAt k b j ≤ keyAt k b i else keyAt k b i ≤ keyAt k b j)

/-- The inverse of a permutation of `0 .. m-1` held as little-endian `Int64`s: element `i` is where `i`
stands in `p`, and `m` where it stands nowhere. `~/q/q.k` line 12 builds `rank` as `<<x`, and the
grade of a permutation is its inverse, so the second grade is one scatter: grading the eight-byte
permutation again was 52ms of `rank` on 20M booleans, twice the first grade. -/
@[extern "qlean_sort_invert"]
def invert (p : @& ByteArray) : ByteArray :=
  let m := p.size / 8
  indices ((List.range m).map fun i => (List.range m).findIdx fun j => (Column.bitsAt p (8 * j) 8).toNat == i)

/-- `grade` off the encoded form, which is the same fact `ascendingFoR` rests on carried one step
further: a block's base is the same for all of it, so `base + residual` is the element and biasing it
is the key. Nothing is decoded, where `Column.bytesOf` wrote eight megabytes for a pass that only
ever wanted a key out of them. -/
@[extern "qlean_sort_grade_foR"]
def gradeFoR (k : Kind) (desc : Bool) (n : USize) (metadata pack : @& ByteArray) : ByteArray :=
  grade k desc n (Coc.decode k.width.toUSize metadata pack n)

/-- `grade` over an id payload at a lane of `w` bits (`Column.packIds`' widths), keyed by the id itself:
codes for a few classes stay packed at 1, 2 or 4 bits and are graded where they lie, where a caller
widening them to a byte first wrote and read a byte an element. The C is `grade`'s counting sort with
a `2 ^ w` table up to sixteen bits. -/
@[extern "qlean_sort_grade_lane"]
def gradeLane (desc : Bool) (n w : USize) (ids : @& ByteArray) : ByteArray :=
  indices ((List.range (Column.idsCap ids w.toNat n.toNat)).mergeSort fun i j =>
    if desc then Column.idAt ids w.toNat j ≤ Column.idAt ids w.toNat i
    else Column.idAt ids w.toNat i ≤ Column.idAt ids w.toNat j)

/-- `~/q/q.k` line 12's `rank:{<<x}` over a fixed-width or boolean payload: the grade graded again,
which is the grade inverted. The C builds the grade only where the key range takes the radix: a range
the counting sort serves has every element's rank in the histogram's prefix sums, written in element
order where the grade is a scatter and its inversion a second one. -/
@[extern "qlean_sort_ranks"]
def ranks (k : Kind) (n : USize) (b : @& ByteArray) : ByteArray := invert (grade k false n b)

/-- `ranks` off the encoded form, `gradeFoR`'s reason again. -/
@[extern "qlean_sort_ranks_foR"]
def ranksFoR (k : Kind) (n : USize) (metadata pack : @& ByteArray) : ByteArray :=
  ranks k n (Coc.decode k.width.toUSize metadata pack n)

/-- The indices at which a key occurs for the first time, in the order they occur — the gather
`distinct` answers with and the key order `group` answers in. -/
def firstsBy {α : Type} [BEq α] (m : Nat) (key : Nat → α) : List Nat :=
  (List.range m).filter fun i => (List.range i).all fun j => key j != key i

/-- Each of the `m` indices' group under `key`, numbered in first-occurrence order, and `firstsBy`:
what `groupIds` answers, over any key so that a pair of columns is the same statement. -/
def idsBy {α : Type} [BEq α] (m : Nat) (key : Nat → α) : ByteArray × ByteArray :=
  let fs := firstsBy m key
  (Column.packIds (Column.idWidthOf fs.length) m (fun i => fs.findIdx (key · == key i)), indices fs)

/-- The group each element falls in, numbered in first-occurrence order, against `firsts` — the same
pass `group` makes, stopping before the buckets. That is what a grouped reduction wants:
`Kernel.overGroups` accumulates straight from the ids, where the index vectors are a row number
written per element and a gather that reads every one of them back. Measured at a million longs in a
thousand groups, the grouping itself is 372us against `buckets`' 610 and the gather's 464.

The ids are packed at `Column.idWidthOf ng` bits, `ng` being the second payload's count — an interned
column's id layout, read by `Column.idAt` — because every consumer reads an id per row and at 100
groups a byte holds what a `long` did; nothing stores the width, the count derives it. -/
@[extern "qlean_sort_group_ids"]
def groupIds (k : Kind) (n : USize) (b : @& ByteArray) : ByteArray × ByteArray :=
  idsBy (min n.toNat (k.avail b)) (keyAt k b)

/-- `groupIds` on the pair `(a[i], b[i])`: the joint dense code of two columns, either kind in either
slot. One kernel because the composition — `groupIds` of each, `p·N + q`, `groupIds` again — reads and
writes three id payloads where the C makes the pair one key and numbers it in one table. -/
@[extern "qlean_sort_group_ids_pair"]
def groupIdsPair (k₁ k₂ : Kind) (n : USize) (a b : @& ByteArray) : ByteArray × ByteArray :=
  idsBy (min n.toNat (min (k₁.avail a) (k₂.avail b))) fun i => (keyAt k₁ a i, keyAt k₂ b i)

/-- `groupIdsPair` on two id payloads — `a` at `wa` bits and `b` at `wb`, an interned column's or
`groupIds`' own, either any lane `Column.laneWidth` answers. The C reads each id through `id_at`
where `keys_of` would read a column's element, so neither payload is widened to longs first. -/
@[extern "qlean_sort_group_ids_pair_ids"]
def groupIdsPairIds (wa wb n : USize) (a b : @& ByteArray) : ByteArray × ByteArray :=
  groupIdsPair .i64 .i64 n (idsOperand 8 wa a n) (idsOperand 8 wb b n)

@[extern "qlean_sort_group_ids_foR"]
def groupIdsFoR (k : Kind) (n : USize) (metadata pack : @& ByteArray) : ByteArray × ByteArray :=
  groupIds k n (Coc.decode k.width.toUSize metadata pack n)

/-- `groupIds` with a segment as the key: `o`'s `g + 1` long offsets cut `v`'s elements into `g`
segments, segment `j` being `v[o[j] .. o[j+1])`, and the answer is each segment's id as a long,
numbered by first occurrence. Segments are compared as sequences, so `1 2` and `2 1` get two ids.
An element is `w` bits (`0 .. 64`) read as `Column.resAt` reads a residual, the one reader of every
narrow layout: dense bytes at 8/16/32/64, a bitmap at 1, interned ids at their lane width, one Frame of
Reference block's residuals at its width. Empty where `w` passes 64 or the offsets do not ascend from
a non-negative start to at most `v`'s count, which the caller reads as a decline, as `segIds` does. -/
@[extern "qlean_sort_rank_slices"]
def rankSlices (w : USize) (v o : @& ByteArray) : ByteArray :=
  let off (j : Nat) : Int := (Column.bitsAt o (8 * j) 8).toInt64.toInt
  let g := o.size / 8 - 1
  let seg (j : Nat) : Array UInt64 := (Array.range ((off (j + 1)).toNat - (off j).toNat)).map fun t =>
    Column.resAt v 0 w.toNat ((off j).toNat + t)
  if 64 < w.toNat || o.size < 8 || off 0 < 0 || Column.idsCap v w.toNat (off g).toNat < off g ||
      (List.range g).any fun j => off (j + 1) < off j then
    .empty
  else ((Array.range g).foldl (init := (ByteArray.empty, (#[] : Array (Array UInt64)))) fun (ids, seen) j =>
    match seen.findIdx? (· == seg j) with
    | some k => (Column.pushBits ids (UInt64.ofNat k) 8, seen)
    | none => (Column.pushBits ids (UInt64.ofNat seen.size) 8, seen.push (seg j))).1

/-- How many elements name each group, which is what `count … by` answers. `group`'s offsets are
this histogram summed, so nothing new is being counted; it is a pass of its own because a query that
names no count never wants it — at a million rows it reads eight megabytes, 187us measured, against
the 190 a whole grouped sum takes. -/
@[extern "qlean_sort_group_sizes"]
def groupSizes (ng w n : USize) (gid : @& ByteArray) : ByteArray :=
  indices ((List.range ng.toNat).map fun g =>
    (List.range (Column.idsCap gid w.toNat n.toNat)).countP fun i => Column.idAt gid w.toNat i == g)

/-- The first `n` of `w`-bit ids as `long`s, for the consumers whose next step is `long` arithmetic
or a `long` column — `pairIds`' `ids·k + ids'`, a join's key ids, `group` over the ids. -/
@[extern "qlean_sort_id_longs"]
def idLongs (n w : USize) (ids : @& ByteArray) : ByteArray :=
  indices ((List.range (Column.idsCap ids w.toNat n.toNat)).map (Column.idAt ids w.toNat ·))

/-- `grade` over a symbol column. The stability argument is `grade`'s: `!= .gt` is the `≤` a stable
merge needs, and a tie satisfies it both ways round. -/
@[extern "qlean_sort_grade_syms"]
def gradeSyms (desc : Bool) (blob : @& ByteArray) (offs : @& Array Nat) : ByteArray :=
  indices ((List.range (offs.size - 1)).mergeSort fun i j =>
    if desc then Column.symCmp (Column.symKey blob offs j) (Column.symKey blob offs i) != .gt
    else Column.symCmp (Column.symKey blob offs i) (Column.symKey blob offs j) != .gt)

/-- `firsts` over a symbol column. Equality is the bytes, so it is `Column.symCmp … = .eq` and not a second
statement of what two symbols being the same means. -/
def symFirsts (blob : ByteArray) (offs : Array Nat) : List Nat :=
  (List.range (offs.size - 1)).filter fun i =>
    (List.range i).all fun j => Column.symCmp (Column.symKey blob offs j) (Column.symKey blob offs i) != .eq

/-- The blob and offsets of these symbols, in `Column.syms` layout: each one's bytes followed by its
NUL, and the `g + 1` starts. -/
def symsAt (blob : ByteArray) (offs : Array Nat) (is : List Nat) : ByteArray × Array Nat :=
  ( is.foldl (init := ByteArray.empty) fun acc i => (acc ++ Column.symKey blob offs i).push 0
  , (is.foldl (init := (#[0], 0)) fun (o, pos) i =>
      (o.push (pos + (Column.symKey blob offs i).size + 1), pos + (Column.symKey blob offs i).size + 1)).1 )

/-- q's `<` and `>` over an interned column. The dictionary is ranked once and every element carries
its entry's rank as the integer key the grade orders — `gradeSyms`' own shape with the group pass
already made, the ids *being* the groups, so the symbols compared are `d` and not `n`.

Ids cannot carry the order themselves and that is measured: q orders symbols by unsigned bytes then
length, `` iasc `$("ab";"a";"aa";"") `` being `3 1 2 0` and `` asc `$("é";"e";"z") `` being
`` `e`z`é ``, which is not the order they were first seen in. So `asc` is two integer passes over a
rank, and not a grade of the ids. -/
@[extern "qlean_sort_grade_ids"]
def gradeIds (desc : Bool) (n : USize) (dict : @& ByteArray) (dof : @& Array Nat)
    (ids : @& ByteArray) : ByteArray :=
  let d := dof.size - 1
  let w := Column.idWidth dof
  -- the rank is a `Nat`, the entries below the id's symbol, as relk's `u64` one: a four-byte key wrapped past `2^31`
  -- entries. Equal symbols tie and an id past the dictionary (the empty symbol) ranks 0, as the kernel's do
  let rank (i : Nat) : Nat := (List.range d).countP fun j =>
    Column.symCmp (Column.symKey dict dof j) (Column.symKey dict dof (Column.idAt ids w i)) == .lt
  indices ((List.range n.toNat).mergeSort fun i j =>
    if desc then decide (rank j ≤ rank i) else decide (rank i ≤ rank j))

/-- The dictionary entry element `i` names: its id, and `d` for any id past the dictionary. Those
all denote the **one** empty symbol — `Column.symBytes` answers `(0, 0)` past its table — so they are
one value here and `distinct` answers it once. It is also what lets the C count into `d + 1` slots
instead of `2 ^ w` of them, which at a 300000-symbol dictionary is a table of four billion. -/
def idKey (d : Nat) (ids : ByteArray) (w i : Nat) : Nat := min (Column.idAt ids w i) d

/-- The indices at which a dictionary entry is named for the first time, in the order they occur. -/
def idFirsts (d n w : Nat) (ids : ByteArray) : List Nat :=
  (List.range n).filter fun i =>
    (List.range i).all fun j => idKey d ids w j != idKey d ids w i

/-- `groupIds` over an interned column: the group of every row and the row each group was first seen
at, which is what a grouped reduction accumulates straight from. -/
@[extern "qlean_sort_id_groups"]
def idGroups (d n w : USize) (ids : @& ByteArray) : ByteArray × ByteArray :=
  let fs := idFirsts d.toNat n.toNat w.toNat ids
  ( Column.packIds (Column.idWidthOf fs.length) n.toNat (fun i =>
      fs.findIdx (idKey d.toNat ids w.toNat · == idKey d.toNat ids w.toNat i))
  , indices fs )

/-- q's `distinct` over a symbol column, as the payload a `Column.syms` is made of. -/
@[extern "qlean_sort_distinct_syms"]
def distinctSyms (blob : @& ByteArray) (offs : @& Array Nat) : ByteArray × Array Nat :=
  symsAt blob offs (symFirsts blob offs)

/-- A symbol column interned: the distinct symbols in `syms` layout, and one id per element
indexing them, packed at `Column.idWidth` — the fields of `Column.enum`, whose docstring says why
the dictionary is the column's own and not a process-wide table.

The specification is the two kernels beside it, so there is one statement of what "the distinct
symbols" are and one of where a symbol is found: `distinctSyms` in first-occurrence order, and
`findSymScalar` against it. The C does both in the pass `sym_group` already makes — the group of an
element *is* its dictionary index, the groups being numbered in that same order. -/
@[extern "qlean_sort_intern_syms"]
def internSyms (blob : @& ByteArray) (offs : @& Array Nat) :
    ByteArray × Array Nat × ByteArray :=
  let (db, dof) := distinctSyms blob offs
  (db, dof, Column.packIds (Column.idWidth dof) (offs.size - 1) fun i =>
    (findSymScalar db dof (Column.symKey blob offs i)).toNat)

end Rel.Kernel.Order

namespace Rel.Kernel

open Rel.Kernel.Scan (Kind)
open Rel.Kernel.Order

/-- The layout a column of this type is ordered at. Every q type but the two that have no key of a
fixed width is here, `char` included — q orders it by its unsigned byte and the blank is not a null
to a comparison, which is `Eval.missing`'s split read from the ordering side. `symbol` has its own
three entry points. -/
def orderKind : QAtomicType → Option Kind
  | .boolean => some .bit
  | .byte | .char => some .u8
  | .short => some .i16
  | .int | .month | .date | .minute | .second | .time => some .i32
  | .long | .timestamp | .timespan => some .i64
  | .real => some .f32
  | .float | .datetime => some .f64
  | .symbol | .general => none

/-- `groupColumn`'s groups as a grouped reduction reads them: the group of every row, and the row
each group was first seen at, which is where its key lies. The key column itself is a gather of the
operand at those rows and is left to the caller, who has the *other* group columns to gather at the
same rows.

Every layout `findColumn` takes is claimed, so the ids are `x?x` renumbered densely by first
appearance: they span `[0, distinct)` where `x?x`'s positions span `[0, n)`. -/
def groupIdsColumn (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option (ByteArray × ByteArray) :=
  match t, e with
  -- interned: the groups are the ids' groups, an id being one symbol, exactly as `groupColumn` reads
  -- an `.enum`
  | .symbol, .enum _ dof ids => needSize (dof.size - 1) "groupIdsColumn: dictionary entries" (fun _ => none)
    fun nd => some (idGroups nd n (Column.idWidth dof).toUSize ids)
  -- a blob is interned first: its ids are already numbered by first appearance, and `idGroups` adds
  -- the first rows off a direct table
  | .symbol, .syms blob offs =>
    let (_, dof, ids) := internSyms blob offs
    needSize (dof.size - 1) "groupIdsColumn: dictionary entries" (fun _ => none)
      fun nd => some (idGroups nd n (Column.idWidth dof).toUSize ids)
  -- `dedup` reads a bitmap a bit an element at `Kind.bit`, so the bitmap is the payload as it lies
  | .boolean, .bits b => some (groupIds .bit n b)
  | t, e =>
    match orderKind t with
    | none => none
    | some k =>
      match e with
      -- a boolean `foR` is `u1`, every element 0 or 1, so its key is the `u8` one; `Kind.bit` reads only a bitmap
      | .foR md pk => some (groupIdsFoR (if k == .bit then .u8 else k) n md pk)
      | e => if k == .bit then none else (Enc.bytesOf t n e).map fun b => groupIds k n b

end Rel.Kernel

namespace Rel.Column


/-- The same column interned, and unchanged where it is not a symbol payload. `Column.blobOf` is the
other direction and the two are inverse on the symbols, which is the whole obligation: interning is a
choice of representation and owes nothing else, exactly as `Column.encode` owes only its round trip.

Here and not beside `Column.symsOf` for the reason `Column.encode` is here and not beside
`Column.ofAtoms`: the kernel that does the work is downstream of `QLean/Value.lean`, and the place a
column is *materialised* is `Eval.vectorOf`, which reaches both of these together.

**The order the arms land in decides whether this pays, and it nearly did not.** With only `distinct`,
`group`, `in` and `?` migrated, calling this from `Eval.vectorOf` lost 16M `1000#xs` 7µs→1035ms,
`xs=xs` 24ms→3.1s and `asc` 109ms→2.5s, because every verb still reaching `Column.blobOf` expands the
dictionary back to a blob. With `#`, `reverse`, `=`, `~`, the gather and the two symbol maps given
arms it wins every line: `reverse` 817ms→3.0, `hsym` 50→3.6, `lower` 35→3.7, `=` 24→6.2, `like`
21→5.9, `asc` 100→43. The maps are where the win is — they run on the *dictionary*, three entries
against sixteen million. -/
def intern (e : Ext.Enc X) : Ext.Enc X :=
  match e with
  | .syms blob offs =>
    let (db, dof, ids) := Rel.Kernel.Order.internSyms blob offs
    .enum db dof ids
  | e => e

end Rel.Column

namespace Rel.Kernel

end Rel.Kernel


namespace Rel.Kernel.Order

open Rel.Kernel.Scan (Kind)

end Rel.Kernel.Order

namespace Rel.Kernel

open Rel.Kernel.Scan (Kind)
open Rel.Kernel.Order

/-- q's `iasc` and `idesc` when a kernel claims them. `asc` and
`desc` are this permutation and K5's gather, and `rank` is this permutation graded again; none of
the three is a kernel of its own, `~/q/q.k` lines 12 and 13 defining them all from `<` and `>`.

The `.bit` guard on the last branch is `Scan.scanColumn`'s: a boolean column is `Column.bits` and a
`.bytes` payload announced at `boolean` holds no elements at all, so it must not be graded as though
its bytes were bits.

Under `rank` the answer is q's `rank`, `<<x` — always ascending, so `desc` is not read — and it is
this same dispatch: where a kernel ranks without building the grade it is asked for the rank, and
everywhere else the grade is inverted. -/
def gradeColumn (t : QAtomicType) (desc : Bool) (n : USize) (e : Ext.Enc X) (rank : Bool := false) : Option (Ext.Enc X) :=
  let inv (p : ByteArray) := if rank then invert p else p
  match t, e with
  | .symbol, .syms blob offs => some (.bytes (inv (gradeSyms desc blob offs)))
  | .symbol, .enum dict dof ids => some (.bytes (inv (gradeIds desc n dict dof ids)))
  | .boolean, .bits b =>
    some (.bytes (if rank then ranks .bit n b else grade .bit desc n b))
  | t, e =>
    match orderKind t with
    | none => none
    | some k =>
      -- a boolean `foR` is `u1`, every element 0 or 1, so its key is the `u8` one; `Kind.bit` reads only a bitmap
      if k == .bit then match e with
        | .foR md pk => some (.bytes (if rank then ranksFoR .u8 n md pk else gradeFoR .u8 desc n md pk))
        | _ => none
      -- the encoded case first, so that `Enc.bytesOf` is never forced underneath the kernel that
      -- made it unnecessary: the key is `base + residual` biased, and no element is ever restored
      else match e with
        | .foR md pk => some (.bytes
            (if rank then ranksFoR k n md pk else gradeFoR k desc n md pk))
        -- the answer is at the header's count, so a payload shorter than it is declined, not read past
        | e => match Enc.bytesOf t n e with
          | some b => if b.size < n.toNat * k.width then none
            else some (.bytes (if rank then ranks k n b else grade k desc n b))
          | none => none

/-- The first `n` ids of a `groupIdsColumn` answer `(ids, firsts)` as `long`s, at the width its
group count gives. -/
def groupLongs (n : USize) (p : ByteArray × ByteArray) : ByteArray :=
  Order.idLongs n (Column.idWidthOf (p.2.size / 8)).toUSize p.1

end Rel.Kernel

namespace Rel.Column

end Rel.Column

namespace Rel.Kernel

end Rel.Kernel
