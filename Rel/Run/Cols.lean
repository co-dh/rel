module

public import Rel.Run.Canon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! Column helpers shared by the set operators (`Rel/Run/SetOps.lean`) and composition (`Rel/Run/Comp.lean`), each a
composition of the five kernels on encoded columns: a constant column, a pointwise map, a running fold, and CONCAT
(`doc/rel-kernels.md`) of two tables' columns. Their laws are in `Rel/RepCols.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The running fold of `op` over the `n` words of `a` from the word `0`: `kscan` with one segment. -/
def colPrefix (op : Op) (n : USize) (a : Enc) : Except String Enc := do
  let z ← colConst n 0
  let r ← kscan op false .i64 .i64 n z [(n, z), (n, a)]
  pure r.1

/-- The `n` words `i + s`: one `kscan` of the positions with `s` added by its post chain, not `colMap .add` of a
`colConst n s`, which costs a `kscatter` more (`colMap_const_eq`). -/
def shiftCol (n : USize) (s : UInt64) : Except String Enc := colMap .first n .pos .pos .i64 .i64 [] [(.add, s)]

/-- `colMap`'s answer as an `Arr t n`, the map's output well formed at `t` (`colMap_closed`). -/
def colArr (op : Op) (n : USize) (a b : Enc) (t : QAtomicType := .i64) (s : QAtomicType := .i64)
    (pre post : List (Op × UInt64) := []) (hs : kscanStream op [(n, a), (n, b)] pre post = false := by lockstep)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by nulfree) :
    Except String (Arr t n) :=
  match h : colMap op n a b t s pre post with
  | .ok o => .ok (Arr.mk o (colMap_closed hs h hF).2 (colMap_plain hs h hF))
  | .error s => .error s

/-- The `kscan` chain taking a word of the atom `t` to the word its verbs and orders compute on: an `f32` word widened to
    `f64` (`Op.f32to64`, `fval`); `i64` and `f64` as stored; any other ordered atom to the `i64` word of its value
    (`Op.cast r .i64`, `r` its `ordNum`: `iordAt`); any other as stored. -/
def widen (t : QAtomicType) : List (Op × UInt64) :=
  match t with
  | .f32 => [(.f32to64, 0)]
  | .i64 | .f64 => []
  | t => match t.ordNum with
    | some r => [(.cast r .i64, 0)]
    | none => []

/-- Two columns hold no null: the sources of a lock-step `kscan` over them satisfy `kscan`'s `hF` (an `Arr` is null-free
by its type, `x.plain`, so `max`/`min` of arrays never meets an in-band null). -/
theorem nulFree₂ {n : USize} {a b : Enc} (ha : hasNul a = false) (hb : hasNul b = false) :
    ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl)
  · exact ha
  · exact hb

/-- `kscan`'s answer as an `Arr t n`, well formed at `t` (`kscan_closed`). -/
def scanArr (op : Op) (rev : Bool) (s t : QAtomicType) (n : USize) (seg : Option Enc) (es : List (USize × Enc))
    (pre post : List (Op × UInt64) := []) (hs : kscanStream op es pre post = false := by lockstep)
    (hF : op.nulFold = none ∨ ∀ p ∈ es, hasNul p.2 = false := by nulfree) :
    Except String (Arr t n) :=
  match h : kscan op rev s t n seg es pre post with
  | .ok r =>
    .ok (Arr.mk r.1 (kscan_lock_closed hs hF h).2.1 (kscan_lock_closed hs hF h).2.2)
  | .error s => .error s

/-- **`colArr` is `colMap`** on the array's column. -/
theorem colArr_ok {op : Op} {n : USize} {a b : Enc} {t s : QAtomicType} {pre post : List (Op × UInt64)}
    {w : Arr t n} {hs : kscanStream op [(n, a), (n, b)] pre post = false}
    {hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false} (h : colArr op n a b t s pre post hs hF = .ok w) : colMap op n a b t s pre post = .ok w.enc := by
  unfold colArr at h; split at h
  · cases h; rename_i o hc; exact hc
  · cases h

/-- A column of `foROk` rows is one every kernel reads (`Enc.Valid`). -/
theorem foROk_valid {n : USize} {e : Enc} (h : foROk n e = true) : Enc.Valid n e := by cases e <;> simpa [Enc.Valid] using h

/-- A stream over columns holding no null writes no flag: `streamEnc` holds no null. -/
theorem streamEnc_plain {s t : QAtomicType} {es : List (USize × Enc)} (hW : ∀ p ∈ es, Ext.Enc.WF s p.1 p.2)
    (hN : ∀ p ∈ es, hasNul p.2 = false) : hasNul (streamEnc s t es) = false := by
  have key : ∀ (L : List (Array UInt64)) (acc : Array UInt64), (∀ x ∈ acc, x = 0) → (∀ a ∈ L, ∀ x ∈ a, x = 0) →
      ∀ x ∈ L.foldl (· ++ ·) acc, x = 0 := by
    intro L; induction L with
    | nil => intro acc h _; exact h
    | cons a L ih =>
      intro acc h hL
      exact ih _ (fun x hx => by
        rcases Array.mem_append.1 hx with hx | hx
        · exact h x hx
        · exact hL a (by simp) x hx) (fun b hb => hL b (by simp [hb]))
  have hz : (streamNul es).any (· != 0) = false := by
    rw [Bool.eq_false_iff]; intro h
    obtain ⟨i, hi, hp⟩ := Array.any_eq_true.1 h
    obtain ⟨v, hv⟩ : ∃ v, v = (streamNul es)[i] := ⟨_, rfl⟩
    have hmem : v ∈ streamNul es := hv ▸ Array.getElem_mem hi
    rw [streamNul_eq] at hmem
    have := key (es.map fun p => foRNuls p.1 p.2) #[] (fun x hx => by simp at hx) (fun a ha x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
      have := foRNuls_plain (hW p hp) (hN p hp) (i := j) (by simpa [foRNuls_size] using hj)
      rw [Array.getElem?_eq_getElem hj] at this
      exact Option.some.inj this) v hmem
    rw [← hv] at hp
    simp [this] at hp
  unfold streamEnc; rw [hz]; exact hasNul_wordsFoR _

/-- **CONCAT of two nullable columns of one type**: ONE `kscan` stream of `x` then `y` (`kscanStream`, `.first` with no
chain), which re-encodes the `n₁ + n₂` words block by block and carries each row's null flag, so a null stays a null
in-band. Where `t` has no width, the sources do not hold `n` rows between them or a source is no `foR`/`pos` column
of its row count (the check each kernel's reader makes), the error. -/
def Opt.concat {t : QAtomicType} {n₁ n₂ : USize} (n : USize) (x : Opt t n₁) (y : Opt t n₂) :
    Except String (Opt t n) :=
  if hn : n₁.toNat + n₂.toNat = n.toNat then
    if hv : foROk n₁ x.enc = true ∧ foROk n₂ y.enc = true then
      match hw : t.width with
      | some _ =>
        match h : kscan .first false t t n none [(n₁, x.enc), (n₂, y.enc)] with
        | .ok r => .ok (Opt.mk r.1 (by
            obtain ⟨h1, -, hwf⟩ := kscan_stream_closed (s := t) hw (by rw [hw]; rfl) (n := n) (es := [(n₁, x.enc), (n₂, y.enc)])
              (by simp; exact ⟨x.wf, y.wf⟩) (by simp) (by simpa using hn)
            rw [h] at h1; cases h1; exact hwf))
        | .error e => .error e
      | none => .error s!"concat: {repr t} has no fixed width"
    else .error s!"concat: a column of {n₁} or {n₂} rows is no foR or pos column of its row count"
  else .error s!"concat: {n₁} + {n₂} rows are not n = {n}"

/-- CONCAT of two columns holding no null: `Opt.concat` of them, read back as an `Arr` (the stream writes no flag,
`streamEnc_plain`, so the `hasNul` test never fails). -/
def Arr.concat {t : QAtomicType} {n₁ n₂ : USize} (n : USize) (x : Arr t n₁) (y : Arr t n₂) : Except String (Arr t n) := do
  let z ← Opt.concat n (Opt.ofArr x) (Opt.ofArr y)
  if hz : hasNul z.enc = false then pure (Arr.mk z.enc z.wf hz)
  else .error s!"concat: the stream of two columns with no null holds one"

/-- The count of `n₁` rows then `n₂`, the error where it does not fit a `USize`. -/
def catRows (n₁ n₂ : USize) : Except String USize :=
  if n₁.toNat + n₂.toNat < USize.size then pure (n₁.toNat + n₂.toNat).toUSize
  else .error s!"concat: {n₁} + {n₂} rows do not fit a USize"

/-- The first of the `n` cells `[lo, hi)` that is no slice of a payload of `m` rows (`0 ≤ lo ≤ hi ≤ m` fails), the
check `readVals` makes once (PLAN 8.5); `none` is `Vals.WF`'s cell clause (`cellBad_none`). -/
def cellBad {n : USize} (m : USize) (lo hi : Arr .i64 n) : Option (Fin n.toNat) :=
  (List.finRange n.toNat).find? fun i =>
    !decide (0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int))

/-- No `arr` side of `x` has a `cellBad` cell: `Vals.WF` decided (`Vals.cellsOk_wf`), for a table no `readVals`
read (a literal, a universe). -/
def ValsB.cellsOk : {A : Obj} → {n : USize} → Vals A n → Bool
  | .atom _, _, _ | .one, _, _ => true
  | .prod _ _, _, x => ValsB.cellsOk x.1 && ValsB.cellsOk x.2
  | .arr _, _, ⟨m, lo, hi, f⟩ => (cellBad m lo hi).isNone && ValsB.cellsOk f
  | .sum _ _, _, s => match s.view with
    | .opt .. => true
    -- the filler clause of `Vals.WF` is not decided here: a literal dense sum is refused until it is (PLAN 8.2)
    | .gen .. => false

/-- The words of `x` with `s` added: one `kscan` whose post chain adds `s` (`colMap_const_eq`). -/
def Arr.shift {n : USize} (s : UInt64) (x : Arr .i64 n) : Except String (Arr .i64 n) :=
  colArr .first n x.enc x.enc .i64 .i64 [] [(.add, s)]

/-- The words of `x` clamped into `[0, c]` (`max` with `0`, then `min` with `c`), then `s` added: one `kscan` whose post
chain holds the three constants (`colMap_const_eq`). -/
def Arr.clampShift {n : USize} (c s : UInt64) (x : Arr .i64 n) : Except String (Arr .i64 n) :=
  colArr .first n x.enc x.enc .i64 .i64 [] [(.max, 0), (.min, c), (.add, s)]

/-- The sources of `colPrefix`'s `kscan` (the zero column and `a`) hold no null where `a` holds none: `hF` for `kscan`. -/
theorem colPrefix_hF {op : Op} {n : USize} {a z : Enc} (hz : colConst n 0 = .ok z)
    (hF : op.nulFold = none ∨ hasNul a = false) :
    op.nulFold = none ∨ ∀ p ∈ [(n, z), (n, a)], hasNul p.2 = false :=
  hF.imp_right fun ha p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Verify.kscatter_plain hz rfl
    · exact ha

/-- `colPrefix`'s answer is a column every kernel reads, `Enc.WF` at `i64` (`kscan_closed`). -/
theorem colPrefix_closed {op : Op} {n : USize} {a o : Enc} (h : colPrefix op n a = .ok o) (ho : op ≠ .first := by decide)
    (hF : op.nulFold = none ∨ hasNul a = false := by nulfree) :
    Kernel.Enc.Valid n o ∧ Enc.WF .i64 n o := by
  unfold colPrefix at h; simp only [bind, Except.bind] at h; split at h; · cases h
  rename_i z hz
  split at h; · cases h
  rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  have hF' := colPrefix_hF hz hF
  exact ⟨(kscan_lock_closed (kscanStream_ne ho _ _ _) hF' hr).1, (kscan_lock_closed (kscanStream_ne ho _ _ _) hF' hr).2.1⟩

/-- `colPrefix`'s answer holds no null (`kscan_closed`). -/
theorem colPrefix_plain {op : Op} {n : USize} {a o : Enc} (h : colPrefix op n a = .ok o) (ho : op ≠ .first := by decide)
    (hF : op.nulFold = none ∨ hasNul a = false := by nulfree) :
    hasNul o = false := by
  unfold colPrefix at h; simp only [bind, Except.bind] at h; split at h; · cases h
  rename_i z hz
  split at h; · cases h
  rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact (kscan_lock_closed (kscanStream_ne ho _ _ _) (colPrefix_hF hz hF) hr).2.2

/-- The last of the `n` words of the `i64` column `e`, or `0` at `n = 0`, read as a count (`Arr.get`, one element). -/
def lastCount (n : USize) (e : Enc) (h : Enc.WF .i64 n e) (hN : hasNul e = false) : Nat :=
  if hn : 0 < n.toNat then (Arr.get (Arr.mk e h hN) ⟨n.toNat - 1, by omega⟩).toNatClampNeg else 0

/-- The positions of a sum side's summand `s` (`false` left, `true` right): `idx` on the rows `tag` gives to it, `0` on
the others (`colMap .mul` by `tag` or by its `.not`), as `ValsB.cols` gathers a summand. -/
def summandPos (n : USize) (s : Bool) (tag : Arr .u1 n) (idx : Enc) : Except String Enc :=
  if s then colMap .mul n idx tag.enc else do colMap .mul n idx (← colMap .not n tag.enc tag.enc)

/-- The count of the `n` rows `tag` gives to the summand `s`: `tag`'s words (`.not` of them at `s = false`), their running sum
(`colPrefix .add`), the last word (`lastCount`); past `2^63` rows, which a signed count cannot reach, the error. -/
def tagCount (n : USize) (s : Bool) (tag : Arr .u1 n) : Except String Nat :=
  if 2 ^ 63 ≤ n.toNat then .error s!"count: {n} rows, past an Int64 count" else do
    let p := (← kscan .first false .i64 .i64 n none [(n, tag.enc)] [] (if s then [] else [(.not, 0)])).1
    match h : colPrefix .add n p with
    | .ok P => .ok (lastCount n P (colPrefix_closed h).2 (colPrefix_plain h))
    | .error e => .error e

/-- The positions `0 … n-1`, a `foR` column (`shiftCol n 0`). -/
def Arr.pos (n : USize) : Except String (Arr .i64 n) :=
  match h : shiftCol n 0 with
  | .ok o => .ok (Arr.mk o (colMap_closed (by simp [kscanStream]) h).2 (colMap_plain (by simp [kscanStream]) h))
  | .error e => .error e

/-- Summand `s` of a sum side of `m` rows (tags `tag`, positions `idx`) at those rows, as `ValsB.row` reads them: its
rows `x` gathered at `summandPos` of the positions clamped into `x`. Where `x` has no rows, a row tagged into it reads
`Obj.dflt`, which no payload row holds: with no such row (`tagCount` is `0`) the rows are never read, and the other
side's summand `o` gathered at row `0` stands in; with some, the error naming the summand and the count. -/
def Vals.catSide {B : Obj} {m l l' : USize} (s : Bool) (tag : Arr .u1 m) (idx : Arr .i64 m) (x : ValsB true B l)
    (o : ValsB true B l') : Except String (ValsB true B m) :=
  if l.toNat = 0 then do
    let c ← tagCount m s tag
    if c = 0 then ValsB.gather m (← colConst m 0) o
    else .error s!"concat: {c} rows tagged into the {if s then "right" else "left"} summand, which has no rows"
  else do ValsB.gather m (← summandPos m s tag (← idx.clampShift (l.toUInt64 - 1) 0).enc) x

/-- Summand `s` of the concat of two sum sides of `n₁` and `n₂` rows, its rows `x₁` and `x₂` on each: their concat
`cat` where both are empty (every row of the summand reads `Obj.dflt`), else each side's `Vals.catSide` (the other
side's summand standing in for an empty one) concatenated, `n` rows read at the positions `Arr.pos`. -/
def Vals.catSummand {B : Obj} {n₁ n₂ l₁ l₂ : USize} (n : USize) (s : Bool) (tag₁ : Arr .u1 n₁)
    (idx₁ : Arr .i64 n₁) (x₁ : ValsB true B l₁) (tag₂ : Arr .u1 n₂) (idx₂ : Arr .i64 n₂) (x₂ : ValsB true B l₂)
    (cat : {m₁ m₂ : USize} → (m : USize) → ValsB true B m₁ → ValsB true B m₂ → Except String (ValsB true B m)) :
    Except String ((m : USize) × ValsB true B m) :=
  if l₁.toNat = 0 ∧ l₂.toNat = 0 then do let m ← catRows l₁ l₂; pure ⟨m, ← cat m x₁ x₂⟩
  else if 2 ^ 63 < l₁.toNat ∨ 2 ^ 63 < l₂.toNat then .error s!"concat: a sum summand of {l₁} or {l₂} rows, past 2^63"
  else do pure ⟨n, ← cat n (← Vals.catSide s tag₁ idx₁ x₁ x₂) (← Vals.catSide s tag₂ idx₂ x₂ x₁)⟩

/-- The words of the nullable `x` with `s` added: `Arr.shift` over `Opt`, a null staying null (`colMap_closed`). -/
def Opt.shift {n : USize} (s : UInt64) (x : Opt .i64 n) : Except String (Opt .i64 n) :=
  match h : colMap .first n x.enc x.enc .i64 .i64 [] [(.add, s)] with
  | .ok o => .ok (Opt.mk o (colMap_closed (by lockstep) h).2)
  | .error e => .error e

/-- CONCAT of two atom columns at ownership `o`: `Arr.concat`, or `Opt.concat` where a row may be null. -/
def ColB.concat : {o : Bool} → {t : QAtomicType} → {n₁ n₂ : USize} → (n : USize) → ColB o t n₁ → ColB o t n₂ →
    Except String (ColB o t n)
  | false, _, _, _, n, x, y => Arr.concat n x y
  | true, _, _, _, n, x, y => Opt.concat n x y

/-- A long column's words with `s` added, at ownership `o`. -/
def ColB.shift : {o : Bool} → {n : USize} → UInt64 → ColB o .i64 n → Except String (ColB o .i64 n)
  | false, _, s, x => Arr.shift s x
  | true, _, s, x => Opt.shift s x

/-- The rows of `x`, then those of `y`, as `n` rows: `ColB.concat` of each atom column. An `arr` side
concatenates its payloads (`catRows`, the recursive call) and its `lo`, `hi` columns, the second's shifted past the
first payload (`Vals.WF`: each cell already inside its own payload, so none reads the other's); a payload past `2^63` rows,
which an `Int64` bound cannot reach, is the error. A `sum` side concatenates its tags and each summand column. -/
def ValsB.concat : {o : Bool} → {A : Obj} → {n₁ n₂ : USize} → (n : USize) → ValsB o A n₁ → ValsB o A n₂ →
    Except String (ValsB o A n)
  | _, .atom _, _, _, n, x, y => ColB.concat n x y
  | _, .prod _ _, _, _, n, x, y => do pure (← ValsB.concat n x.1 y.1, ← ValsB.concat n x.2 y.2)
  | _, .arr _, _, _, n, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ =>
    if m₁.toNat + m₂.toNat < 2 ^ 63 then do
      let p ← catRows m₁ m₂
      let lo ← ColB.concat n lo₁ (← ColB.shift m₁.toUInt64 lo₂)
      let hi ← ColB.concat n hi₁ (← ColB.shift m₁.toUInt64 hi₂)
      pure ⟨p, lo, hi, ← ValsB.concat p f₁ f₂⟩
    else .error s!"concat: {m₁} + {m₂} payload rows, past an Int64 bound"
  | _, .sum _ _, _, _, n, s₁, s₂ => match ValsB.view s₁, ValsB.view s₂ with
    | .opt h x₁, .opt h' x₂ => ValsB.ofOpt h <$> Opt.concat n x₁ (Option.some.inj (h'.symm.trans h) ▸ x₂)
    | .opt h _, .gen h' .. | .gen h' .., .opt h _ => absurd (h.symm.trans h') nofun
    | .gen h tag₁ x₁ y₁, .gen _ tag₂ x₂ y₂ =>
      do pure (ValsB.ofGen h (← Arr.concat n tag₁ tag₂) (← ValsB.concat n x₁ x₂) (← ValsB.concat n y₁ y₂))
  | _, .one, _, _, _, _, _ => pure ()

end Rel
