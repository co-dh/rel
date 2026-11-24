module

public import Rel.Run.Core
public import Rel.Kernel.Seen
public import Rel.KernelSpec.Closure

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The column helpers below `Canon`: a constant column, a pointwise map, a side gathered at positions, WHERE, and a bit
matrix read back as rows (`Tab.ofBits`). Apart from `Canon` because `Rel.bits` (`Lazy.lean`) reads with `Tab.ofBits`,
and `Canon`'s `Tab.dom`/`Tab.ran` would then reach every module that opens both `Tab` and `Alg`, making `dom` ambiguous. -/

namespace Rel
open  Rel.Kernel Rel.Verify

/-- The source column of a successful `kgather` is one every kernel reads (`foRWords` accepted it). -/
theorem kgather_valid {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) : Kernel.Enc.Valid n e := by
  unfold kgather at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i ws hws
  exact (foRWords_valid _ _ _).2 _ hws

/-- **A gathered column is a column of its type**, nulls included (`Opt`, so `Arr` by `Opt.ofArr`): the source is a
valid column under `Enc.WF`, so a `foR` one at a type with a width, whose words at `u1` but a null's are below `2`; a
gathered row that is no null reads a source row that is no null (its flag moves with it, `raw_kgather`), so its word
is one of them. -/
theorem Opt.kgather_wf {t : QAtomicType} {n m : USize} {ix o : Enc} (x : Opt t n) (h : kgather m ix n x.enc = .ok o) :
    Enc.WF t m o := by
  have hv := kgather_valid h
  obtain ⟨his, -, hlt, rfl⟩ := raw_kgather m ix n x.enc o h
  have hw := x.wf
  generalize x.enc = e at hv hw hlt ⊢
  cases e with
  | foR md pk =>
    have hw' : t.width.isSome = true ∧ (t = .u1 → ∀ i < n.toNat, ∀ v,
        Column.foROpt md pk (Column.blockStarts md) i = some v → v.toNat < 2) ∧
        n.toNat ≤ Column.blk md * Column.nblk md := by
      cases t <;> simp only [Enc.WF] at hw <;>
        first | exact ⟨hw.1, hw.2.1, hw.2.2.1⟩ | exact ⟨hw.1, fun _ => hw.2.1 trivial, hw.2.2.1⟩ | exact ⟨hw.1, fun h => absurd h (by decide), hw.2.1⟩
    refine (wordsFoR_nul _ _ (by rw [Array.size_map, his])).2.2.2 hw'.1 fun hu k hk hk0 => ?_
    rw [Array.size_map] at hk
    have hi := hlt k (by omega)
    rw [Array.getElem?_eq_getElem hk, Option.getD_some] at hi
    -- the gathered row is no null (`hk0`), so neither is the source row it reads
    have hnn : Column.foRNul md pk (Column.blockStarts md) (Enc.raw .i64 m ix)[k].toNat = false := by
      by_cases hN : hasNul (.foR md pk) = true
      · rw [if_pos hN, nulMap] at hk0
        rw [Verify.bitAt_packOf _ _ _ (by rw [Array.size_map]; exact hk)] at hk0
        simp only [Array.getElem?_map, Array.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, foRNuls,
          Array.getElem?_range, hi, if_true] at hk0
        revert hk0; cases Column.foRNul md pk (Column.blockStarts md) (Enc.raw .i64 m ix)[k].toNat <;> decide
      · exact foRNul_of_plain (Bool.eq_false_iff.2 hN) (Nat.lt_of_lt_of_le hi hw'.2.2)
    simp only [Array.getElem_map, raw_foR .i64 8 rfl (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map,
      Array.getElem?_range, hi, if_true, Option.map_some, Option.getD_some, Nat.reduceMul, ofNat_toNat_mod64]
    exact UInt64.lt_iff_toNat_lt.2 (hw'.2.1 hu _ hi _ (by simp [Column.foROpt, hnn]))
  | pos =>
    -- `pos` is a column only at `i64` (`Enc.WF`), where the gathered words need no bound
    cases t <;> simp only [Enc.WF] at hw
    simp only [hasNul, Bool.false_eq_true, if_false]
    exact (wordsFoR_closed _ (by rw [Array.size_map, his])).2.2 rfl (fun h => absurd h (by decide))
  | _ => all_goals simp only [Kernel.Enc.Valid] at hv

/-- `n` cells holding the word `w`: `kscatter` of no rows. -/
def colConst (n : USize) (w : UInt64) : Except String Enc := kscatter .last 0 .pos .pos n w

/-- `op` row by row over the `n` words of `a` and `b` read at `s`, each through `chain pre`, the answer through
`chain post`: `out[i] = post(op(pre(a[i]), pre(b[i])))` written at `t`, in one `kscan` pass with every row starting a
segment (`seg = none`: no column is written for it). `.first` over the two columns is a stream (`kscanStream`), not a map. -/
def colMap (op : Op) (n : USize) (a b : Enc) (t : QAtomicType := .i64) (s : QAtomicType := .i64)
    (pre post : List (Op × UInt64) := []) : Except String Enc := do
  let r ← kscan op false s t n none [(n, a), (n, b)] pre post
  pure r.1

/-- `colMap`'s answer is a column every kernel reads, `Enc.WF` at `t`, holding no null (`kscan_closed`). -/
theorem colMap_closed {op : Op} {n : USize} {a b o : Enc} {t s : QAtomicType} {pre post : List (Op × UInt64)}
    (hs : kscanStream op [(n, a), (n, b)] pre post = false) (h : colMap op n a b t s pre post = .ok o)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, b)], hasNul p.2 = false := by nulfree) :
    Kernel.Enc.Valid n o ∧ Enc.WF t n o ∧ hasNul o = false := by
  unfold colMap at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact kscan_lock_closed hs hF hr

/-- `colMap` of one column with itself under an op that orders null (`Op.nulFold`), a null row of it included, answers a
column every kernel reads, `Enc.WF` at `t` (`kscan_nul_row` where `a` holds a null, `colMap_closed` where not). -/
theorem colMap_closed_nul {op b : Op} {fill : UInt64} (hnf : op.nulFold = some (b, fill)) {n : USize} {a o : Enc}
    {t s : QAtomicType} {post : List (Op × UInt64)} (ht : t.width.isSome) (hsw : s.width.isSome)
    (hW : Enc.WF s n a) (hs : kscanStream op [(n, a), (n, a)] [] post = false)
    (h : colMap op n a a t s [] post = .ok o) : Kernel.Enc.Valid n o ∧ Enc.WF t n o := by
  have hWs : ∀ p ∈ [(n, a), (n, a)], Enc.WF s p.1 p.2 := fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> exact hW
  by_cases hN : hasNul a = true
  · unfold colMap at h; simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ht
    obtain ⟨out, nl, -, -, -, hV, hF, -⟩ := kscan_nul_row hnf hw hsw hs hWs ⟨(n, a), by simp, hN⟩ hr
    exact ⟨hV, hF⟩
  · exact (colMap_closed hs h (Or.inr fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simpa using hN)).imp_right And.left

/-- The rows `ix` (`m` positions) of the column `x`: `kgather` at `ix`, an `Arr` again by `Opt.kgather_wf`. -/
def Arr.gather {t : QAtomicType} {n : USize} (m : USize) (ix : Enc) (x : Arr t n) : Except String (Arr t m) :=
  match h : kgather m ix n x.enc with
  | .ok o => .ok (Arr.mk o (Opt.kgather_wf (Opt.ofArr x) h)
      (by rw [Verify.kgather_plain h x.plain]; exact Verify.hasNul_wordsFoR _))
  | .error s => .error s

/-- The rows `ix` (`m` positions) of the nullable column `x`: `kgather`, which moves each row's null flag with its word
(`raw_kgather`), so a null row gathers to a null row; an `Opt` again by `Opt.kgather_wf`. -/
def Opt.gather {t : QAtomicType} {n : USize} (m : USize) (ix : Enc) (x : Opt t n) : Except String (Opt t m) :=
  match h : kgather m ix n x.enc with
  | .ok o => .ok (Opt.mk o (Opt.kgather_wf x h))
  | .error s => .error s

/-- The rows `ix` (`m` positions) of an atom column at ownership `o`: `Arr.gather`, or `Opt.gather` where a row may be null. -/
def ColB.gather : {o : Bool} → {t : QAtomicType} → {n : USize} → (m : USize) → Enc → ColB o t n →
    Except String (ColB o t m)
  | false, _, _, m, ix, x => Arr.gather m ix x
  | true, _, _, m, ix, x => Opt.gather m ix x

/-- The rows `ix` of `x`, at either ownership `o`: a summand's null rows gather to null rows (`Opt.gather`). -/
def ValsB.gather (m : USize) (ix : Enc) : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n →
    Except String (ValsB o A m)
  | _, .atom _, _, x => ColB.gather m ix x
  | _, .prod _ _, _, x => do pure (← ValsB.gather m ix x.1, ← ValsB.gather m ix x.2)
  | _, .arr _, _, ⟨c, lo, hi, f⟩ => do pure ⟨c, ← ColB.gather m ix lo, ← ColB.gather m ix hi, f⟩
  | _, .sum _ _, _, s => match ValsB.view s with
    | .opt h x => do pure (ValsB.ofOpt h (← Opt.gather m ix x))
    | .gen h tag x y =>
      do pure (ValsB.ofGen h (← Arr.gather m ix tag) (← ValsB.gather m ix x) (← ValsB.gather m ix y))
  -- no column, but `ix` is checked as every side's is: gathering the positions `0 … n-1` refuses an index past `n`
  | _, .one, n, _ => do let _ ← Arr.gather m ix (Arr.mk (t := .i64) (n := n) .pos trivial rfl); pure ()

/-- The positions of the `1` words among the `m` words `b` (each `0` or `1`), ascending, and their count `K`. WHERE
as `scan → scatter`, O(m) and no sort: the prefix sum `s` of `b` (`kscan .add`, one segment) returns the count `K` as
its fold result; `m = 0` folds no row and returns `none`, and an empty `where` counts `0` positions by definition, so
`none` is `K = 0`. The destination `d = s − b` (`colMap .sub`) is the number of kept rows before each row: a kept row's
own cell `0 … K − 1`, and a dropped row's the next kept row's cell, which that later row overwrites (`kscatter .last`,
the last row winning), or the spare cell `K` past every kept row. `kscatter` of `pos` at `d` into `K + 1` cells, then
`kgather` of the first `K` (at `pos`): 6 kernel calls (`colConst`, `kscan`, `colMap` = `colConst` + `kscan`,
`kscatter`, `kgather`), where `kasc ≫ kseen` took 13. `m` is below `B`, so `K + 1 ≤ m + 1` cells fit a `USize`. -/
def whereCol (m : USize) (b : Enc) : Except String (USize × Enc) :=
  let B := min (USize.size - 1) (2 ^ 63)
  if m.toNat < B then do
    let z ← colConst m 0
    let sk ← kscan .add false .i64 .i64 m z [(m, z), (m, b)]
    let K := (sk.2.getD 0).toNat.toUSize
    let d ← colMap .sub m sk.1 b
    let e ← kscatter .last m d .pos (K.toNat + 1).toUSize 0
    (K, ·) <$> kgather K .pos (K.toNat + 1).toUSize e
  else .error s!"where: {m} rows, not below {B}: m + 1 cells fit a USize and the counts 0 … m are i64 words below it"

-- `1 0 1 1 0`: the destinations `0 1 1 2 3` send the dropped row 1 to row 2's cell and row 4 to the spare cell `3`
#guard (whereCol 5 (Enc.ofBytes 8 (Column.packIds 64 5 fun i => [1, 0, 1, 1, 0][i]?.getD 0))).toOption.map
  (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (3, [0, 2, 3])
-- no kept row, and no row at all: `K = 0`
#guard (whereCol 3 (Enc.ofBytes 8 (Column.packIds 64 3 fun _ => 0))).toOption.map
  (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (0, [])
#guard (whereCol 0 .pos).toOption.map (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (0, [])

/-- The set bits of the `g · w` bits `o`, bit `a·w + c` the row `(x[ra[a]], y[rc[c]])`: `whereCol`, then `a` and `c` by
the post steps `(.rdiv, w)`, `(.rmod, w)`, each side `kgather`ed. Ascending by `(a, c)`, so canonical where the numbers are `kasc` ranks. -/
def Tab.ofBits {A C : Obj} {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) :
    Except String (Tab A C) := do
  let (M, sel) ← whereCol (g * w) o
  expandNote s!"a {g}×{w} bit matrix read back as rows (Tab.ofBits)" M.toNat fun _ => do
    let ix ← kgather M (← colMap .first M sel sel .i64 .i64 [] [(.rdiv, w.toUInt64)]) g ra
    let iy ← kgather M (← colMap .first M sel sel .i64 .i64 [] [(.rmod, w.toUInt64)]) w rc
    pure ⟨M, ← ValsB.gather M ix x, ← ValsB.gather M iy y⟩

end Rel
