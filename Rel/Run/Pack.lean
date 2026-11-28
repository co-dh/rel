module

public import Rel.Run.Cols
public import Rel.Run.SetOps

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `pack`: a table's array payloads cut to the elements its cells read (`Vals.cells`, `ValsB.pack`, `Tab.pack`). Before
`Rel/Run/Comp.lean` so that `Tab.compBlocks` packs its accumulator as `fixOn`'s rounds do. -/

namespace Rel
open  Rel.Kernel Rel.Verify

/-- **EXPAND** (`doc/rel-kernels.md`) of the `K` widths `w`: `T` output rows, each row's group `G` and its offset `u`
in the group. A prefix sum `P` places the groups (`o = P - w`), `kscatter (.max)` of each group id at its offset,
filled forward by `colPrefix (.max)`, the spare cell `T` cut off by `kgather`; `u = pos - o[G]`. The one scalar read
is the count `T` (`lastCount`). -/
def expand (K : USize) (w : Enc) : Except String (USize × Enc × Enc) := do
  match hP : colPrefix .add K w with
  | .error s => throw s
  | .ok P =>
    let T := lastCount K P (colPrefix_closed hP).2.1 (colPrefix_closed hP).2.2
    if USize.size ≤ T + 1 then throw s!"expand: {T} output rows past USize"
    let T := T.toUSize
    expandNote s!"the {K} groups of a composition (expand)" T.toNat fun _ => do
      let o ← colMap .sub K P w
      let G ← kgather T .pos (T + 1) (← colPrefix .max (T + 1) (← kscatter .max K o .pos (T + 1) 0))
      pure (T, G, ← colMap .sub T .pos (← kgather T G K o))


/-- `n` cells of the widths `w`, laid out one after another over the payload `pay`: `hi` the running sum of `w`
(`colPrefix .add`, the layout `expand` places its groups by), `lo = hi - w`. -/
def Vals.cells {B : Obj} {T : USize} (n : USize) (w : Enc) (pay : Vals B T) : Except String (Vals (.arr B) n) := do
  let P ← colPrefix .add n w
  pure ⟨T, ← colArr .sub n P w, ← scanArr .first false .i64 .i64 n Option.none [(n, P)], pay⟩

/-- The words of `x` as a nullable column, null in the rows where `big` (a nullable column of `i64` max) is: `min` of the
two, `big` being above every word of `x` there (null orders below, and `min` is null where any source is); decided
`Enc.WF` as `Arr.of` decides it. -/
def Opt.maskWith {n : USize} (big : Enc) (x : Arr .i64 n) : Except String (Opt .i64 n) := do
  let e ← colMap .min n big x.enc
  match Enc.wf? .i64 n e with
  | some ⟨h⟩ => pure (Opt.mk e h)
  | none => throw s!"pack: the masked bounds are not {n} well-formed longs (`Enc.wf?` refuses their blocks)"

/-- `x` with every array payload cut to the elements its cells read, where at most `1/k` of it is read (`k · T ≤ m`,
`T` the summed widths): the widths EXPANDed, the payload `kgather`ed there, laid out by `Vals.cells`; nested payloads
the same. A payload joined to a copy of itself (`ValsB.concat` in `∪`, `cat`) doubles while its cells read one copy;
the cut at `k = 2` is paid by the dead half, so a round's slices (`uncons`) are not copied each round. `k = 0` cuts
every payload: the payload is then the cells' slices one after another and `lo`, `hi` their running sums, a form
that depends on the cells alone (design §0: a payload past the cells' reach is no part of an `arr` value), which is
what an output file holds (`Table.writeVals`). -/
def ValsB.pack (k : Nat) : {o : Bool} → {A : Obj} → {n : USize} → ValsB o A n → Except String (ValsB o A n)
  | _, .atom _, _, x => pure x
  | _, .prod _ _, _, x => do pure (← ValsB.pack k x.1, ← ValsB.pack k x.2)
  -- a summand's cells (`o = true`) have null bounds in the rows of the other summand: `max` with `0` reads a null as
  -- `0` (null orders below every value), so such a row has width `0` and no payload; the laid-out cells are `min`ed
  -- with `big`, `i64` max where a bound is a value and null where it is null, which keeps the nulls
  | true, .arr _, n, ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"pack: {n} cells over {m} elements past 2^63"
    let z ← colConst n 0
    let s ← colMap .max n lo.enc z
    let w ← colMap .sub n (← colMap .max n hi.enc z) s
    match hP : colPrefix .add n w with
    | .error err => throw err
    | .ok P =>
      if 0 < m.toNat ∧ k * lastCount n P (colPrefix_closed hP).2.1 (colPrefix_closed hP).2.2 ≤ m.toNat then do
        let (T, G, u) ← expand n w
        let ⟨T', lo', hi', f'⟩ ← Vals.cells n w (← ValsB.pack k (← ValsB.gather T (← colMap .add T (← kgather T G n s) u) f))
        let big ← colMap .max n lo.enc lo.enc .i64 .i64 [] [(.and, 0), (.or, 0x7fffffffffffffff)]
        pure ⟨T', ← Opt.maskWith big lo', ← Opt.maskWith big hi', f'⟩
      else pure ⟨m, lo, hi, ← ValsB.pack k f⟩
  | false, .arr _, n, ⟨m, lo, hi, f⟩ => do
    -- the bounds, widths, their prefix sums and the positions `lo + u` are read signed: each below `n * m + n + m`
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"pack: {n} cells over {m} elements past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    match hP : colPrefix .add n w with
    | .error err => throw err
    | .ok P =>
      if 0 < m.toNat ∧ k * lastCount n P (colPrefix_closed hP).2.1 (colPrefix_closed hP).2.2 ≤ m.toNat then do
        let (T, G, u) ← expand n w
        Vals.cells n w (← ValsB.pack k (← ValsB.gather T (← colMap .add T (← kgather T G n lo.enc) u) f))
      else pure ⟨m, lo, hi, ← ValsB.pack k f⟩
  | _, .sum _ _, _, s => match s.view with
    | .opt .. => pure s
    | .gen h tag x y => do pure (ValsB.ofGen h tag (← ValsB.pack k x) (← ValsB.pack k y))
  | _, .one, _, _ => pure ()

/-- **`R` with its payloads cut** (`ValsB.pack` of both sides): the same rows in the same order. -/
def Tab.pack {k v : Obj} (R : Tab k v) : Except String (Tab k v) := do
  pure ⟨R.n, ← ValsB.pack 2 R.key, ← ValsB.pack 2 R.val⟩

end Rel
