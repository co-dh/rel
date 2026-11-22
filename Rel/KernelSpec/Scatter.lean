import Rel.Kernel.Scatter
import Rel.KernelSpec.Raw

/-! `scatter`'s law (design §4: `out[ix[k]] = e[k]`), on the words `Enc.raw` reads from its arguments. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- The fold `scatterWords` runs, over the first `m` rows from any start `o`: it succeeds exactly when every index is
below `n`, keeps the size, leaves a cell no row names as it was, and holds in a named cell the last row naming it. -/
private theorem scatterFold (I : Nat → Nat) (X : Nat → UInt64) (n : Nat) (err : Nat → String)
    (o : Array UInt64) (m : Nat) :
    let step := fun (o : Array UInt64) k =>
      if I k < n then (Except.ok (o.setIfInBounds (I k) (X k)) : Except String _) else .error (err k)
    ((∃ ws, (List.range m).foldlM step o = .ok ws) ↔ ∀ k < m, I k < n) ∧
    ∀ ws, (List.range m).foldlM step o = .ok ws → ws.size = o.size ∧
      (∀ j, (∀ k < m, I k ≠ j) → ws[j]? = o[j]?) ∧
      ∀ k < m, (∀ k', k < k' → k' < m → I k' ≠ I k) → I k < o.size → ws[I k]? = some (X k) := by
  intro step
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true, and_true]
    exact ⟨⟨o, rfl⟩, fun ws h => by obtain rfl : o = ws := Except.ok.inj h; exact ⟨rfl, fun _ _ => rfl⟩⟩
  | succ m ih =>
    obtain ⟨ihx, ihw⟩ := ih
    rw [List.range_succ, List.foldlM_append]
    cases h1 : (List.range m).foldlM step o with
    | error s =>
      refine ⟨⟨fun ⟨ws, h⟩ => (by simp [bind, Except.bind] at h), fun h => ?_⟩,
        fun ws h => (by simp [bind, Except.bind] at h)⟩
      obtain ⟨ws, hw⟩ := ihx.2 fun k hk => h k (by omega)
      rw [h1] at hw; cases hw
    | ok w =>
      obtain ⟨hs, hfix, hlast⟩ := ihw w h1
      have hall := ihx.1 ⟨w, h1⟩
      by_cases hm : I m < n
      · have he : ((Except.ok w : Except String _) >>= fun o' => [m].foldlM step o') =
            .ok (w.setIfInBounds (I m) (X m)) := by simp [bind, Except.bind, List.foldlM, step, hm]; rfl
        rw [he]
        refine ⟨⟨fun _ k hk => ?_, fun _ => ⟨_, rfl⟩⟩, fun ws h => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact hall k hk
          · exact hm
        · cases h
          refine ⟨by simp [hs], fun j hj => ?_, fun k hk hl hko => ?_⟩
          · rw [Array.getElem?_setIfInBounds_ne (hj m (by omega)), hfix j fun k hk => hj k (by omega)]
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · rw [Array.getElem?_setIfInBounds_ne (hl m hk (by omega)),
                hlast k hk (fun k' a b => hl k' a (by omega)) hko]
            · rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
      · have he : ((Except.ok w : Except String _) >>= fun o' => [m].foldlM step o') = .error (err m) := by
          simp [bind, Except.bind, List.foldlM, step, hm]
        rw [he]
        exact ⟨⟨fun ⟨_, h⟩ => (by cases h), fun h => absurd (h m (by omega)) hm⟩, fun _ h => (by cases h)⟩

/-- A row's index as `scatterWords` reads it. -/
private abbrev ixAt (is : Array UInt64) (k : Nat) : Nat := (is[k]?.getD 0).toNat

/-- `scatterWords` answers exactly when every index is below `n`; its `n` cells are `fill` where no row names them,
and `es[k]` at `is[k]` where no later row names the same cell. -/
theorem scatterWords_spec (is es : Array UInt64) (n : Nat) (fill : UInt64) :
    ((∃ ws, scatterWords .last is es n fill = .ok ws) ↔ ∀ k < is.size, ixAt is k < n) ∧
    ∀ ws, scatterWords .last is es n fill = .ok ws → ws.size = n ∧
      (∀ j < n, (∀ k < is.size, ixAt is k ≠ j) → ws[j]? = some fill) ∧
      ∀ k < is.size, (∀ k', k < k' → k' < is.size → ixAt is k' ≠ ixAt is k) →
        ws[ixAt is k]? = some (es[k]?.getD 0) := by
  obtain ⟨hx, hw⟩ := scatterFold (ixAt is) (fun k => es[k]?.getD 0) n
    (fun k => s!"scatter: index {is[k]?.getD 0} at row {k} is not below n = {n}") (Array.replicate n fill) is.size
  refine ⟨hx, fun ws h => ?_⟩
  obtain ⟨hs, hfix, hlast⟩ := hw ws h
  have hall := hx.1 ⟨ws, h⟩
  refine ⟨by simpa using hs, fun j hj hn => by rw [hfix j hn]; simp [hj], fun k hk hl => hlast k hk hl ?_⟩
  simpa using hall k hk

/-- What `foRWords` answers is `Enc.raw` at a 64-bit column, `m` words of it. -/
theorem foRWords_raw (what : String) (m : USize) (e : Enc) (ws : Array UInt64)
    (h : foRWords what m e = .ok ws) : ws = raw .i64 m e ∧ ws.size = m.toNat := by
  unfold foRWords at h
  split at h
  · cases h; refine ⟨rfl, ?_⟩; cases e <;> simp_all [raw, QAtomicType.width]
  · cases h

/-- Design §4's `scatter` law, on words: the `n` words `ws` `Enc.raw` reads from an answer of `kscatter`, against the
`m` words `is` and `es` it reads from `ix` and `e`: every index is below `n`, a cell no row names is `fill`, and
`ws[is[k]] = es[k]` for every row `k` no later row overrides. The answer is `foR`, `Coc.encode` of `ws` at 8 bytes. -/
theorem raw_scatter (m : USize) (ix e : Enc) (n : USize) (fill : UInt64) (o : Enc)
    (hnul : hasNul e = false) (h : kscatter .last m ix e n fill = .ok o) :
    let is := raw .i64 m ix
    let es := raw .i64 m e
    let ws := raw .i64 n o
    o = .foR (Coc.encode 8 (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)).1
      (Coc.encode 8 (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)).2 ∧
      is.size = m.toNat ∧ es.size = m.toNat ∧ ws.size = n.toNat ∧
      (∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat) ∧
      (∀ j < n.toNat, (∀ k < m.toNat, (is[k]?.getD 0).toNat ≠ j) → ws[j]? = some fill) ∧
      ∀ k < m.toNat, (∀ k', k < k' → k' < m.toNat → is[k']?.getD 0 ≠ is[k]?.getD 0) →
        ws[(is[k]?.getD 0).toNat]? = some (es[k]?.getD 0) := by
  intro is es ws'
  unfold kscatter at h
  cases hi : foRWords "scatter: ix" m ix with
  | error s => simp [hi, bind, Except.bind] at h
  | ok is' =>
    cases he : foRWords "scatter: e" m e with
    | error s => simp [hi, he, bind, Except.bind] at h
    | ok es' =>
      obtain ⟨rfl, hisz⟩ := foRWords_raw _ _ _ _ hi
      obtain ⟨rfl, hesz⟩ := foRWords_raw _ _ _ _ he
      have hn : noNul "scatter: ix" m ix = .ok () := by
        cases hn : noNul "scatter: ix" m ix with
        | error s => simp [hi, he, hn, bind, Except.bind] at h
        | ok u => rfl
      cases hw : scatterWords .last (raw .i64 m ix) (raw .i64 m e) n.toNat fill with
      | error s => simp [hi, he, hn, hw, bind, Except.bind, pure, Except.pure] at h
      | ok ws =>
        simp only [hi, he, hn, hw, hnul, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at h
        have h8 : USize.ofNat32 8 (by decide) = 8 := USize.toNat_inj.mp (by simp)
        rw [h8] at h
        obtain ⟨hx, hok⟩ := scatterWords_spec (raw .i64 m ix) (raw .i64 m e) n.toNat fill
        obtain ⟨hs, hfix, hlast⟩ := hok ws hw
        have hall := hx.1 ⟨ws, hw⟩
        have ho := (Except.ok.inj h).symm
        -- the answer reads back the words it packs
        obtain ⟨hxs, -, hxg⟩ := foldl_pushBits (fun v => v) 8 (by decide) ws.toList ByteArray.empty
        rw [Array.foldl_toList] at hxs hxg
        simp only [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Array.length_toList] at hxs hxg
        have hraw : ws' = ws := by
          show raw .i64 n o = ws
          have h88 : (8 : USize) = (8 : Nat).toUSize := rfl
          rw [ho, Coc.encode, h88, raw_encodeAt .i64 8 rfl (by decide) Column.lgEnc (by decide) _ n (by rw [hxs]; omega)]
          refine Array.ext (by simp [hs]) fun i h1 _ => ?_
          simp only [Array.getElem_map, Array.getElem_range]
          rw [Nat.mul_comm, hxg i (by simp at h1; omega), ofNat_toNat_mod64, Array.getElem_toList]
        rw [hraw]
        refine ⟨ho, hisz, hesz, hs, fun k hk => hall k (by omega), fun j hj hn => hfix j hj
          fun k hk => hn k (by omega), fun k hk hl => hlast k (by omega) fun k' a b hc => hl k' a (by omega) ?_⟩
        exact UInt64.toNat_inj.mp hc

/-- Law S1 (PLAN 6.13): scattering to the positions `ix = pos` at `m = n` writes every cell once, at its own row, so the
answer reads back as `e`: the identity is a permutation, and a caller holding `pos` skips the call. -/
theorem kscatter_pos_ix {n : USize} {e o : Enc} {fill : UInt64} (hnul : hasNul e = false)
    (h : kscatter .last n .pos e n fill = .ok o) :
    raw .i64 n o = raw .i64 n e := by
  obtain ⟨-, his, hes, hws, -, -, hlast⟩ := raw_scatter n .pos e n fill o hnul h
  have hm : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le n.toNat_lt_size USize.size_le
  -- row `k` of `pos` is `k`
  have hrow : ∀ k < n.toNat, ((raw .i64 n (.pos : Enc))[k]?.getD 0).toNat = k := fun k hk => by
    simp [raw, hk, Nat.mod_eq_of_lt (Nat.lt_trans hk hm)]
  apply Array.ext (by rw [hws, hes])
  intro j h1 h2
  have hj : j < n.toNat := by omega
  have hw := hlast j hj fun k' _ hk' hc => by have := congrArg UInt64.toNat hc; rw [hrow k' hk', hrow j hj] at this; omega
  rw [hrow j hj, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some] at hw
  exact Option.some.inj hw

/-- A fold whose every successful `step` names a cell `ix k` below `n` and combines `es k` into it by `f`: a successful
run over the rows `l` from `o` of `n` cells keeps the size, and cell `j` ends as `f` folded over `es k` for the rows `k`
of `l` naming `j`, in row order, from `o[j]`. -/
private theorem foldCells {f : UInt64 → UInt64 → UInt64} {ix : Nat → Nat} {es : Nat → UInt64} {n : Nat}
    {step : Array UInt64 → Nat → Except String (Array UInt64)}
    (hstep : ∀ o k o', step o k = .ok o' → ix k < n ∧ o' = o.setIfInBounds (ix k) (f (o[ix k]?.getD 0) (es k))) :
    ∀ (l : List Nat) (o ws : Array UInt64), o.size = n → l.foldlM step o = .ok ws →
      ws.size = n ∧ ∀ j, ws[j]?.getD 0 = ((l.filter fun k => ix k = j).map es).foldl f (o[j]?.getD 0)
  | [], o, ws, hs, h => by cases h; exact ⟨hs, fun j => by simp⟩
  | k :: l, o, ws, hs, h => by
    rw [List.foldlM_cons] at h
    cases h1 : step o k with
    | error s => rw [h1] at h; cases h
    | ok o1 =>
      rw [h1] at h
      obtain ⟨hk, rfl⟩ := hstep o k o1 h1
      obtain ⟨hs', hj⟩ := foldCells hstep l _ ws (by simp [hs]) h
      refine ⟨hs', fun j => ?_⟩
      rw [hj j]
      by_cases e : ix k = j
      · subst e
        rw [Array.getElem?_setIfInBounds_self_of_lt (hs ▸ hk)]
        simp
      · rw [Array.getElem?_setIfInBounds_ne e]
        simp [e]

/-- **`scatter` under an `op` whose `eval` is the total `f` is a per-cell fold** (design §4: `out[ix[k]] := op(out[ix[k]],
e[k])` in row order): a successful run holds `n` cells, cell `j` being `f` folded over `es[k]` for the rows `k` naming
`j`, in row order, from `fill`. `.add`, `.mul`, `.and`, `.or`, `.min`, `.max`, `.first` and `.last` are instances
(`hf` by `rfl`); `.last` folds to the last row naming `j`, or `fill`. -/
theorem scatterWords_fold {op : Op} {f : UInt64 → UInt64 → UInt64} (hf : ∀ a x, op.eval a x = .ok (f a x))
    {is es ws : Array UInt64} {n : Nat} {fill : UInt64} (h : scatterWords op is es n fill = .ok ws) :
    ws.size = n ∧ ∀ j < n, ws[j]?.getD 0 =
      (((List.range is.size).filter fun k => (is[k]?.getD 0).toNat = j).map (es[·]?.getD 0)).foldl f fill := by
  unfold scatterWords at h
  obtain ⟨hs, hj⟩ := foldCells (f := f) (ix := fun k => (is[k]?.getD 0).toNat) (es := (es[·]?.getD 0))
    (fun o k o' h => by
      dsimp only at h
      split at h
      · rename_i hk; simp only [hf, Except.ok.injEq] at h; exact ⟨hk, h.symm⟩
      · cases h) _ _ ws (by simp) h
  exact ⟨hs, fun j hjn => by rw [hj j]; simp [hjn]⟩


end Rel.Verify
