module

public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Coc
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Alp` the Rel kernels reach; `Rel.Verify.Alp` imports it. -/


namespace Rel.Verify

open Rel









/-- `Coc.encode`'s block count, the one `Column.alpSects` is laid out by. -/
theorem nblk_encode (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray)
    {patch : Bool} {nul : ByteArray} :
    Column.nblk (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1 = (x.size / w + 2 ^ lg - 1) / 2 ^ lg ∧
      Column.blk (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1 = 2 ^ lg ∧
      Column.lgAt (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1 = lg := by
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  unfold Kernel.Coc.encodeAt
  simp only [hwt, Nat.one_shiftLeft]
  generalize x.size / w = n
  have hd := fun b => planBlock_byte lg w n (patch && decide (n < 2 ^ 64)) x nul b
  generalize (patch && decide (n < 2 ^ 64)) = pl at hd ⊢
  generalize Kernel.Coc.planBlock lg w n pl x nul = blk at hd ⊢
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    ((Array.map blk (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg))).map fun x =>
      (x.1.toUInt64, x.2.1.toUInt64, x.2.2.1, x.2.2.2.2)) (fun b h => by
      simp only [Array.size_map, Array.size_range] at h
      simp only [Array.getElem_map, getElem_range]
      exact Nat.lt_of_le_of_lt (hd b (mul_lt_of_lt_cdiv (Nat.two_pow_pos lg) h)).1 (by decide))
  exact ⟨by rw [hMr.1]; simp, by rw [blk_of_lgAt _ (by rw [hMr.2.1]; exact hlg), hMr.2.1], hMr.2.1⟩

/-- A column encoded with no null bitmap flags no block (`nulAt_encodeAt`). -/
theorem nulAt_encodeAt_empty (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw0 : 0 < w) (hw : w ≤ 8) (x : ByteArray)
    {patch : Bool} (b : Nat) (hb : b < Column.nblk (Kernel.Coc.encodeAt lg w.toUSize x patch).1) :
    Column.nulAt (Kernel.Coc.encodeAt lg w.toUSize x patch).1 b = false := by
  rw [(nblk_encode lg hlg w hw0 hw x (nul := .empty)).1] at hb
  cases h : Column.nulAt (Kernel.Coc.encodeAt lg w.toUSize x patch).1 b
  · rfl
  · obtain ⟨j, -, -, hj⟩ := nulAt_encodeAt lg hlg w hw0 hw x .empty b (mul_lt_of_lt_cdiv (Nat.two_pow_pos _) hb) h
    rw [bitAt_empty] at hj; cases hj

/-- What the writers guarantee of a Frame-of-Reference column of `n` elements: one block per started
`blk` elements, a pack ending where its last block's residuals do or where the patch list its header
declares does, and no width past 64. -/
structure FoRWF (n : Nat) (md pk : ByteArray) : Prop where
  nblk : Column.nblk md = (n + Column.blk md - 1) / Column.blk md
  size : pk.size = Column.blockStart md (Column.nblk md)
    ∨ (Kernel.Coc.foRTail (Column.nblk md) pk (Column.blockStart md (Column.nblk md))).map
        (Column.blockStart md (Column.nblk md) + ·) = some pk.size
  width : ∀ b < Column.nblk md, Column.widthAt md b ≤ 64

end Rel.Verify


namespace Rel.Verify

open Rel

/-- **The runtime test is the writer's form**: `Kernel.Coc.foRStd` is `FoRWF`. -/
theorem foRStd_iff {n : USize} {md pk : ByteArray} : Kernel.Coc.foRStd n md pk = true ↔ FoRWF n.toNat md pk := by
  simp only [Kernel.Coc.foRStd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- **What the encoder writes is the writers' form**, at every element width a kernel is instantiated at and every
block size the layout admits, patched or not: the codec's half of the closure law, a column the codec answers is one
every kernel that reads `foR` through `Coc.foRStd` accepts. -/
theorem foRWF_encodeAt (lg : Nat) (hlg : 6 ≤ lg ∧ lg ≤ 16) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (x : ByteArray) {patch : Bool} {nul : ByteArray} :
    FoRWF (x.size / w) (Kernel.Coc.encodeAt lg w.toUSize x patch nul).1 (Kernel.Coc.encodeAt lg w.toUSize x patch nul).2 := by
  have hw0 : 0 < w := by omega
  have hw8 : w ≤ 8 := by omega
  have hwt : w.toUSize.toNat = w := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize, h] <;> omega
  have hBp : 0 < 2 ^ lg := Nat.two_pow_pos _
  have hB16 : 2 ^ lg ≤ 65536 := Nat.pow_le_pow_right (by decide) hlg.2
  unfold Kernel.Coc.encodeAt
  simp only [hwt, Nat.one_shiftLeft]
  generalize x.size / w = n
  have hd := fun b => planBlock_byte lg w n (patch && decide (n < 2 ^ 64)) x nul b
  have hin := fun j => planBlock_inside lg w n (patch && decide (n < 2 ^ 64)) x nul j
  have h64 : (patch && decide (n < 2 ^ 64)) = true → n < 2 ^ 64 := fun h => by simp at h; exact h.2
  generalize (patch && decide (n < 2 ^ 64)) = pl at hd hin h64 ⊢
  generalize hlst : decide (n < 2 ^ 64) = lst
  generalize Kernel.Coc.planBlock lg w n pl x nul = blk at hd hin ⊢
  generalize hbs : Array.map blk (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)) = bs
  have hbsz : bs.size = (n + 2 ^ lg - 1) / 2 ^ lg := by rw [← hbs]; simp
  have hbget : ∀ b (h : b < bs.size), bs[b] = blk b := by
    intro b h; subst hbs; simp only [Array.getElem_map, getElem_range]
  have hMr := foRMeta_reads lg (Nat.lt_of_le_of_lt hlg.2 (by decide)) (Kernel.Coc.sumNul w) n
    (bs.map fun x => (x.1.toUInt64, x.2.1.toUInt64, x.2.2.1, x.2.2.2.2)) (fun b h => by
      simp only [Array.size_map] at h; simp only [Array.getElem_map]; rw [hbget b h]
      exact Nat.lt_of_le_of_lt (hd b (mul_lt_of_lt_cdiv hBp (hbsz ▸ h))).1 (by decide))
  generalize Kernel.Coc.foRMeta lg (Kernel.Coc.sumNul w) n _ = M at hMr ⊢
  obtain ⟨hnb, hlgM, hMb⟩ := hMr
  have hBM : Column.blk M = 2 ^ lg := by rw [blk_of_lgAt M ⟨hlgM ▸ hlg.1, hlgM ▸ hlg.2⟩, hlgM]
  simp only [Array.size_map] at hnb hMb
  have hbg : ∀ j < n, bs.getD (j / 2 ^ lg) default = blk (j / 2 ^ lg) := fun j hj => by
    have h : j / 2 ^ lg < bs.size := hbsz ▸ lt_cdiv hBp hj
    unfold Array.getD; rw [dif_pos h]; exact hbget _ h
  generalize hexc : Array.filter (fun i => !Column.bitAt nul i && Kernel.Coc.patched lst
      (bs.getD (i / 2 ^ lg) default).2.2.2.1 (bs.getD (i / 2 ^ lg) default).2.2.2.2 (Kernel.Coc.keyAt w x i))
      (Array.range n) = exc
  -- a patch list is written only with patching on, so below `2 ^ 64` elements
  have h64e : exc.size ≠ 0 → exc.size < 2 ^ 64 := fun h => by
    have hen : exc.size ≤ n := by
      rw [← hexc, ← Array.length_toList, Array.toList_filter, Array.toList_range]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    by_cases hn64 : n < 2 ^ 64
    · exact Nat.lt_of_le_of_lt hen hn64
    · have hpl : pl = false := by cases hp : pl; rfl; exact absurd (h64 hp) hn64
      -- by cases on the list, not `List.eq_nil_iff_forall_not_mem`, which carries `Classical.choice`
      have he : exc.toList = [] := by
        cases hl : exc.toList with
        | nil => rfl
        | cons j t =>
          have hj : j ∈ exc.toList := hl ▸ List.mem_cons_self
          rw [← hexc, Array.toList_filter, Array.toList_range, List.mem_filter, List.mem_range] at hj
          have h2 := hj.2
          simp only [Kernel.Coc.patched, ← hlst, decide_eq_false hn64, Bool.false_and, Bool.or_false] at h2
          rw [hbg j hj.1, hin j hj.1 hpl] at h2; exact absurd h2 Bool.false_ne_true
      exact absurd (by rw [← Array.length_toList, he]; rfl) h
  have hfsz : (Array.map (fun x : Int64 × Int64 × UInt64 × Int64 × Nat => (x.2.2.2.1 - x.1).toUInt64) bs).size =
      Column.nblk M := by simp [hnb]
  generalize Array.map (fun x : Int64 × Int64 × UInt64 × Int64 × Nat => (x.2.2.2.1 - x.1).toUInt64) bs = fs at hfsz ⊢
  generalize (fs.any fun a => a != 0) = frm
  have hQ := pack_blockStart M (2 ^ lg) hBM bs (·.2.2.2.2 % 128) hnb (fun c h => by rw [Column.widthAt, (hMb c h).2]; simp)
    (fun (a : ByteArray × Nat) (e : Int64 × Int64 × UInt64 × Int64 × Nat) =>
      (a.1 ++ Kernel.Coc.packRes (2 ^ lg) (e.2.2.2.2 % 128) fun j =>
        if (decide (a.2 * 2 ^ lg + j < n) && Column.bitAt nul (a.2 * 2 ^ lg + j)) = true then
          Column.ones (e.2.2.2.2 % 128) else (if (decide (a.2 * 2 ^ lg + j < n) &&
        !Kernel.Coc.patched lst e.2.2.2.1 e.2.2.2.2 (Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (a.2 * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64, a.2 + 1))
    (fun m (e : Int64 × Int64 × UInt64 × Int64 × Nat) j =>
      if (decide (m * 2 ^ lg + j < n) && Column.bitAt nul (m * 2 ^ lg + j)) = true then
        Column.ones (e.2.2.2.2 % 128) else (if (decide (m * 2 ^ lg + j < n) && !Kernel.Coc.patched lst e.2.2.2.1 e.2.2.2.2
        (Kernel.Coc.keyAt w x (m * 2 ^ lg + j))) = true then
        Kernel.Coc.keyAt w x (m * 2 ^ lg + j) - e.2.2.2.1 else 0).toUInt64)
    (fun a m e => rfl)
  generalize (Array.foldl _ (ByteArray.empty, 0) bs).1 = pack at hQ ⊢
  refine ⟨by rw [hnb, hbsz, hBM], ?_, fun b hb => ?_⟩
  · split
    · left; rw [ByteArray.size_append, ← hQ.1]; rfl
    · next h0 =>
      right
      have hlast : (fs.foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v 8).size = 8 * bs.size := by
        rw [← Array.foldl_toList, (foldl_pushBits (fun v => v) 8 (by decide) fs.toList ByteArray.empty).1,
          Array.length_toList, hfsz, hnb]; simp
      obtain ⟨hc, hwd, -, -, -, -, -, hsz⟩ := excBlob_reads (w.toUInt64 ||| if frm = true then 256 else 0) (2 ^ lg)
        ⟨hBp, hB16⟩ w hw8 bs.size x exc
        (if frm = true then fs.foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v 8 else ByteArray.empty)
        (h64e h0) _ pack.size (fun k _ => ba_append_right _ _ _)
      have hW : ([1, 2, 4, 8].contains ((w.toUInt64 ||| if frm = true then 256 else 0).toNat % 256) &&
          decide ((w.toUInt64 ||| if frm = true then 256 else 0).toNat < 512)) = true ∧
          (w.toUInt64 ||| if frm = true then 256 else 0).toNat % 256 = w ∧
          (if (w.toUInt64 ||| if frm = true then 256 else 0).toNat < 256 then 0 else 8 * bs.size) =
            if frm = true then 8 * bs.size else 0 := by
        rcases hw with rfl | rfl | rfl | rfl <;> cases frm <;>
          exact ⟨by decide +kernel, by decide +kernel, by split <;> first | rfl | exact absurd ‹_› (by decide +kernel)⟩
      rw [← hQ.1, hnb]
      unfold Kernel.Coc.foRTail
      rw [hwd, hc, if_pos hW.1, Option.map_some, hW.2.1, hW.2.2, ByteArray.size_append, hsz]
      cases frm
      · simp
      · simp only [↓reduceIte, hlast]; rw [show (8 * bs.size + 7) / 8 * 8 = 8 * bs.size by omega]
  · rw [Column.widthAt, (hMb b (hnb ▸ hb)).2]; simp only [Array.getElem_map]; rw [hbget b (hnb ▸ hb)]
    exact (hd b (mul_lt_of_lt_cdiv hBp (hbsz ▸ hnb ▸ hb))).2

end Rel.Verify
