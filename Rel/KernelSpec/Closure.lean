import Rel.KernelSpec.Alp
import Rel.KernelSpec.Scatter
import Rel.KernelSpec.KGather

/-! The closure law (PLAN 6.14): a column the codec or a kernel answers is a column every kernel accepts. `Enc.Valid`
is what `foRWords` checks before it reads a `foR` or `pos` argument (`kscatter`, `kgather`, `kasc` and through it
`kseen`); the codec's answer satisfies it (`encode8_valid`, from `Verify.foRWF_encodeAt`), and so does each kernel's
answer, every one a `Coc.encode` at 8 bytes. A composition's success is then a chain of these laws. -/

namespace Rel.Kernel
open Ext.Enc

/-- The arguments `foRWords` reads at `n` rows: a `foR` column in the writers' layout (`Coc.foRStd`) with a stored `lg`
the layout admits, or `pos`. -/
def Enc.Valid (n : USize) : Enc → Prop
  | .foR md pk => Column.lgOk md = true ∧ Coc.foRStd n md pk = true
  | .pos => True
  | _ => False

end Rel.Kernel

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- **The reader accepts a valid column**: `foRWords` answers its raw words. -/
theorem foRWords_valid (what : String) {m : USize} {e : Enc} (h : Enc.Valid m e) :
    foRWords what m e = .ok (raw .i64 m e) := by
  unfold foRWords
  cases e <;> simp_all [Enc.Valid]

/-- **The codec's answer is valid**: `Coc.encode` at 8 bytes of `x`, at the `x.size / 8` rows it holds. -/
theorem encode8_valid (x : ByteArray) {n : USize} (hn : n.toNat = x.size / 8) :
    Enc.Valid n (.foR (Coc.encode 8 x).1 (Coc.encode 8 x).2) := by
  have hlg : 6 ≤ Column.lgEnc ∧ Column.lgEnc ≤ 16 := ⟨by decide, by decide⟩
  have hl := (nblk_encode Column.lgEnc hlg 8 (by decide) (by decide) x (patch := true)).2.2
  refine ⟨by unfold Column.lgOk; rw [show (8 : USize) = (8 : Nat).toUSize from rfl]; simp [Coc.encode, hl, Column.lgEnc],
    foRStd_iff.2 (hn ▸ foRWF_encodeAt Column.lgEnc hlg 8 (by decide) x)⟩

/-- **A kernel's answer is valid**: `wordsFoR` of `ws`, which every kernel answers, at its `ws.size` rows. -/
theorem wordsFoR_valid (ws : Array UInt64) {n : USize} (hn : n.toNat = ws.size) : Enc.Valid n (wordsFoR ws) := by
  have hx := (foldl_pushBits (fun v => v) 8 (by decide) ws.toList ByteArray.empty).1
  rw [Array.foldl_toList] at hx
  exact encode8_valid _ (by rw [hx, Array.length_toList, hn]; show ws.size = (0 + 8 * ws.size) / 8; omega)

/-- `scatterWords` answers its `n` cells. -/
theorem scatterWords_size {op : Op} {is es : Array UInt64} {n : Nat} {fill : UInt64} {o : Array UInt64}
    (h : scatterWords op is es n fill = .ok o) : o.size = n := by
  unfold scatterWords at h
  generalize List.range is.size = l at h
  have ha : (Array.replicate n fill).size = n := by simp
  generalize Array.replicate n fill = a at h ha
  induction l generalizing a with
  | nil => cases h; exact ha
  | cons k t ih =>
    rw [List.foldlM_cons] at h
    dsimp only at h
    split at h
    · split at h
      · exact ih _ h (by simp [ha])
      · cases h
    · cases h

/-- `kscatter`'s answer is valid at its `n` cells. -/
theorem kscatter_valid {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64}
    (h : kscatter op m ix e n fill = .ok o) : Enc.Valid n o := by
  unfold kscatter at h
  cases h1 : foRWords "scatter: ix" m ix <;> simp only [h1, bind, Except.bind] at h
  · cases h
  cases h2 : foRWords "scatter: e" m e <;> simp only [h2] at h
  · cases h
  cases h3 : scatterWords op _ _ n.toNat fill <;> simp only [h3] at h
  · cases h
  cases h
  exact wordsFoR_valid _ (scatterWords_size h3).symm

/-- `kgather`'s answer is valid at its `m` rows. -/
theorem kgather_valid {m n : USize} {ix e o : Enc} (h : kgather m ix n e = .ok o) : Enc.Valid m o := by
  obtain ⟨hs, -, -, rfl⟩ := raw_kgather m ix n e o h
  exact wordsFoR_valid _ (by simp [hs])

end Rel.Verify
