import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Chain` the Rel kernels reach; `Rel.Verify.Chain` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel

theorem stage_bytes_size (s : Ew.Stage) : s.bytes.size = Ew.stageBytes := by
  simp [Ew.Stage.bytes, Column.pushBits_size, ba_size_push, Ew.stageBytes]

/-- A left fold of `++` over records of one size `m`: its size, the prefix untouched, and byte `j` of
record `k` at `m * k + j` past the prefix. -/
theorem foldl_append_get (m : Nat) (L : List ByteArray) (hL : ∀ x ∈ L, x.size = m) (a : ByteArray) :
    (L.foldl (· ++ ·) a).size = a.size + m * L.length ∧
    (∀ i < a.size, (L.foldl (· ++ ·) a)[i]? = a[i]?) ∧
    ∀ k (hk : k < L.length), ∀ j < m, (L.foldl (· ++ ·) a)[a.size + (m * k + j)]? = L[k][j]? := by
  induction L generalizing a with
  | nil => exact ⟨by simp, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    obtain ⟨hs, hp, hg⟩ := ih (fun y hy => hL y (by simp [hy])) (a ++ x)
    have hax : (a ++ x).size = a.size + m := by rw [ByteArray.size_append, hx]
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨by rw [hs, hax, Nat.mul_succ]; omega,
      fun i hi => by rw [hp i (by omega), ba_append_left _ _ _ hi], fun k hk j hj => ?_⟩
    cases k with
    | zero =>
      rw [hp _ (by omega), Nat.mul_zero, Nat.zero_add, ba_append_right, List.getElem_cons_zero]
    | succ k =>
      rw [List.getElem_cons_succ, ← hg k (by simp at hk; omega) j hj, hax,
        show a.size + (m * (k + 1) + j) = a.size + m + (m * k + j) by rw [Nat.mul_succ]; omega]

/-- A one-byte read is the byte. -/
theorem bitsAt_one (b : ByteArray) (o : Nat) : Column.bitsAt b o 1 = (b[o]?.getD 0).toUInt64 := by
  rw [Column.bitsAt_succ]; simp [Column.bitsAt]

/-- One record read back at its own start. -/
theorem stageAt_bytes (s : Ew.Stage) : Ew.stageAt s.bytes 0 = s := by
  obtain ⟨e, op, cls, sh, a, b, c, nul, nulOut⟩ := s
  let head := ((((((((ByteArray.empty.push e).push op).push cls).push sh).push a).push b).push c).push 0)
  have hh : head.size = 8 := rfl
  have h1 : ∀ i < 8, (Ew.Stage.bytes ⟨e, op, cls, sh, a, b, c, nul, nulOut⟩)[i]? = head[i]? := fun i hi => by
    show (Column.pushBits (Column.pushBits head nul.toUInt64 8) nulOut.toUInt64 8)[i]? = _
    rw [Column.pushBits_getElem?_lt _ _ _ _ (by rw [Column.pushBits_size]; omega),
      Column.pushBits_getElem?_lt _ _ _ _ (by omega)]
  have hn : Column.bitsAt (Ew.Stage.bytes ⟨e, op, cls, sh, a, b, c, nul, nulOut⟩) 8 8 = nul.toUInt64 := by
    show Column.bitsAt (Column.pushBits (Column.pushBits head nul.toUInt64 8) nulOut.toUInt64 8) 8 8 = _
    rw [bitsAt_shift _ (Column.pushBits head nul.toUInt64 8) 8 8 8
      (fun k hk => Column.pushBits_getElem?_lt _ _ _ _ (by rw [Column.pushBits_size, hh]; omega))]
    have := bitsAt_pushBits8 head nul.toUInt64
    rwa [hh] at this
  have ho : Column.bitsAt (Ew.Stage.bytes ⟨e, op, cls, sh, a, b, c, nul, nulOut⟩) 16 8 = nulOut.toUInt64 := by
    show Column.bitsAt (Column.pushBits (Column.pushBits head nul.toUInt64 8) nulOut.toUInt64 8) 16 8 = _
    have := bitsAt_pushBits8 (Column.pushBits head nul.toUInt64 8) nulOut.toUInt64
    rw [Column.pushBits_size, hh] at this
    exact this
  simp only [Ew.stageAt, Nat.zero_mul, Nat.zero_add, Ew.stageBytes, hn, ho, bitsAt_one,
    h1 0 (by omega), h1 1 (by omega), h1 2 (by omega), h1 3 (by omega), h1 4 (by omega),
    h1 5 (by omega), h1 6 (by omega)]
  simp only [head, Ew.Stage.mk.injEq]
  simp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The program a build writes gives every stage back**: `stageAt` at `k` reads the `k`-th of the
build's stages with the last one after them. -/
theorem stageAt_prog (b : Ew.Build) (last : Ew.Stage) (k : Nat) (hk : k < b.stages.size + 1) :
    Ew.stageAt (b.prog last) k = (b.stages.push last)[k]'(by simpa using hk) := by
  let L := (b.stages.push last).toList.map Ew.Stage.bytes
  have hL : ∀ x ∈ L, x.size = Ew.stageBytes := fun x hx => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx; exact stage_bytes_size s
  have hp : b.prog last = L.foldl (· ++ ·) ByteArray.empty := by
    simp only [Ew.Build.prog, L, ← Array.foldl_toList, Array.toList_map]
  have hkL : k < L.length := by simpa [L] using hk
  obtain ⟨-, -, hg⟩ := foldl_append_get Ew.stageBytes L hL ByteArray.empty
  have hr : ∀ o w, o + w ≤ Ew.stageBytes →
      Column.bitsAt (b.prog last) (k * Ew.stageBytes + o) w =
        Column.bitsAt ((b.stages.push last)[k]'(by simpa using hk)).bytes o w := fun o w hw =>
    bitsAt_shift _ _ _ _ _ fun j hj => by
      have := hg k hkL (o + j) (by omega)
      rw [ByteArray.size_empty, Nat.zero_add] at this
      rw [hp, show k * Ew.stageBytes + o + j = Ew.stageBytes * k + (o + j) by rw [Nat.mul_comm]; omega,
        this, List.getElem_map, Array.getElem_toList]
  conv => rhs; rw [← stageAt_bytes ((b.stages.push last)[k]'(by simpa using hk))]
  simp only [Ew.stageAt, Nat.zero_mul, Nat.zero_add]
  have h0 := hr 0 1 (by decide)
  rw [Nat.add_zero] at h0
  rw [h0, hr 1 1 (by decide), hr 2 1 (by decide), hr 3 1 (by decide),
    hr 4 1 (by decide), hr 5 1 (by decide), hr 6 1 (by decide), hr 8 8 (by decide),
    hr 16 8 (by decide)]

/-- A build with no stage of its own writes a one-stage program, and that stage is `last`. -/
theorem prog_one (b : Ew.Build) (hb : b.stages = #[]) (last : Ew.Stage) :
    (b.prog last).size / Ew.stageBytes = 1 ∧ Ew.stageAt (b.prog last) 0 = last := by
  refine ⟨?_, by rw [stageAt_prog b last 0 (by simp [hb])]; simp [hb]⟩
  have hL : ∀ x ∈ (b.stages.push last).toList.map Ew.Stage.bytes, x.size = Ew.stageBytes := fun x hx => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx; exact stage_bytes_size s
  have hs := (foldl_append_get Ew.stageBytes _ hL ByteArray.empty).1
  have hp : b.prog last = ((b.stages.push last).toList.map Ew.Stage.bytes).foldl (· ++ ·) ByteArray.empty := by
    simp only [Ew.Build.prog, ← Array.foldl_toList, Array.toList_map]
  rw [hp, hs]; simp [hb, Ew.stageBytes]

/-- **A one-stage value chain is `Ew.val` over the two input payloads it names.** -/
theorem run_val (b : Ew.Build) (hb : b.stages = #[]) (op cls shape sa sb : UInt8) (nul : Int64)
    (ha : sa < Ew.slot0) (hb' : sb < Ew.slot0) (n : USize) :
    b.run { engine := Ew.eVal, op, cls, shape, a := sa, b := sb, nul } n =
      Ew.val op cls shape nul b.inputs[sa.toNat]! b.inputs[sb.toNat]! n := by
  obtain ⟨hk, h0⟩ := prog_one b hb { engine := Ew.eVal, op, cls, shape, a := sa, b := sb, nul }
  simp only [Ew.Build.run, Ew.chain, hk, show List.range 1 = [0] from rfl, List.foldl_cons, List.foldl_nil]
  rw [h0]
  simp [ha, hb']

/-- **A one-stage comparison chain is `Ew.cmp` over the two input payloads it names**, whose bits
`cmp_bitAt` reads. -/
theorem run_cmp (b : Ew.Build) (hb : b.stages = #[]) (op cls shape sa sb : UInt8) (nul : Int64)
    (ha : sa < Ew.slot0) (hb' : sb < Ew.slot0) (n : USize) :
    b.run { engine := Ew.eCmp, op, cls, shape, a := sa, b := sb, nul } n =
      Ew.cmpBitmap op cls shape b.inputs[sa.toNat]! b.inputs[sb.toNat]! n := by
  obtain ⟨hk, h0⟩ := prog_one b hb { engine := Ew.eCmp, op, cls, shape, a := sa, b := sb, nul }
  simp only [Ew.Build.run, Ew.chain, hk, show List.range 1 = [0] from rfl, List.foldl_cons, List.foldl_nil]
  rw [h0]
  simp [ha, hb', Ew.eCmp, Ew.eVal]

theorem width_pos_le (cls : UInt8) : 0 < Ew.width cls ∧ Ew.width cls ≤ 8 := by
  unfold Ew.width; repeat' split
  all_goals omega

/-- **`Ew.val`'s elements**: element `i` of its answer is `valStep` on the two elements the shape reads
at `i`, on the low `8 * width cls` bits the payload holds. -/
theorem elemsW_val (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    elemsW (Ew.width cls) (Ew.val op cls shape nul a b n) = (List.range n.toNat).map fun i =>
      UInt64.ofNat ((Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1)
        (Ew.elem cls b (Ew.shapeIdx shape i).2)).toNat % 2 ^ (8 * Ew.width cls)) := by
  obtain ⟨hw0, hw8⟩ := width_pos_le cls
  let g : Nat → UInt64 := fun i =>
    Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2)
  have hf : Ew.val op cls shape nul a b n =
      (List.range n.toNat).foldl (fun acc i => Column.pushBits acc (g i) (Ew.width cls)) ByteArray.empty := rfl
  obtain ⟨hs, -, hg⟩ := foldl_pushBits g (Ew.width cls) hw8 (List.range n.toNat) ByteArray.empty
  rw [hf, elemsW, hs, ByteArray.size_empty, Nat.zero_add, List.length_range, Nat.mul_div_cancel_left _ hw0]
  apply List.map_congr_left
  intro i hi
  have := hg i (by simpa using hi)
  rw [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at this
  rw [Nat.mul_comm, this]

end Rel.Verify

/-- info: 'Rel.Verify.stageAt_prog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.stageAt_prog

-- `Classical.choice` is the statement's: `Ew.val` names `valStep`, which names `f64Step` and so
-- `Float.ofBits`, an opaque whose `Inhabited` witness is choice; the proof adds none.
/-- info: 'Rel.Verify.run_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.run_val

/-- info: 'Rel.Verify.run_cmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.run_cmp

/-- info: 'Rel.Verify.elemsW_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.elemsW_val

/-- info: 'Rel.Verify.prog_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Verify.prog_one
