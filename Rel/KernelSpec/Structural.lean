import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.KernelSpec.Distinct
import Rel.Kernel.Structural
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Structural` the Rel kernels reach; `Rel.Verify.Structural` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel

/-- A `copySlice` that fits both arrays: `len` bytes of `src` from `so` at `d`, `dst` everywhere else. -/
theorem copySlice_getElem? (src dst : ByteArray) (so d len j : Nat) (hd : d + len ≤ dst.size)
    (hs : so + len ≤ src.size) :
    (src.copySlice so dst d len)[j]? =
      if d ≤ j then if j < d + len then src[so + (j - d)]? else dst[j]? else dst[j]? := by
  have hd' : d + len ≤ dst.data.size := hd
  have hs' : so + len ≤ src.data.size := hs
  show (dst.data.extract 0 d ++ src.data.extract so (so + len) ++
      dst.data.extract (d + min len (src.data.size - so)) dst.data.size)[j]? =
    if d ≤ j then if j < d + len then src.data[so + (j - d)]? else dst.data[j]? else dst.data[j]?
  rw [Nat.min_eq_left (by omega)]
  simp only [Array.getElem?_append, extract_getElem?, Array.size_append, Array.size_extract]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (congr 1; omega) | exact (Array.getElem?_eq_none (by omega)).symm

/-- A fold of writes, each replacing at most element `u k` by `val k` and keeping the size: element `i` of
the answer is the value of the last write naming `i`, or the start's own. Elements are read by `read`, and an
array of `size` `s` holds `N s` of them: whole bytes (`bitsAt`), fields within a byte (`resAt`) and the slots of an
`Array` (`getElem?`) alike. -/
theorem foldl_lastWrite {σ β : Type} (size : σ → Nat) (N : Nat → Nat) (read : σ → Nat → β) (step : σ → Nat → σ)
    (u : Nat → Nat) (val : Nat → β) (L : List Nat) (hsz : ∀ acc k, size (step acc k) = size acc)
    (hel : ∀ acc, ∀ k ∈ L, ∀ i < N (size acc), read (step acc k) i = if u k = i then val k else read acc i)
    (acc : σ) :
    size (L.foldl step acc) = size acc ∧ ∀ i < N (size acc), read (L.foldl step acc) i =
      match (L.filter (u · == i)).getLast? with | some k => val k | none => read acc i := by
  induction L generalizing acc with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons k L ih =>
    have hs1 := hsz acc k
    obtain ⟨hs, he⟩ := ih (fun acc k hk => hel acc k (List.mem_cons_of_mem _ hk)) (step acc k)
    refine ⟨by rw [List.foldl_cons, hs, hs1], fun i hi => ?_⟩
    rw [List.foldl_cons, he i (by rw [hs1]; exact hi), hel acc k List.mem_cons_self i hi, List.filter_cons]
    by_cases hk : u k = i
    · rw [if_pos hk, if_pos (beq_iff_eq.2 hk), List.getLast?_cons]
      cases (L.filter (u · == i)).getLast? <;> rfl
    · rw [if_neg hk, if_neg (fun h => hk (beq_iff_eq.1 h))]


/-- The nested fold `expandBytes` runs, each `i` writing its value `c i` times, is one fold over the
values each repeated. -/
theorem foldl_replicate (w : Nat) (c : Nat → Nat) (v : Nat → UInt64) (L : List Nat) (acc : ByteArray) :
    L.foldl (fun acc i => (Array.range (c i)).foldl (init := acc) fun acc _ => Column.pushBits acc (v i) w) acc =
      (L.flatMap fun i => List.replicate (c i) (v i)).foldl (fun acc x => Column.pushBits acc x w) acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, List.foldl_append, ← Array.foldl_toList, toList_range,
      show List.replicate (c i) (v i) = (List.range (c i)).map fun _ => v i by rw [List.map_const', List.length_range], List.foldl_map]


/-- **`tilLongs` is `til n`**: read back as eight-byte elements, the answer is `0, 1, …, n - 1`. -/
theorem tilLongs_spec (n : USize) : (elemsW 8 (tilLongs n)).map UInt64.toNat = List.range n.toNat := by
  unfold tilLongs
  rw [elemsW_foldl (fun i => (Int64.ofNat i).toUInt64) 8 (by decide) (by decide) _ (fun e _ => UInt64.toNat_lt _),
    List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.length_range] at h2
  simp only [List.getElem_map, List.getElem_range, Function.comp]
  rw [show (Int64.ofNat j).toUInt64 = UInt64.ofNat j from rfl, UInt64.toNat_ofNat_of_lt' (by have := usize_lt n; exact Nat.lt_trans h2 this)]

end Rel.Verify

#print axioms Rel.Verify.tilLongs_spec
