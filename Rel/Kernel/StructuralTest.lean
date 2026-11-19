import Rel.Kernel.Coc
import Rel.Kernel.Structural
import Rel.Kernel.Value

/-! The part of `Rel.Kernel.StructuralTest` the Rel kernels reach; `Rel.Kernel.StructuralTest` imports it. -/


namespace Rel.Kernel.StructuralTest

open Rel Rel.Kernel

-- part 0 holds no element and one block: copying that block would read `[5]` where the join is `[7]`
def extraBlk : Array ((USize × ByteArray) × ByteArray) :=
  #[((0, Coc.foRMeta Rel.Column.lgEnc 0 0 #[(5, 5, 0, 0)]), .empty), ((1, Coc.foRMeta Rel.Column.lgEnc 0 0 #[(7, 7, 0, 0)]), .empty)]
#guard (moveFoR extraBlk).isNone
-- part 0's pack is empty where its width needs 1024 bytes, so it reads its base; joining the packs
-- whole would read part 1's residual 3 as part 0's element 0 and part 1's element as its base
def shortPack : Array ((USize × ByteArray) × ByteArray) :=
  #[((1024, Coc.foRMeta Rel.Column.lgEnc 0 0 #[(5, 260, 0, 8)]), .empty),
    ((1, Coc.foRMeta Rel.Column.lgEnc 0 0 #[(7, 10, 0, 8)]), ⟨(Array.replicate 1024 0).set! 0 3⟩)]
#guard (moveFoR shortPack).isNone
-- `reverse` of a full block with a second block past the count: moving would put the 9s first
def extraRev : ByteArray := Coc.foRMeta Rel.Column.lgEnc 0 0 #[(5, 5, 0, 0), (9, 9, 0, 0)]
-- the scatter and the enumeration walk the source's blocks: two past the count wrapped the C's
-- block length, so the walk overran its buffer
def extraTwo : ByteArray := Coc.foRMeta Rel.Column.lgEnc 0 0 #[(5, 5, 0, 0), (9, 9, 0, 0), (9, 9, 0, 0)]

/-- `bitsOfFoR`'s `decide`-beside-`#guard` pairs: the booleans `xs` as `Coc.encode 2` lays them out, read back as a
bitmap of `n` rows. A width-1 block (copied), a constant one and a patched one. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h
def bitsOf (xs : List UInt8) (n : USize) : List UInt8 :=
  let r := Coc.encode (u 2) ⟨(xs.flatMap fun x => [x, 0]).toArray⟩
  (bitsOfFoR r.1 r.2 n).data.toList
-- 33 rows, the fewest at which one 4-byte patch (width 0) is cheaper than width 1 (5 bytes): `decide +kernel`'s
-- memory grows with the rows `encode` plans over
def oneHigh : List UInt8 := (List.range 33).map fun i => if i = 5 then 1 else 0
example : bitsOf [0, 1, 1, 0, 1] (u 5) = [22] := by decide +kernel
#guard bitsOf [0, 1, 1, 0, 1] (u 5) = [22]
example : bitsOf (List.replicate 10 1) (u 10) = [255, 3] := by decide +kernel
#guard bitsOf (List.replicate 10 1) (u 10) = [255, 3]
example : bitsOf oneHigh (u 33) = 32 :: List.replicate 4 0 := by decide +kernel
#guard bitsOf oneHigh (u 33) = 32 :: List.replicate 4 0

end Rel.Kernel.StructuralTest
