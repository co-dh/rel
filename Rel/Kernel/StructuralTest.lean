import QLean.RelPart.Kernel.Coc
import QLean.RelPart.Kernel.Structural
import QLean.RelPart.Value

/-! The part of `QLean.Kernel.StructuralTest` the Rel kernels reach; `QLean.Kernel.StructuralTest` imports it. -/


namespace QLean.Kernel.StructuralTest

open QLean QLean.Kernel

-- part 0 holds no element and one block: copying that block would read `[5]` where the join is `[7]`
def extraBlk : Array ((USize × ByteArray) × ByteArray) :=
  #[((0, Coc.foRMeta QLean.Column.lgEnc 0 0 #[(5, 5, 0, 0)]), .empty), ((1, Coc.foRMeta QLean.Column.lgEnc 0 0 #[(7, 7, 0, 0)]), .empty)]
#guard (moveFoR extraBlk).isNone
-- part 0's pack is empty where its width needs 1024 bytes, so it reads its base; joining the packs
-- whole would read part 1's residual 3 as part 0's element 0 and part 1's element as its base
def shortPack : Array ((USize × ByteArray) × ByteArray) :=
  #[((1024, Coc.foRMeta QLean.Column.lgEnc 0 0 #[(5, 260, 0, 8)]), .empty),
    ((1, Coc.foRMeta QLean.Column.lgEnc 0 0 #[(7, 10, 0, 8)]), ⟨(Array.replicate 1024 0).set! 0 3⟩)]
#guard (moveFoR shortPack).isNone
-- `reverse` of a full block with a second block past the count: moving would put the 9s first
def extraRev : ByteArray := Coc.foRMeta QLean.Column.lgEnc 0 0 #[(5, 5, 0, 0), (9, 9, 0, 0)]
-- the scatter and the enumeration walk the source's blocks: two past the count wrapped the C's
-- block length, so the walk overran its buffer
def extraTwo : ByteArray := Coc.foRMeta QLean.Column.lgEnc 0 0 #[(5, 5, 0, 0), (9, 9, 0, 0), (9, 9, 0, 0)]

end QLean.Kernel.StructuralTest
