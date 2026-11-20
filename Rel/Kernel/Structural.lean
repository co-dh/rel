import Rel.Kernel.Need
import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.Structural` the Rel kernels reach; `Rel.Kernel.Structural` imports it. -/


open Rel.Ext
namespace Rel.Kernel












/-- q's `til`, as little-endian `Int64`s. Measured — `til 5` is `0 1 2 3 4`, `til 0` is the empty long
vector, `type til 5` is `7h` and `til 2h` is `0 1`, so the answer is `long` whatever the count's own
type was; `til -1` and `til 0N` are both `'domain`, which `tilColumn` declines rather than encodes. -/
def tilLongs (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (Int64.ofNat i).toUInt64 8


















end Rel.Kernel


namespace Rel.Kernel









end Rel.Kernel
