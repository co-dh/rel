import Std.Data.HashMap
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Eval.Val` the Rel kernels reach; `Rel.Eval.Val` imports it. -/


open Rel.Ext

namespace Rel

end Rel

namespace Rel.Eval

/-- The sentinel q uses for an absent element of each type. Boolean, byte and char have no
null proper, but `3#0#0b` still has to answer with something, and q answers with these. -/
def nullAtom (t : QAtomicType) (h : t ≠ .general := by first | decide | assumption) : QAtom :=
  match t with
  | .general => absurd rfl h
  | .u1 => .u1 false
  | .u8 => .u8 0
  | .i16 => .i16 Int16.minValue
  | .i32 => .i32 Int32.minValue
  | .i64 => .i64 Int64.minValue
  | .f32 => .f32 0xffc00000
  | .f64 => .f64 0xfff8000000000000
  | .char => .char 32
  | .sym => .sym 0
  | .date => .date Int32.minValue
  | .datetime => .datetime Int64.minValue
  | .i8 => .i8 Int8.minValue


end Rel.Eval
