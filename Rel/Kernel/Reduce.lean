import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.Reduce` the Rel kernels reach; `Rel.Kernel.Reduce` imports it. -/


namespace Rel.Kernel


/-- What the fold answers when nothing survives, at the class the payload is read as. For a signed
type this is `Over.seed`: its null is its minimum, so `~~~nul` is the type's maximum and `nul + 1`
the least element that is not the null. The two unsigned classes have no null and every value from
`0` to `255` is an element, so their extremes are those — measured, `min 0#0x00` is `0xff`,
`max 0#0x00` is `0x00`, and the same at `char`. Every other verb seeds with a constant that no null
enters, which is why they come straight from `Over.seed`. -/
def Coc.Over.denseSeed (op : Coc.Over) (cls : UInt8) (nul : Int64) : Int64 :=
  if cls != Ew.u8 || (op != .lesser && op != .greater) then op.seed nul
  else if op == .lesser then 255 else 0

/-- q's `f/` over a dense payload, at one of the four integral classes. `Coc.over` is this same fold
over the encoded form — the same `Over.seed`, `Over.step` and `Over.boolCast` — and the two differ
only in where an element comes from, which is what `~/q/q.k` line 7's one `/aggr` family asks for.

Reading an element is `Ew.signed`'s rule and not a second one, so `byte` and `char` zero-extend and
everything else sign-extends, which is exactly what makes `min "a b"` the blank. -/
def overBytes (op : Coc.Over) (cls : UInt8) (nul : Int64) (b : @& ByteArray) : Int64 :=
  (List.range (b.size / Ew.width cls)).foldl (init := op.denseSeed cls nul) fun acc i =>
    let x := Ew.signed cls (Ew.elem cls b i)
    if !op.boolCast && x == nul then acc else op.step acc x


end Rel.Kernel


namespace Rel.Kernel

/-- The null of an encoded type as the fold has to skip it, and `none` at a type the encoding is not
for. The encoded form holds a narrow column's elements sign-extended, so a `short` null is `-32768`
there and not `Int64.minValue`; the block structure is unchanged, the null still being the smallest
value the type has. -/
def Coc.nullOf : QAtomicType → Option Int64
  | .i16 => some (-32768)
  | .i32 | .date => some (-2147483648)
  | .i64 | .datetime => some Int64.minValue
  | _ => none

/-- The fold on the encoded form, before the narrowing `sum` and `prd` put on top of it. It is
separate because `avg` divides *this* one and not the narrowed one: measured, `avg 1000000#3000i` is
`3000f` where `sum` of the same is `0Ni`. -/
def overFoR (op : Coc.Over) (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option Int64 :=
  match e with
  | .foR metadata pack => (Coc.nullOf t).map (Coc.over op · metadata pack n)
  | _ => none


end Rel.Kernel
