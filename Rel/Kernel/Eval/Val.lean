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
  | .boolean => .boolean false
  | .byte => .byte 0
  | .short => .short Int16.minValue
  | .int => .int Int32.minValue
  | .long => .long Int64.minValue
  | .real => .real 0xffc00000
  | .float => .float 0xfff8000000000000
  | .char => .char 32
  | .symbol => .symbol ""
  | .timestamp => .timestamp Int64.minValue
  | .month => .month Int32.minValue
  | .date => .date Int32.minValue
  | .datetime => .datetime 0xfff8000000000000
  | .timespan => .timespan Int64.minValue
  | .minute => .minute Int32.minValue
  | .second => .second Int32.minValue
  | .time => .time Int32.minValue

/-- `~` on two payloads of one type. `Kernel.matchColumn` compares the payloads themselves — bytes
at a fixed width, symbol by symbol at a blob, since a gather leaves the same symbols in a different
blob — and folds the two signed zeros, which are the one pair `QAtom.identical` calls equal with
different bits. The element read below is what a shape it does not claim still needs. -/
def sameColumn (t : QAtomicType) (na : USize) (ea : Enc) (nb : USize) (eb : Enc) : Bool :=
  match Kernel.matchColumn t na ea nb eb with
  | some r => r
  | none => (List.range na.toNat).all fun i =>
    match Enc.get t na ea i, Enc.get t nb eb i with
    | some x, some y => x.identical y
    | _, _ => false

/-- q's `~`, which compares bit patterns, so a null matches a null and `1~1b` is false. -/
def identicalFuel (ae : QAtom → QAtom → Bool) (ce : QAtomicType → USize → Enc → USize → Enc → Bool) :
    Nat → QValue → QValue → Bool
  | 0, _, _ => false
  -- `~` does not see an attribute: measured, `` (`s#1 2 3)~1 2 3 `` is `1b`
  -- the domain is part of the value: measured, `(`d$`b)~`b` is `0b`
  | fuel + 1, .enum da a, .enum db b => da == db && identicalFuel ae ce fuel a b
  | _ + 1, .atom a, .atom b => ae a b
  -- before `atoms`, which boxed **both** columns to compare them element by element
  | fuel + 1, .general a _ _, .general b _ _ =>
      a.size == b.size && (List.range a.size).all fun i => identicalFuel ae ce fuel a[i]! b[i]!
  -- `ta == tb` guards `ce`: `matchColumn` compares payloads and does not read the type
  | _ + 1, .vector ta na ea _, .vector tb nb eb _ =>
      ta != .general && ta == tb && na == nb && ce ta na ea nb eb
  -- a `slices` **is** the general list it denotes, so `~` compares it as one against either shape:
  -- what q sends back over the wire is a list, and the layout is ours
  | fuel + 1, .slices t n e a o, b => identicalFuel ae ce fuel (.ofArray (QValue.slicesExpand t n e a o)) b
  | fuel + 1, a, .slices t n e c o => identicalFuel ae ce fuel a (.ofArray (QValue.slicesExpand t n e c o))
  | fuel + 1, .dict ka va _, .dict kb vb _ =>
      identicalFuel ae ce fuel ka kb && identicalFuel ae ce fuel va vb
  | fuel + 1, .table (.mk na ca _), .table (.mk nb cb _) =>
      na == nb && identicalFuel ae ce fuel (.ofArray ca) (.ofArray cb)
  | fuel + 1, .keyed ka va _, .keyed kb vb _ =>
      identicalFuel ae ce fuel (.table ka) (.table kb) && identicalFuel ae ce fuel (.table va) (.table vb)
  | fuel + 1, .func ca a, .func cb b => ca == cb && identicalFuel ae ce fuel (.ofArray a) (.ofArray b)
  | _ + 1, .err a, .err b => a == b
  | _ + 1, _, _ => false

/-- q identity: what keys, `?`, `distinct`, `group` and the joins read, bit for bit. `~` is
`matchValue`, the same walk under the comparison tolerance. -/
def identical (a b : QValue) : Bool := identicalFuel QAtom.identical sameColumn 4096 a b

end Rel.Eval
