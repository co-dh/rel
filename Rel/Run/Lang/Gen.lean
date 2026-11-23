module

public import Rel.Run.Lang.Lazy

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! What the code a `rel_program` definition expands into names besides `GenK`: a definition's listed value
    (`Gv`, `entry`), and the literal columns rebuilt from their payloads. -/

open Rel.Ext

namespace Rel.Lang

open Tab

namespace Gen

open Rel Rel.Kernel

/-- A definition's value with its objects: what `rel_program n` lists as `n.expanded`. -/
abbrev Gv := (A : Obj) × (B : Obj) × Except String (Tab A B)

def entry (n : String) (A B : Obj) (c : Except String (Tab A B)) : String × Gv := (n, ⟨A, B, c⟩)
/-! ### Leaves: the values `build` put in the term, rebuilt from their payloads -/

/-- The bytes of the hex text `s` (two lowercase digits a byte, as `Expand.hex` writes them). One string
    literal per column, so a column of any size is one node of the generated term. -/
def unhex (s : String) : ByteArray := Id.run do
  let u := s.toUTF8; let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
  let mut b := ByteArray.emptyWithCapacity (u.size / 2)
  for h : i in [0:u.size / 2] do
    have := h.upper; b := b.push (d u[2 * i] * 16 + d u[2 * i + 1])
  pure b

/-- The `foR` column of `t` whose metadata and pack are the hex texts `m` and `p`, rebuilt as it was written, and its
    fit as its ok bit: `Enc.WF` and no null (`hasNul`) are decided, so a payload that does not fit `n` is a blank column with bit false, never a
    wrong column read as right. -/
def atom (t : QAtomicType) (n : USize) (m p : String) : Arr t n × Bool :=
  let e := Enc.foR (unhex m) (unhex p)
  match Enc.wf? t n e with
  | some ⟨h⟩ => if hN : hasNul e = false then (Arr.mk e h hN, true) else blank
  | none => blank
where blank := (Arr.mk (Enc.blank t n) (Enc.blank_WF t n) (Enc.blank_plain t n), false)

/-- A rebuilt column from its rebuilt parts, its bit the `&&` of theirs. -/
def pairV (A B : Obj) (n : USize) (x : Vals A n × Bool) (y : Vals B n × Bool) : Vals (.prod A B) n × Bool :=
  ((x.1, y.1), x.2 && y.2)
def arrV (B : Obj) (n m : USize) (lo hi : Arr .i64 n × Bool) (p : Vals B m × Bool) : Vals (.arr B) n × Bool :=
  (⟨m, lo.1, hi.1, p.1⟩, lo.2 && hi.2 && p.2)
def sumV (A B : Obj) (n l r : USize) (tag : Arr .u1 n × Bool) (idx : Arr .i64 n × Bool) (x : Vals A l × Bool)
    (y : Vals B r × Bool) : Vals (.sum A B) n × Bool :=
  (⟨l, r, tag.1, idx.1, x.1, y.1⟩, tag.2 && idx.2 && x.2 && y.2)
/-- A side of `1`: no column, so nothing to rebuild and nothing to misfit. -/
def oneV (n : USize) : Vals .one n × Bool := ((), true)
def relV (A B : Obj) (n : USize) (k : Vals A n × Bool) (v : Vals B n × Bool) : Tab A B × Bool :=
  (⟨n, k.1, v.1⟩, k.2 && v.2)
end Gen

end Rel.Lang
