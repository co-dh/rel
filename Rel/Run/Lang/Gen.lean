module

public import Rel.Run.Lang.Lazy
import all Init.Data.Array.Basic

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! What the code a `rel_program` definition expands into names besides `GenK`: a definition's listed value
    (`Gv`, `entry`), and the literal columns rebuilt from their payloads. -/


namespace Rel.Lang

open Tab

namespace Gen

open Rel Rel.Kernel

/-- A definition's value with its objects: what `rel_program n` lists as `n.expanded`. -/
abbrev Gv := (A : Obj) × (B : Obj) × Except String (Tab A B)

def entry (n : String) (A B : Obj) (c : Except String (Tab A B)) : String × Gv := (n, ⟨A, B, c⟩)
/-! ### Leaves: the values `build` put in the term, rebuilt from their payloads -/

/-- The bytes of the hex text `s` as a byte loop pushed onto `b`: the fast compiled form (`unhex_eq`). -/
def unhexFastAcc (b0 : ByteArray) (s : String) : ByteArray := Id.run do
  let u := s.toUTF8; let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
  let mut b := b0
  for h : i in [0:u.size / 2] do
    have := h.upper; b := b.push (d u[2 * i] * 16 + d u[2 * i + 1])
  pure b

/-- The bytes of the digit pairs of a UTF-8 byte list, structurally: what the kernel reduces fastest. -/
def unhexL : List UInt8 → List UInt8
  | a :: b :: r => ((if a ≤ 57 then a - 48 else a - 87) * 16 + (if b ≤ 57 then b - 48 else b - 87)) :: unhexL r
  | _ => []

/-- The bytes of one hex chunk `s`. -/
def unhexS (s : String) : List UInt8 := unhexL s.toByteArray.data.toList

/-- The bytes of the hex text written as the chunks `ss` (two lowercase digits a byte, an even number of digits per chunk,
    as `Expand.hexE` writes them). A column is a list of short literals, never one long one: the kernel is superlinear in
    the length of one string literal, so its cost is linear in the number of chunks. Structural over the UTF-8 bytes
    because the kernel unfolds a `forIn` loop per byte (`unhexFastAcc`, its compiled form by `unhex_eq`). -/
def unhex (ss : List String) : ByteArray := ⟨⟨ss.flatMap unhexS⟩⟩

/-- Byte `i` of a chunk is the hex digits `2i`, `2i + 1` of `s`'s UTF-8 bytes, `s.toList.utf8Encode`, the form a
    literal's bytes evaluate in (`String.toUTF8` of a literal is not exposed). -/
private theorem unhexL_eq (l : List UInt8) : unhexL l = (List.range (l.length / 2)).map fun i =>
    let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
    d (l.getD (2 * i) 0) * 16 + d (l.getD (2 * i + 1) 0) := by
  induction l using unhexL.induct with
  | case1 a b r ih =>
    rw [unhexL, ih, show (a :: b :: r).length / 2 = r.length / 2 + 1 by simp only [List.length_cons]; omega,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_succ, Function.comp_def]
    congr 1
  | case2 l h =>
    match l with
    | [] => rfl
    | [_] => simp [unhexL]
    | _ :: _ :: _ => exact absurd rfl (h _ _ _)

theorem unhexS_eq (s : String) : unhexS s =
    let u := s.toList.utf8Encode
    (List.range (u.size / 2)).map fun i =>
      let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
      d (u.data.getD (2 * i) 0) * 16 + d (u.data.getD (2 * i + 1) 0) := by
  rw [← String.toByteArray_ofList, String.ofList_toList]
  show unhexL s.toByteArray.data.toList = _
  rw [unhexL_eq]
  simp only [ByteArray.size, Array.length_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **What `Gen.unhex` reads**, for any chunks `ss`: the concatenation of each chunk's bytes. -/
theorem unhex_toList (ss : List String) : (unhex ss).data.toList = ss.flatMap fun s =>
    let u := s.toList.utf8Encode
    (List.range (u.size / 2)).map fun i =>
      let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
      d (u.data.getD (2 * i) 0) * 16 + d (u.data.getD (2 * i + 1) 0) := by
  show ss.flatMap unhexS = _
  congr 1; funext s; exact unhexS_eq s

private theorem fastAcc_toList (b0 : ByteArray) (s : String) :
    (unhexFastAcc b0 s).data.toList = b0.data.toList ++ unhexS s := by
  have push : ∀ {α : Type} (l : List α) (g : α → UInt8) (b : ByteArray),
      (l.foldl (fun b x => b.push (g x)) b).data.toList = b.data.toList ++ l.map g := by
    intro α l; induction l with
    | nil => simp
    | cons x l ih => intro g b; simp [ih]
  rw [unhexS_eq, ← String.toByteArray_ofList, String.ofList_toList]
  simp [unhexFastAcc, Std.Legacy.Range.forIn'_eq_forIn'_range', ← List.range_eq_range']
  show (List.foldl (α := ByteArray) _ _ _).data.toList = _
  rw [push]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i _ h2
    simp only [List.length_map, List.length_range] at h2
    have h3 : 2 * i + 1 < s.toByteArray.data.size := show _ < s.utf8ByteSize by omega
    simp only [List.getElem_map, List.getElem_attach, List.getElem_range]
    rw [Array.getElem?_eq_getElem h3, Array.getElem?_eq_getElem (show 2 * i < s.toByteArray.data.size by omega),
      Option.getD_some]
    simp only [Option.getD_some]
    rfl

/-- `unhex` as a loop over the chunks: the fast compiled form (`unhex_eq`). -/
def unhexFast (ss : List String) : ByteArray := ss.foldl unhexFastAcc .empty

private theorem foldl_toList (ss : List String) (b : ByteArray) :
    (ss.foldl unhexFastAcc b).data.toList = b.data.toList ++ ss.flatMap unhexS := by
  induction ss generalizing b with
  | nil => simp
  | cons s r ih => rw [List.foldl_cons, ih, fastAcc_toList, List.flatMap_cons, List.append_assoc]

/-- The compiled `unhex` is the byte loop: the kernel and the proofs read `unhex`, the code runs `unhexFast`. -/
@[csimp] theorem unhex_eq : @unhex = @unhexFast := by
  funext ss; exact ByteArray.ext (Array.toList_inj.1 (by
    rw [unhexFast, foldl_toList]; simp [ByteArray.empty, ByteArray.emptyWithCapacity]; rfl))

/-- The `foR` column of `t` whose metadata and pack are the hex texts `m` and `p`, rebuilt as it was written, and its
    fit as its ok bit: `Enc.WF` and no null (`hasNul`) are decided, so a payload that does not fit `n` is a blank column with bit false, never a
    wrong column read as right. -/
def atom (t : QAtomicType) (n : USize) (m p : List String) (hw : t.width.isSome = true := by first | decide | assumption) :
    Arr t n × Bool :=
  let e := Enc.foR (unhex m) (unhex p)
  match Enc.wf? t n e with
  | some ⟨h⟩ => if hN : hasNul e = false then (Arr.mk e h hN, true) else blank
  | none => blank
where blank := (Arr.mk (Enc.blank t n) (Enc.blank_WF t n hw) (Enc.blank_plain t n hw), false)

/-- A nullable column's payload `m`, `p` rebuilt as `atom` rebuilds a column but nulls allowed: `Enc.WF` decided, a
    payload that does not fit `n` a blank column with bit false. -/
def opt (t : QAtomicType) (n : USize) (m p : List String) (hw : t.width.isSome = true := by first | decide | assumption) :
    Opt t n × Bool :=
  let e := Enc.foR (unhex m) (unhex p)
  match Enc.wf? t n e with
  | some ⟨w⟩ => (⟨e, w⟩, true)
  | none => (⟨Enc.blank t n, Enc.blank_WF t n hw⟩, false)
/-- An atom column at ownership `o` rebuilt from its payload: `atom`, or `opt` where a row may be null. -/
def colB (o : Bool) (t : QAtomicType) (n : USize) (m p : List String) (hw : t.width.isSome = true := by first | decide | assumption) :
    ColB o t n × Bool :=
  match o with
  | false => atom t n m p hw
  | true => opt t n m p hw

/-- A rebuilt column from its rebuilt parts, its bit the `&&` of theirs; at ownership `o`, as `ValsB`. -/
def pairV (o : Bool) (A B : Obj) (n : USize) (x : ValsB o A n × Bool) (y : ValsB o B n × Bool) :
    ValsB o (.prod A B) n × Bool :=
  ((x.1, y.1), x.2 && y.2)
def arrV (o : Bool) (B : Obj) (n m : USize) (lo hi : ColB o .i64 n × Bool) (p : Vals B m × Bool) :
    ValsB o (.arr B) n × Bool :=
  (⟨m, lo.1, hi.1, p.1⟩, lo.2 && hi.2 && p.2)
def sumV (o : Bool) (A B : Obj) (h : Obj.band A B = none) (n : USize) (tag : Arr .u1 n × Bool)
    (x : ValsB true A n × Bool) (y : ValsB true B n × Bool) : ValsB o (.sum A B) n × Bool :=
  (ValsB.ofGen h tag.1 x.1 y.1, tag.2 && x.2 && y.2)
/-- A band sum's one nullable column (`Obj.band`), rebuilt by `opt`. -/
def optV (o : Bool) (A B : Obj) (t : QAtomicType) (h : Obj.band A B = some t) (n : USize) (m p : List String)
    (hw : t.width.isSome = true := by first | decide | assumption) :
    ValsB o (.sum A B) n × Bool :=
  ((ValsB.ofOpt h (opt t n m p hw).1, (opt t n m p hw).2))
/-- A side of `1`: no column, so nothing to rebuild and nothing to misfit. -/
def oneV (o : Bool) (n : USize) : ValsB o .one n × Bool := ((), true)
def relV (A B : Obj) (n : USize) (k : Vals A n × Bool) (v : Vals B n × Bool) : Tab A B × Bool :=
  (⟨n, k.1, v.1⟩, k.2 && v.2)
end Gen

end Rel.Lang
