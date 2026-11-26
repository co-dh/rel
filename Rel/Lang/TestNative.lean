import Rel.Run.Lang.EmitC
import Rel.Run.Lang.Embed
import Rel.Programs.Prelude

/-! Stage 1a of the native backend (`doc/rel-native-design.md` §13): `x ≜ {…}°`, `output x to "out"`. Its plan is
    literals, the converse's `canon` (`kasc`, `kseen`, `kgather`) and `qlean_own_write` calls. `main` is the `relc-1a` exe:
    `c FILE` prints the plan as C, `lean DIR` writes `DIR/out` from the value Lean computed (`writeRel`), `plan DIR`
    runs the plan in `DIR` (`Plan.run`). The language has no `output` declaration yet (stage 2), so the output is
    stated here, as `planOf`'s arguments. -/

namespace Rel.Lang.TestNative

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel

-- the prelude's `1` (`ℓ`'s `⊤(1,L)`), read by `relc` outside this Lean scope through the program's recorded homes
open Rel.Programs.prelude in
rel_program native1a where
    obj X = {A,B,C}
    obj N = 0…9
    x : X ⟶ N ≜ {(1,A),(2,B),(5,C),(5,A)}°
    un : N ⟶ X ≜ {(1,A),(2,B)} ∪ {(5,C),(2,B)}
    me : N ⟶ X ≜ {(1,A),(2,B)} ∩ {(5,C),(2,B)}
    df : N ⟶ X ≜ {(1,A),(2,B)} − {(5,C),(2,B)}
    zr : X ⟶ N ≜ 𝟘
    cm : X ⟶ X ≜ x x°
    dm : X ⟶ X ≜ dom(x)
    rn : N ⟶ N ≜ ran(x)
    pr : X ⟶ N × N ≜ ⟨x, x⟩
    cx : X × N ⟶ N × X ≜ x × x°
    po : X × N ⟶ X ≜ (x × x°) π₂
    pl : X × N ⟶ N ≜ (x × x°) π₁
    ix : X ⟶ X ≜ x x° 𝟙
    tp : X ⟶ X ≜ x ⊤
    ed : N ⟶ N ≜ {(1,2),(2,3),(3,5)}
    tc : N ⟶ N ≜ μY : ed ∪ (Y ed)
    cy : N ⟶ N ≜ {(1,1),(1,2),(2,3)}
    gf : N ⟶ N ≜ νY : cy ∩ (cy Y)
    le : X ⟶ N ≜ x ≤
    lt : N ⟶ X ≜ < x°
    ml : N ⟶ N ≜ {(1,5),(5,2),(2,2),(9,3)} ∩ ≤
    sc : X ⟶ N ≜ x succ
    w : N×N ⟶ N×N ≜ {((7,2),(7,2)),((2,7),(2,7)),((7,0),(7,0)),((3,5),(3,5))}
    ps : N×N ⟶ N ≜ w plus
    mn : N×N ⟶ N ≜ w minus
    dv : N×N ⟶ N ≜ w div
    tm : N×N ⟶ N ≜ w times
    f(S : X ⟶ N) : X ⟶ N ≜ S succ ∪ S
    fc : X ⟶ N ≜ f(x)
    bo : X ⟶ X ≜ {(B,A),(C,A)}
    rt : X ⟶ N ≜ {(A,3),(B,7),(C,2)}
    lm : X ⟶ [X] ≜ dom(x) Λ(bo°)
    nl : X ⟶ [N] ≜ dom(x) nil
    lu : X ⟶ [X] ≜ lm ∪ (dom(x) nil)
    hd : X ⟶ X ≜ lm at(0)
    ee : X ⟶ [N] ≜ lm E(x)
    fm : X ⟶ [N] ≜ lm F(rt)
    hy : X ⟶ N ≜ dom(x) hylo(⟨𝟙, Λ(bo°)⟩, π₁ rt)
    ld : N ⟶ N ≜ x \ x
    a1 : X ⟶ N ≜ {(A,1)}
    a2 : X ⟶ N ≜ {(A,2)}
    l1 : N ⟶ N ≜ a1 \ a2
    rd : N ⟶ N ≜ x° / x°
    g(S : N ⟶ N) : X ⟶ N ≜ x S
    gc : X ⟶ N ≜ g(succ)
    xs : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,2 2)}
    z0 : N ⟶ N ≜ {(0,0)}
    f1 : N ⟶ N ≜ xs ⦇[z0, plus]⦈
    f3 : N ⟶ N ≜ xs ⦇[z0, π₁ ∪ π₂]⦈ʳ
    es : N ⟶ N ≜ xs est(≤)
    th : N ⟶ [N] ≜ xs front(≤)
    obj L = 5…6
    ℓ : 1 ⟶ [L] ≜ Λ(⊤(1,L))
    pf(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇[⟨𝟙,𝟙⟩, π₁ ∪ (π₁ (𝟙×R))]⦈)
    q1 : X ⟶ X ≜ {(A,B),(B,C)}
    fa : N ⟶ X×X ≜ {(0,0)}⊤(N,X)⟨𝟙,bo⟩ ∪ ({(1,1)}⊤(N,X)⟨𝟙,q1⟩)
    fi : N ⟶ (X×X)×(X×X) ≜ pf(fa)
    -- `inl`, `inr` into a general sum `N+N` (tag, position, two payloads, one of them of no row) and `inr` into the in-band
    -- `1+N` (one nullable column); their key is the sum's `ValsB.cols` (tag, then each summand gathered at its position)
    gi : N ⟶ N+N ≜ ed inl
    gj : N ⟶ N+N ≜ ed inr
    gk : N ⟶ 1+N ≜ ed inr
    -- `∪` of the two on a general sum (both tags in one column, `catSummandB`), `inl ()` into the nullable column (`nulsB`)
    -- and `∪` of the two on the nullable column (in-band concat, a null beside values)
    gu : N ⟶ N+N ≜ gi ∪ gj
    gn : N ⟶ 1+N ≜ {(1,∗),(2,∗)} inl
    gv : N ⟶ 1+N ≜ gn ∪ gk
    -- `1+(N×N)` is no band column: its summand `1` has no column, its count is the tag's rows (`colsOf`) and its file
    -- holds the count only (`oneKind`; the left `1` of no row here, written by `writeOnes`); `inr` of a pair
    gx : N ⟶ 1+(N×N) ≜ ⟨ed, ed⟩ inr
    -- `inl ()` rows of two keys, and beside the `inr` rows (`∪` is `canon`): the `1` summand's count after `canon`
    gy : N ⟶ 1+(N×N) ≜ {(1,∗),(2,∗)} inl
    gz : N ⟶ 1+(N×N) ≜ gy ∪ gx
    gw : N ⟶ 1+(N×N) ≜ gy ∪ gy
    -- the key of a sum whose summand holds a list or a sum (`zeroCols`: the other summand has no row)
    gm : N ⟶ [N]+N ≜ xs inl
    gp : N ⟶ (N+N)+N ≜ gi inl
    -- `inl°`, `inr°` on the sum values in demand: a dense sum with a summand `1` (`jl`, `jr`), a list summand (`kl`), the
    -- nullable column in band with rows and a null (`bn`; `br` the non-null rows, `bl` the null), and a case `[R, S]`
    bn : N ⟶ 1+N ≜ gk ∪ ({(9,∗)} inl)
    jl : N ⟶ 1 ≜ gx inl°
    jr : N ⟶ N×N ≜ gx inr°
    kl : N ⟶ [N] ≜ gm inl°
    br : N ⟶ N ≜ bn inr°
    bl : N ⟶ 1 ≜ bn inl°
    bc : N ⟶ N ≜ bn [{(∗,0)}, 𝟙]
    -- `sum` and `sums` at `i64` with a wrapping row (cell 1, key 1 from position 1 on: dropped), and `sum` at `f64`
    obj I
    obj F : f64
    bg : N ⟶ [I] ≜ {(1,9223372036854775807 1),(2,5 6),(3,[]),(4,7 0)}
    sb : N ⟶ I ≜ bg sum
    fl : N ⟶ [F] ≜ {(1,1.5 2.25),(2,[]),(3,0.5 0.25)}
    sf : N ⟶ F ≜ fl sum
    sx : N×N ⟶ I ≜ {((1,0),5),((1,1),9223372036854775807),((1,2),1),((2,0),3),((2,1),4),((2,2),9)}
    ss : N×N ⟶ I ≜ sums(sx)
    -- `length` of cells of two, none and two elements
    ln : N ⟶ N ≜ bg length
    -- `mix` (splitmix64, `Op.mixWord`) at counters 0, 42 and the largest `i64`, where `u + 1` leaves the sign
    mx : N ⟶ I ≜ {(1,0),(2,42),(3,9223372036854775807)} mix
    -- `<` on an unbounded object, bounded only by the literal composed after it: run with its range that literal's
    -- domain (`S` first) and read at the range of the table before it (a closed node that cannot run closed)
    obj M
    gb : M ⟶ M ≜ {(0,5),(1,100),(2,200)} dom(<°{(99,∗)})
    tk : M ⟶ M ≜ dom(< {(∗,2)}°) {(0,7),(1,8),(2,9),(3,4)}
    -- `cat°` on cells of three, none, two and two elements (each cell's `e - s + 1` splits), and each split's side (the
    -- bodies of `prefix`, `suffix`, whose rows are of their own; `last`, `init` also need `τ`, with no plan recipe yet)
    cu : N ⟶ [N]×[N] ≜ xs cat°
    pre : N ⟶ [N] ≜ xs cat° π₁
    suf : N ⟶ [N] ≜ xs cat° π₂
    -- the rows `prefix`, `suffix`, `τ` and the prelude's `last`, `init`, `tail` (`at(0)τ ∩ 𝟙`, `cat°`), on the same cells
    pfx : N ⟶ [N] ≜ xs prefix
    sfx : N ⟶ [N] ≜ xs suffix
    la : N ⟶ N ≜ xs last
    ini : N ⟶ [N] ≜ xs init
    tl : N ⟶ [N] ≜ xs tail
    tw : N ⟶ [[N]] ≜ xs τ

/-- `output x to "out"`. -/
def plan : Lean.Meta.MetaM (Except String Plan) := return (← outputOf ``native1a "x" "out") >>= Bld.plan

/-! F-e: a computed relation as columns. `arithB` on two literal columns answers a count register and `Enc`
    registers; the output is the one-row relation of lists `gu ↦ s`: each side's `.e` a computed column handed over
    encoded (`encRegs`), its `.hi` the one-row column of the count (`constB`), its `.lo` the literal `[0]`. -/

/-- The literal `i64` column of `xs`, encoded as the kernels encode their answers (`wordsFoR`). -/
def longs (xs : List Int64) : Enc := wordsFoR (xs.map Int64.toUInt64).toArray

/-- A list side of one row: `.lo` `[0]`, `.hi` `[m]`, `.e` the `m` rows of the column `e`. -/
def listSide (m e : Nat) : Bld Side := do
  let one ← lit (.size 1)
  return [(".lo", ← encRegs .i64 one (← lit (Reg.put (longs [0])))),
    (".hi", ← encRegs .i64 one (← constB one (← call1 (kernel% USize.toUInt64) #[m]))), (".e", ← encRegs .i64 m e)]

/-- `arith add`'s operands: a null, an overflow, a negative operand among the rows. -/
def arithIn : Bld (Array Nat) := do
  let n ← lit (.size 5)
  arithB .add n (← lit (Reg.put (longs [5, 7, Alg.nul, Int64.maxValue, -3]))) (← lit (Reg.put (longs [1, 2, 3, 1, 4])))

/-- `arithIn`'s relation, written to `dir`. -/
def arithOut (dir : String) : Bld Unit := do
  let rs ← arithIn
  output dir (.arr (.atom .i64)) (.arr (.atom .i64)) ⟨← lit (.size 1), ← listSide (← nth rs 0 "arithB") (← nth rs 1 "arithB"), ← listSide (← nth rs 0 "arithB") (← nth rs 3 "arithB")⟩

-- six columns, each one `qlean_own_write`
#eval show IO Unit from do
  let (_, ws) ← IO.ofExcept ((← IO.ofExcept (Bld.plan (arithOut "out"))).run abiOf)
  unless ws.size == 6 do throw (IO.userError s!"arithOut writes {ws.size} columns, not six")

-- the kept rows are those of `arith`: `5+1`, `7+2`, `-3+4` (the null and the overflow out); decoded here, in the test
#eval show IO Unit from do
  let (rs, is, _, fs, gs) ← IO.ofExcept (arithIn.run (#[], 0, #[], #[]))
  let (vs, _) ← IO.ofExcept (({ funs := fs, globals := gs, main := is.toList } : Plan).run abiOf)
  let col (i : Nat) : List UInt64 := match rs[i]?.bind (vs[·]?) |>.bind (Reg.get? (α := Enc)) with
    | some e => (Enc.raw .i64 3 e).toList | none => []
  unless (rs[0]?.bind (vs[·]?) |>.bind (Reg.get? (α := USize))) == some 3 do throw (IO.userError "arithB keeps not 3 rows")
  unless col 1 == [5, 7, (-3 : Int64).toUInt64] && col 3 == [6, 9, 1] do
    throw (IO.userError s!"arithB keeps u = {col 1}, s = {col 3}")

-- an `i64` overflow fails the run as `Tab.arithOp` / `Tab.succOp` do (`Rel.Run.Arith`), the same text, at the first
-- such row; a null operand and a zero divisor have no image and no error. `fail`'s C prints the same text (`failSegs`).
#eval show IO Unit from do
  let lits (xs : List Int64) : Bld Nat := lit (Reg.put (longs xs))
  let go (b : Bld Unit) : Except String Unit := do discard <| (← Bld.plan b).run abiOf
  let ar (s : String) (as bs : List Int64) : Except String Unit := go do
    let n ← lit (.size as.length.toUSize)
    discard <| arithOpB s (.prod (.atom .i64) (.atom .i64)) (.atom .i64) n [.atom "" .i64 (← lits as), .atom "" .i64 (← lits bs)]
  let su (xs : List Int64) : Except String Unit := go do
    discard <| succOpB (.atom .i64) (.atom .i64) (← lit (.size xs.length.toUSize)) [.atom "" .i64 (← lits xs)]
  let cases : List (String × Except String Unit × String) :=
    [("plus", ar "plus" [1, Int64.maxValue, Int64.maxValue] [1, 1, 2], "plus: i64 overflow at plus(9223372036854775807, 1)"),
     ("minus", ar "minus" [3, -9223372036854775807] [1, 3], "minus: i64 overflow at minus(-9223372036854775807, 3)"),
     ("times", ar "times" [4, Int64.maxValue] [5, 2], "times: i64 overflow at times(9223372036854775807, 2)"),
     ("succ", su [1, Int64.maxValue, Int64.maxValue], "succ: i64 overflow at succ(9223372036854775807)"),
     ("none", ar "div" [7, 7, Alg.nul, 9] [0, 2, 3, 3], ""), ("succ none", su [1, Alg.nul, -4], "")]
  for (w, r, e) in cases do
    unless (match r with | .error m => m | .ok _ => "") == e do throw (IO.userError s!"{w}: the run answers {repr (match r with | .error m => m | .ok _ => "")}, not {repr e}")

/-! Group ids (`groupIdsB`, design §4 group-by `kasc ≫ kseen`), as a plan function, so a function's C is printed. -/

/-- The plan function of `groupIdsB` on its parameters: the type's byte, the row count, the column. -/
def gfun : Bld Nat := defFun #[.u8, .size, .obj] fun ps => do
  pure #[← groupIdsB (← nth ps 0 "gfun") (← nth ps 1 "gfun") (← nth ps 2 "gfun")]

/-- Columns of each type a key reads, with their group ids: ties, a boolean, no row. -/
def codes : List (QAtomicType × Nat × Enc × List UInt64) :=
  [(.i64, 5, longs [3, 1, 3, 2, 1], [2, 0, 2, 1, 0]), (.u1, 4, wordsFoR #[1, 0, 1, 1], [1, 0, 1, 1]),
   (.i64, 0, longs [], [])]

/-- `gfun` applied to `c`: its ids register. -/
def gapply (c : QAtomicType × Nat × Enc × List UInt64) (f : Nat) : Bld Nat := do
  nth (← apply f #[← lit (Reg.put c.1), ← lit (.size c.2.1.toUSize), ← lit (Reg.put c.2.2.1)] 1) 0 "gfun"

/-- `gfun` applied to each of `cs`; `main`'s last register is the last column's ids. -/
def gplan (cs : List (QAtomicType × Nat × Enc × List UInt64)) : Except String Plan := Bld.plan do
  let f ← gfun
  for c in cs do discard <| gapply c f

/-- `Plan.run` of `gplan [c]` answers `c`'s ids. -/
def agrees (c : QAtomicType × Nat × Enc × List UInt64) : IO Bool := do
  let (rs, _) ← IO.ofExcept ((← IO.ofExcept (gplan [c])).run abiOf)
  pure <| (rs.back?.bind (Reg.get? (α := Enc))).any fun g => (Enc.raw .i64 c.2.1.toUSize g).toList == c.2.2.2

#eval show IO Unit from do for c in codes do unless ← agrees c do throw (IO.userError s!"group ids differ at {repr c.1}")

/-- The ids of `codes`' first column, written to `dir/key`. -/
def gidOut (dir : String) : Bld Unit := do
  let some c := codes.head? | throw "codes is empty"
  output dir (.atom .i64) (.atom .i64) ⟨← lit (.size c.2.1.toUSize), [("", ← encRegs .i64 (← lit (.size c.2.1.toUSize)) (← gapply c (← gfun)))], []⟩

/-! IO step I10: a program's `input`s read and its `output`s written by the plan as `n.io` reads and writes them. The
    native gate runs `nativeIO.io` (`relc run`) beside the native executable on `test/native/in` (a CSV file and a
    table directory) and compares `out/io` byte for byte. -/

open Rel.Programs.prelude in
rel_program nativeIO where
    obj N
    obj F : f64
    schema Row = {px : N, qty : N}
    schema Key = {px : N}
    schema Q = {qty : N}
    schema FRow = {px : N, w : F}
    input t : N ⟶ Row from csv "in/t.csv"
    -- the own-format files `output t to "out/io/t"` writes, kept as test/native/in/t
    input s : N ⟶ Row from "in/t"
    -- keyed: in/k/key/px and in/k/val/qty are in/t's two columns, rows not in key order, so the read sorts them
    input k : Key ⟶ Q from "in/k"
    input kc : Key ⟶ Q from csv "in/t.csv"
    input f : N ⟶ FRow from csv "in/f.csv"
    -- the own-format files `output f to "out/io/f"` writes, kept as test/native/in/f: a float column mapped from its file
    input g : N ⟶ FRow from "in/f"
    -- nullable columns `1+N` (in band: one `csvRead` column each, an empty cell its null), read, written back as CSV and as
    -- a table directory, and as the key of the converse (`canon` sorts the null first)
    schema NRow = {v : 1+N, f : 1+N}
    input nu : N ⟶ NRow from csv "in/nu.csv"
    cn : NRow ⟶ N ≜ nu°
    output nu to csv "out/io/nu.csv"
    output nu to "out/io/nu"
    output cn to "out/io/cn"
    -- general sums written as own table directories (tag, position, each summand's own file, a side of `1` its count
    -- file): `[N]+N` (a list summand) and `1+(N×N)` (a summand `1`, a product summand), kept as test/native/in/gm and
    -- test/native/in/gx
    schema GM = {a : [N]+N}
    schema GX = {a : 1+(N×N)}
    ed : N ⟶ N ≜ {(1,2),(2,3),(3,5)}
    xs : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2)}
    gm : N ⟶ GM ≜ xs inl
    gx : N ⟶ GX ≜ ⟨ed, ed⟩ inr
    output gm to "out/io/gm"
    output gx to "out/io/gx"
    -- those directories and `out/io/nu` read back as own table directories (the tag, the position and each summand's file,
    -- a `1` summand's count against the tag's rows, a nullable column as `1+N` in band) and written again: `out/io/gmi`,
    -- `gxi` and `nd` equal `gm`, `gx` and `nu` byte for byte
    input gmi : N ⟶ GM from "in/gm"
    input gxi : N ⟶ GX from "in/gx"
    input nd : N ⟶ NRow from "in/nu"
    output gmi to "out/io/gmi"
    output gxi to "out/io/gxi"
    output nd to "out/io/nd"
    -- symbol columns: two CSV files interned into one dictionary (ids in insertion order, not text order: `pear`, `apple`,
    -- `fig`, then `kiwi`), read, written back as texts, and met on ids by `∪`
    obj S : sym
    schema SRow = {nm : S, qty : N}
    input sy : N ⟶ SRow from csv "in/sy.csv"
    input sz : N ⟶ SRow from csv "in/sz.csv"
    su : N ⟶ SRow ≜ sy ∪ sz
    -- the dictionary as the relation `S ⟶ [C]` after both inputs: id order, its texts
    obj C : char
    dictionary dd : S ⟶ [C]
    output dd to csv "out/io/dd.csv"
    output sy to csv "out/io/sy.csv"
    -- own format with a symbol column: its ids as they lie, and the library dictionary out/io/sym.* (Table.writeLib)
    output sy to "out/io/sy"
    output sz to csv "out/io/sz.csv"
    output su to csv "out/io/su.csv"
    -- a `1+S` not in band (`1+PQ`, no band column): one nullable file column per field of `PQ` (`PQ.pa`, `PQ.pb`; as a key
    -- `pa`, `pb`), a row with both empty the `1`; read (`csvSideB`: tag, position, values of each) and written back
    schema PQ = {pa : N, pb : N}
    input pq : N ⟶ N×(1+PQ) from csv "in/pq.csv"
    input qk : 1+PQ ⟶ N from csv "in/qk.csv"
    output pq to csv "out/io/pq.csv"
    output qk to csv "out/io/qk.csv"
    -- a column of the side `1` (`CsvCol.one`): read as nothing, written as its one element's code `0` in each row
    schema OU = {o : 1, v : N}
    input ou : N ⟶ OU from csv "in/ou.csv"
    output ou to csv "out/io/ou.csv"
    cp : N ⟶ Row ≜ t
    un : N ⟶ Row ≜ t ∪ t
    cm : N ⟶ N ≜ t t°
    sk : N ⟶ Row ≜ s ∪ s
    output t to "out/io/t"
    output t to csv "out/io/t.csv"
    output cp to csv "out/io/cp.csv"
    output s to "out/io/s"
    output s to csv "out/io/s.csv"
    output sk to "out/io/sk"
    output un to "out/io/un"
    output cm to "out/io/cm"
    output k to "out/io/k"
    output k to csv "out/io/k.csv"
    output kc to "out/io/kc"
    output f to "out/io/f"
    output g to "out/io/g"
    output g to csv "out/io/g.csv"

-- a float column mapped from its file is checked canonical as `Table.readArr` checks it: `-0` and a NaN fail the run,
-- `+0`, `-2.25` and `+∞` pass, at both float atoms
#eval show IO Unit from do
  let check (t : QAtomicType) (ws : Array UInt64) : Except String Unit := do
    let p ← Bld.plan do canonFloatB "w" t (← lit (.size ws.size.toUSize)) (← lit (Reg.put (wordsFoR ws)))
    discard <| p.run abiOf
  let cases : List (QAtomicType × List UInt64 × Array UInt64) :=
    [(.f64, [0x8000000000000000, 0x7ff8000000000001], #[0, 0xc002000000000000, 0x7ff0000000000000]),
     (.f32, [0x80000000, 0x7fc00000], #[0, 0xc0100000, 0x7f800000])]
  for (t, bad, good) in cases do
    if let .error e := check t good then throw (IO.userError s!"canonFloatB at {repr t} refuses canonical words: {e}")
    for b in bad do
      match check t (good.push b) with
      | .error e => unless e.startsWith "w: a" && (e.splitOn "not canonical").length == 2 do
          throw (IO.userError s!"canonFloatB at {repr t} fails {b} with {e}")
      | .ok _ => throw (IO.userError s!"canonFloatB at {repr t} passes the word {b}")

/-- `R`'s Lean value written to `dir` (`writeRel`), its error the program's. -/
def semOut {A B : Obj} (R : Except String (Tab A B)) (dir : String) : IO Unit := do writeRel dir (← IO.ofExcept R)

/-- The closed definitions of `native1a`, one per `Tm` node the plan builds (`tabB`), each written to `out/NAME`:
    by `relc lean` from its Lean value and by the gate's plan from its term, the one list both sides read. -/
def semOuts : List (String × (String → IO Unit)) :=
  [("x", semOut native1a.x), ("un", semOut native1a.un), ("me", semOut native1a.me), ("df", semOut native1a.df),
   ("zr", semOut native1a.zr), ("cm", semOut native1a.cm), ("dm", semOut native1a.dm), ("rn", semOut native1a.rn),
   ("pr", semOut native1a.pr), ("cx", semOut native1a.cx), ("po", semOut native1a.po), ("pl", semOut native1a.pl),
   ("ix", semOut native1a.ix), ("tp", semOut native1a.tp), ("tc", semOut native1a.tc), ("gf", semOut native1a.gf),
   ("le", semOut native1a.le), ("lt", semOut native1a.lt),
   ("ml", semOut native1a.ml), ("sc", semOut native1a.sc), ("ps", semOut native1a.ps), ("mn", semOut native1a.mn),
   ("dv", semOut native1a.dv), ("tm", semOut native1a.tm), ("fc", semOut native1a.fc), ("nl", semOut native1a.nl),
   ("hd", semOut native1a.hd), ("ee", semOut native1a.ee), ("lm", semOut native1a.lm), ("lu", semOut native1a.lu),
   ("ld", semOut native1a.ld), ("l1", semOut native1a.l1), ("rd", semOut native1a.rd), ("gc", semOut native1a.gc),
   ("fm", semOut native1a.fm), ("hy", semOut native1a.hy), ("f1", semOut native1a.f1), ("f3", semOut native1a.f3),
   ("es", semOut native1a.es), ("th", semOut native1a.th), ("fi", semOut native1a.fi), ("sb", semOut native1a.sb),
   ("sf", semOut native1a.sf), ("ss", semOut native1a.ss), ("gb", semOut native1a.gb), ("tk", semOut native1a.tk), ("ln", semOut native1a.ln),
   ("mx", semOut native1a.mx), ("gi", semOut native1a.gi), ("gj", semOut native1a.gj), ("gk", semOut native1a.gk),
   ("gu", semOut native1a.gu), ("gn", semOut native1a.gn), ("gv", semOut native1a.gv),
   ("gx", semOut native1a.gx), ("gy", semOut native1a.gy), ("gz", semOut native1a.gz), ("gw", semOut native1a.gw),("gm", semOut native1a.gm), ("gp", semOut native1a.gp),
   ("cu", semOut native1a.cu), ("pre", semOut native1a.pre), ("suf", semOut native1a.suf),
    ("jl", semOut native1a.jl), ("jr", semOut native1a.jr), ("kl", semOut native1a.kl), ("br", semOut native1a.br),
    ("bl", semOut native1a.bl), ("bc", semOut native1a.bc),
    ("pfx", semOut native1a.pfx), ("sfx", semOut native1a.sfx), ("la", semOut native1a.la), ("ini", semOut native1a.ini),
    ("tl", semOut native1a.tl), ("tw", semOut native1a.tw)]

-- CROSS past `crossMax` pairs fails the run as `Vals.cross` fails, before any column is built
#eval show IO Unit from do
  let p ← IO.ofExcept (Bld.plan do discard <| crossB (← lit (.size 32768)) (← lit (.size 8193)) [] [])
  match p.run abiOf with
  | .error e => unless e.startsWith "cross: values of the left object by values of the right, past the bound 268435456" do
      throw (IO.userError s!"crossB past crossMax fails with {e}")
  | .ok _ => throw (IO.userError "crossB of 32768 × 8193 rows passed `crossMax`")

/-- The native gate's plan: `nativeIO`'s IO statements (its input edge first), each of `semOuts` to `out/NAME`, then
    the computed relation's to `out/arith` and the group ids to `out/gid`. -/
def gatePlan : Lean.Meta.MetaM (Except String Plan) := do
  -- one heartbeat budget per output: the run's single budget is spent by the sum of the outputs, so each new case
  -- would shrink what the others may use
  let bs ← semOuts.mapM fun (x, _) => Lean.withCurrHeartbeats (outputOf ``native1a x ("out/" ++ x))
  let io ← Lean.withCurrHeartbeats (ioOf ``nativeIO)
  return do
    let (bs, (rd, wr)) := (← bs.mapM id, ← io)
    Bld.planIO rd fun ins => do
      wr ins
      for b in bs do b
      mainStepB (arithOut "out/arith"); mainStepB (gidOut "out/gid")

/-- The plan of the IO statements of the program `n` (`ioOf`): its input edge, then its computations and writes. -/
def progPlan (n : Lean.Name) : Lean.Meta.MetaM (Except String Plan) := do
  let io ← ioOf n
  return do let (rd, wr) ← io; Bld.planIO rd wr

/-- The plan `p` computes, run outside Lean in the environment of the module `mod` and the modules on `LEAN_PATH`
    (as `lake env` sets it), where the elaborator's unifier finds the objects' constants (`Obj.named`). -/
unsafe def planInImpl (mod : Lean.Name) (p : Lean.Meta.MetaM (Except String Plan)) : IO Plan := do
  Lean.initSearchPath (← Lean.findSysroot)
  -- `loadExts`: the registry (`Expand.relRegistry`, each program's homes) is an extension; unloaded, a program
  -- reads no home, and a name of the prelude (`⊤(1,L)`'s `1`) resolves to nothing
  Lean.enableInitializersExecution
  let env ← Lean.importModules (loadExts := true) #[{ module := mod }] {}
  let (r, _) ← p.run'.toIO { fileName := "relc-1a", fileMap := default } { env }
  IO.ofExcept r

@[implemented_by planInImpl] opaque planIn (mod : Lean.Name) (p : Lean.Meta.MetaM (Except String Plan)) : IO Plan

/-- The native gate's plan, `gatePlan`. -/
def planIO : IO Plan := planIn `Rel.Lang.TestNative gatePlan

/-- The writes of the plan `p` of `output what to "out"` are those of the Lean value `v`, column for column: each
    written `OwnFile` equal to the one `Db.ownFile` makes of the value's column (the `rel-native` gate's check). -/
def writesAgree {A B : Obj} (what : String) (p : Except String Plan) (v : Except String (Tab A B)) :
    Lean.Meta.MetaM Unit := do
  let p ← match p with | .ok p => pure p | .error e => throwError "{what}: {e}"
  let (_, ws) ← match p.run abiOf with | .ok r => pure r | .error e => throwError "{what}: {e}"
  let x ← match v with | .ok x => pure x | .error e => throwError "{what}: {e}"
  -- each side as `Table.writeVals` writes it: payloads cut to the cells' reach (`ValsB.pack 0`)
  let (xk, xv) ← match ValsB.pack 0 x.key, ValsB.pack 0 x.val with
    | .ok k, .ok v => pure (k, v) | .error e, _ | _, .error e => throwError "{what}: {e}"
  let side (s : String) (cs : List (String × SideCol)) := cs.map fun (p, v) => ("out/" ++ s ++ p, v)
  let want ← match (side "key" (cols _ xk "") ++ side "val" (cols _ xv "")).filterMapM
      (fun (p, v) => do pure ((← ownFile p v).map fun f => (p, f))) with | .ok w => pure w | .error e => throwError e
  let got := ws.toList.filterMap fun (_, vs) => match vs.toList with
    | .str p :: c :: k :: n :: ps :: _ => (p, ·) <$> Reg.get? (α := Db.OwnFile) (.ctor 0 #[ps] #[c, k, n])
    | _ => none
  let flat (pf : String × Db.OwnFile) :=
    (pf.1, pf.2.code, pf.2.kind, pf.2.count.toNat, pf.2.parts.toList.map (·.toList))
  unless got.length == ws.size && got.map flat == want.map flat do
    let g := got.map flat
    let w := want.map flat
    let d := ((g.zip w).filter fun (a, b) => !(a == b)).map fun (a, b) => (a.1, b.1, a.2.1 == b.2.1, a.2.2.1 == b.2.2.1, a.2.2.2.1 == b.2.2.2.1)
    throwError (s!"the plan of `{what}` writes {got.length} of {ws.size} columns, not those of its Lean value ({want.length} wanted); differing (got, want, code, kind, count) {d}; got {g.map (·.1)}; want {w.map (·.1)}")

/-- The plan of `output x to "out"` for the definition `x` of the program `m` from the reading `r` of `m`
    (`Expand.reread m`), which a caller planning each definition of `m` reads once. -/
def planOfRead (m : Lean.Name) (r : Except Err Expand.Read) (x : String) : Except String Plan :=
  outputOfRead m r x "out" >>= Bld.plan

/-- The plan of `output x to "out"` for the definition `x` of the program `m` (`rel_program m`). -/
def planOfIn (m : Lean.Name) (x : String) : Lean.Meta.MetaM (Except String Plan) :=
  return planOfRead m (← Expand.reread m) x

/-- `writesAgree` of the definition `x` of the program `m` against its Lean value `v`, with its own heartbeat budget
    (a block of checks shares one otherwise) and its plan and run times logged. -/
def agree {A B : Obj} (m : Lean.Name) (x : String) (v : Except String (Tab A B)) : Lean.Meta.MetaM Unit := do
  let t ← IO.monoMsNow
  Lean.withCurrHeartbeats do
    let p ← planOfIn m x
    let t1 ← IO.monoMsNow
    writesAgree x p v
    -- a slot of `shareB` not built is inline at each use: a lazy slot is expected, any other failure is a bug and fails the gate
    let (g, bugs) := p.toOption.elim ("", []) fun p =>
      let fs := p.globals.toList.filterMap (·.failure?)
      let bugs := (fs.filter (!·.lazy)).map (·.msg)
      (s!", slots built {(p.globals.filter (!·.res.isEmpty)).size} of {p.globals.size}, lazy slots {(fs.filter (·.lazy)).length}, closed build failed {bugs.length}{
        if bugs.isEmpty then "" else s!" ({bugs.eraseDups})"}", bugs)
    Lean.logInfo m!"{m}.{x}: plan {t1 - t} ms, run {(← IO.monoMsNow) - t1} ms{g}"
    unless bugs.isEmpty do throwError "{m}.{x}: closed build failed {bugs.eraseDups}"

-- the plan's writes are those of the Lean value `native1a.x` (`Tab.conv`: swapped, then `canon`)
#eval show Lean.Meta.MetaM Unit from do writesAgree "x" (← plan) native1a.x

/-- `NAME.io` (IO design B) of the program `NAME` elaborated in the module `MOD`, both read by Lean's name parser,
    run in the environment of the modules on `LEAN_PATH` (as `planIO`); its error is the program's. -/
unsafe def runIOImpl (mod name : String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules (loadExts := true) #[{ module := mod.toName }] {}
  (← IO.ofExcept (env.evalConst (IO Unit) {} (name.toName ++ `io)))

@[implemented_by runIOImpl] opaque runIO (mod name : String) : IO Unit

end Rel.Lang.TestNative

open Rel.Lang.Plan Rel.Lang.TestNative in
/-- The `relc-1a` exe (`lakefile.lean`): `c FILE`, `lean DIR`, `plan DIR`, as the module doc says; `run MOD NAME`
    runs the reads, computations and writes of the program `NAME` (`runIO`); `c FILE MOD NAME` and
    `plan DIR MOD NAME` print and run the plan of that program's IO statements (`progPlan`) instead of the gate's. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["run", mod, name] => runIO mod name
    | ["c", file] => IO.FS.writeFile file (← IO.ofExcept (relc abiOf (← planIO)))
    | ["c", file, mod, name] =>
      IO.FS.writeFile file (← IO.ofExcept (relc abiOf (← planIn mod.toName (progPlan name.toName))))
    | ["lean", dir] => for (x, w) in semOuts do w (System.FilePath.mk dir / "out" / x).toString
    | ["plan", dir] => IO.Process.setCurrentDir dir; discard <| (← planIO).exec abiOf
    | ["plan", dir, mod, name] =>
      let p ← planIn mod.toName (progPlan name.toName); IO.Process.setCurrentDir dir; discard <| p.exec abiOf
    | ["g", file] => IO.FS.writeFile file (← IO.ofExcept (gplan codes >>= relc abiOf))
    | _ => throw (IO.userError
      "usage: relc-1a c FILE [MOD NAME] | lean DIR | plan DIR [MOD NAME] | g FILE | run MOD NAME")
    pure 0
  catch e => IO.eprintln e; pure 1
