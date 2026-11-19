import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- a nested literal (§c): each leaf position its own object, the side their product
open Rel.Programs.prelude in
rel_program nested where
    obj X = {A,B}
    obj N = 0…1
    L : X×N ⟶ N×X ≜ {((A,0),(1,B)),((B,1),(0,A))}
    print L
#guard nested.ok && nested.prints == ["L = {((A, 0), (1, B)), ((B, 1), (0, A))}"] &&
  (get nested.expanded "L" (.prod .long .long) (.prod .long .long)).map (·.toList) ==
    some [((0, 0), (1, 1)), ((1, 1), (0, 0))]
#eval errAt "obj X = {A,B}\nL ≜ {((A,B),A),(A,B)}\n" 2 "nest alike"

/-! Declared types (§e). -/

-- a body that is not the declared type; a definition with none, told the type it has
#eval errAt "obj X = {A,B}\nobj N = 0…1\nf : X ⟶ N ≜ 𝟙(X)\n" 3 "`f` is declared X ⟶ N, but its body is X ⟶ X"
#eval errAt "obj X = {A,B}\nf ≜ 𝟙(X)\n" 2 "`f` has no type; it is f : X ⟶ X"
#eval errAt "obj X = {A,B}\nf(R : X ⟶ X) ≜ R°\n" 2 "`f` has no type; it is f(R : X ⟶ X) : X ⟶ X"
-- one generic definition at two objects in one program: its variables instantiated at each use
open Rel.Programs.prelude in
rel_program generic where
    obj X = {A,B}
    obj N = 0…1
    sw : α×β ⟶ β×α ≜ ⟨π₂,π₁⟩
    print {((A,0),(A,0))}sw
    print {((1,B),(1,B))}sw
#guard printed generic.prints == ["{((A, 0), (0, A))}", "{((1, B), (B, 1))}"]
-- the declared type determines an object the body leaves open: `nil`'s source and element
open Rel.Programs.prelude in
rel_program declNil where
    obj N = 0…3
    e : 1 ⟶ [N] ≜ nil
    print e
#guard printed declNil.prints == ["{(∗, [])}"]
-- `typesOf` prints each definition's head as it is declared
def heads : List String := ["f : X ⟶ X", "g(R : α ⟶ β) : β ⟶ α", "_≼_(R : α ⟶ β, S : β ⟶ γ) : α ⟶ γ"]
def headsSrc : String := "obj X = {A,B}\n" ++
  String.join ((heads.zip ["𝟙", "R°", "R S"]).map fun (h, b) => s!"{h} ≜ {b}\n")
#eval do
  let p ← match ← readIn (preludeScope) headsSrc with | .ok p => pure p | .error e => throwError "{e}"
  match ← Lean.Elab.Command.liftTermElabM (typesOf (some p)).run with
  | .ok ts => unless ts == heads do throwError "the heads print as {ts}"
  | .error e => throwError "{e}"
-- a `where` item; a test takes no type of its own
open Rel.Programs.prelude in
rel_program whereItem where
    obj B = 0…1
    f : B×B ⟶ B ≜ a where a ≜ π₂
    print {((0,1),(0,1))}f
#guard printed whereItem.prints == ["{((0, 1), 1)}"]
#eval errAt "obj X = {A,B}\nh(S : X ⟶ X) : X ⟶ X ≜ 𝟙 ⊑ S\n" 2 "the test `h` has no type of its own"

/-! Array literals (§c): two or more items juxtaposed, or `[…]`; an element position is one object over the
    elements of all rows' arrays there, at any depth and on either side; printed as it is read. -/

open Rel.Programs.prelude in
rel_program arrs where
    obj N = -3…9
    obj K = {a,b}
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    xc : 1 ⟶ [N] ≜ ⟨{(∗,3)}, ⟨{(∗,1)}, ⟨{(∗,2)}, nil⟩cons⟩cons⟩cons
    check x = xc
    check {(∗,[3 1 2])} = xc
    check {(∗,[1])} = ⟨{(∗,1)},nil⟩cons
    check {(∗,[1] [2 3])} = ⟨{(∗,[1])},⟨{(∗,2 3)},nil⟩cons⟩cons
    check {(∗,(1,2) (3,4))} = ⟨{(∗,(1,2))},⟨{(∗,(3,4))},nil⟩cons⟩cons
    print x
    print {(a b,1)}
    print {(∗,(1,2) (3,4))}
    print {(∗,[1] [2 3])}
    print {((a,1 2),[3])}
    print {(a,-1 2),(b,[])}
    print {(∗,[1 2] [])}
    print {(3 1 2,a b)}
    print {(∗,[[]] [[1]])}

#guard arrs.ok && printed arrs.prints == ["{(∗, 3 1 2)}", "{(a b, 1)}", "{(∗, (1, 2) (3, 4))}", "{(∗, [1] [2 3])}",
  "{((a, 1 2), [3])}", "{(a, -1 2), (b, [])}", "{(∗, [1 2] [])}", "{(3 1 2, a b)}", "{(∗, [[]] [[1]])}"]
#guard (get arrs.expanded "x" .long (.arr .long)).map (·.toList) == some [((0 : Int64), [(3 : Int64), 1, 2])]
-- a printed literal reads back as itself
#eval trips ["{(∗, 3 1 2)}", "{(∗, [1] [2 3])}", "{((a, 1 2), [3])}", "{(b, [])}", "{(∗, (1, 2) (3, 4))}"]
-- an element position whose arrays are all empty, a word in no object, rows nesting differently, a comma
def arrE : String := "obj N = 0…9\n"
def emptyErr : String := "the object of [] cannot be read off an empty array: write nil(A,[O])"
-- nothing determines the object: the error at the literal
#eval errAt (arrE ++ "print {(∗,[])}\n") 2 emptyErr (col := some 7)
#eval errAt (arrE ++ "print {(∗,[[]] [])}\n") 2 emptyErr (col := some 7)
#eval errAt (arrE ++ "print {(∗,[])} ∪ {(∗,[])}\n") 2 emptyErr (col := some 7)
-- an untyped definition names the type its body has, the object left open a variable
#eval errAt (arrE ++ "e ≜ {(∗,[])}\n") 2 "`e` has no type; it is e : Rel.Programs.prelude.«1» ⟶ [α]"
-- the context determines it (§c): the other side of a check, the other operand, the declared type, the
-- composition, the pair
open Rel.Programs.prelude in
rel_program arrCtx where
    obj N = 0…9
    obj K = {a,b}
    e : 1 ⟶ [N] ≜ nil
    x : 1 ⟶ [N] ≜ {(∗,1 2)}
    check e = {(∗,[])}
    check {(∗,[])} = e
    check e ⊑ {(∗,[])}
    check x ∪ {(∗,[])} = {(∗,1 2),(∗,[])}
    check x ∩ {(∗,[])} = 𝟘(1,[N])
    check x − {(∗,[])} = x
    d : 1 ⟶ [N] ≜ {(∗,[])}
    check d = e
    nn : 1 ⟶ [[N]] ≜ {(∗,[[]])}
    check nn = ⟨e,nil⟩cons
    c : 1 ⟶ N ≜ {(∗,[])}{([],3),([1],4)}
    check c = {(∗,3)}
    check ⟨{(∗,[])},{(∗,a)}⟩ = ⟨e,{(∗,a)}⟩
    check {(∗,[] [3])} = ⟨e,⟨{(∗,[3])},nil⟩cons⟩cons
    print d
    print nn
#guard arrCtx.ok && printed arrCtx.prints == ["{(∗, [])}", "{(∗, [[]])}"]
-- words two objects hold: open too, fixed by the context, else the error at the literal
def twoObjs : String := "obj A = {a,b}\nobj B = {a,c}\n"
open Rel.Programs.prelude in
rel_program twoObjsX where
    obj A = {a,b}
    obj B = {a,c}
    x : A ⟶ B ≜ {(a,a)}
    print x
#guard printed twoObjsX.prints == ["{(a, a)}"]
#eval errAt (twoObjs ++ "print {(a,c)}\n") 3 "the elements [a] are in [B, A]; write the literal after its object" (col := some 7)
-- a wrong expectation is a failed check, not an object error
open Rel.Programs.prelude in
rel_program wrongCheck where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,1 2)}
    check x = {(∗,[])}
#guard wrongCheck.failures.any fun e => (e.msg.splitOn "check failed").length > 1
#eval errAt (arrE ++ "e ≜ {(∗,1 12)}\n") 2 "no declared object has the elements [1, 12]"
#eval errAt (arrE ++ "e ≜ {(∗,1 2),(∗,3)}\n") 2
  "the rows of a literal nest alike: found 3, expected the form of 1 2"
#eval errAt (arrE ++ "e ≜ {(∗,(1,2) 3)}\n") 2 "the rows of a literal nest alike: found 3, expected the form of (1, 2)"

/-! Signed numbers (§a, §c): a range `-3…3`, signed literal words, `succ ≤ <` and the value verbs on it, each
    against Lean's `Int` (`div` floors and `mod` takes the divisor's sign, as q's: `Int.fdiv`, `Int.fmod`); a print
    lists numbers by value. -/

def zs : List Int := (List.range 7).map fun k : Nat => (k : Int) - 3
open Rel.Programs.prelude in
rel_program signed where
    obj Z = -3…3
    obj K = {a,b}
    x : K ⟶ Z ≜ {(a,-1),(b,2),(a,-3)} -- a comment, after a signed literal
    print x
    print Λ(x)
    print x − {(a,-3)}
    print {(-1,-1)}−{(2,2)}
    s : Z ⟶ Z ≜ 𝟙(Z) succ
    le : Z ⟶ Z ≜ 𝟙(Z) ≤
    lt : Z ⟶ Z ≜ 𝟙(Z) <
    W : Z×Z ⟶ Z×Z ≜ 𝟙(Z×Z)
    pl : Z×Z ⟶ Z ≜ W plus
    tm : Z×Z ⟶ Z ≜ W times
    mi : Z×Z ⟶ Z ≜ W minus
    dv : Z×Z ⟶ Z ≜ W div
    md : Z×Z ⟶ Z ≜ W mod
    mx : Z×Z ⟶ Z ≜ W max
    mn : Z×Z ⟶ Z ≜ W min

def ints (R : Tab .long .long) : List (Int × Int) := R.toList.map fun (a, b) => (a.toInt, b.toInt)

#guard signed.ok
#guard signed.prints == ["x = {(a, -3), (a, -1), (b, 2)}", "Λ(x) = {(a, -3 -1), (b, [2])}",
  "x − {(a, -3)} = {(a, -1), (b, 2)}", "{(-1, -1)} − {(2, 2)} = {(-1, -1)}"]
-- `succ` at `-1` gives `0`, at the top `3` nothing; `≤`, `<` the numeric order
#guard (get signed.expanded "s" .long .long).map ints == some ((zs.filter (· < 3)).map fun a => (a, a + 1))
#guard [("le", fun (a b : Int) => decide (a ≤ b)), ("lt", fun a b => decide (a < b))].all fun (n, f) =>
  match get signed.expanded n .long .long with
  | some R => sameSet (ints R) ((zs.flatMap fun a => zs.map (a, ·)).filter fun (a, b) => f a b)
  | none => false
-- each verb on every pair of `Z`: a row exactly where the result is in `Z` and the divisor is not `0`
#guard [("pl", fun (a b : Int) => some (a + b)), ("tm", fun a b => some (a * b)), ("mi", fun a b => some (a - b)),
    ("dv", fun a b => if b == 0 then none else some (a.fdiv b)),
    ("md", fun a b => if b == 0 then none else some (a.fmod b)),
    ("mx", fun a b => some (max a b)), ("mn", fun a b => some (min a b))].all fun (n, f) =>
  match get signed.expanded n (.prod .long .long) .long with
  | some R => sameSet (R.toList.map fun ((a, b), c) => ((a.toInt, b.toInt), c.toInt))
      ((zs.flatMap fun a => zs.map (a, ·)).filterMap fun (a, b) =>
        (f a b).bind fun c => if zs.contains c then some ((a, b), c) else none)
  | none => false
-- `-5…-1` is a range; `3…-3` is empty, refused at its last number; a word other than a number is no range bound
open Rel.Programs.prelude in
rel_program negRange where
    obj Z = -5…-1
    print 𝟙(Z) succ
#guard negRange.prints == ["𝟙(Z) succ = {(-5, -4), (-4, -3), (-3, -2), (-2, -1)}"]
#eval errAt "obj X = {A}\nobj Z = 3…-3\n" 2 "the range 3…-3 is empty: -3 is below 3" (col := some 11)
#eval errAt "obj Z = -3…3\nf ≜ {(-4,0)}\n" 2 "no declared object has the elements [-4]"
#eval trips ["{(A, -1)}", "{((-1, B), -20)}", "R − S"]


end Rel.Lang.Test
