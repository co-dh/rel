import Rel.Run.Bits
import Rel.Run.Comp
import Rel.Run.Div

/-! `Tab.compBits` against `Tab.comp` and `Tab.ldivBits` against `Tab.ldiv`, both run, as lists of rows: duplicates,
empty groups, an empty side, a tuple-valued side, and a matrix of several 1024-bit blocks at a width that is no
multiple of 64. -/

namespace Rel.BitsTest
open Rel.Kernel

/-- The longs `xs` as an `Arr .i64`: their words as `wordsFoR`, through `colArr` for its well-formedness. -/
def arr (xs : List Int64) : Except String (Arr .i64 xs.length.toUSize) :=
  colArr .max _ (wordsFoR (xs.map (·.toUInt64)).toArray) (wordsFoR (xs.map (·.toUInt64)).toArray)

/-- A table of long pairs. -/
def tab (ps : List (Int64 × Int64)) : Except String (Tab .long .long) := do
  let k ← arr (ps.map (·.1)); let v ← arr (ps.map (·.2))
  pure ⟨_, k, by simpa using v⟩

/-- `𝟙` on the longs `xs`. -/
def diag (xs : List Int64) : Except String (Tab .long .long) := tab (xs.map fun x => (x, x))

/-- A pseudo-random relation on `0 .. m-1` with `n` pairs, as `CanonTest.rnd`. -/
def rnd (seed n m : Nat) : List (Int64 × Int64) :=
  (List.range n).map fun i => let x := (seed * 7919 + i * 104729) % 1000003
    (Int64.ofNat (x % m), Int64.ofNat ((x / m) % m))

/-- `compBits` and `comp` of the same tables answer the same rows, both succeeding. -/
def sameComp {A B C : Obj} [BEq A.El] [BEq C.El] (R : Except String (Tab A B)) (S : Except String (Tab B C)) : Bool :=
  match (do Tab.compBits (← R) (← S)), (do Tab.comp (← R) (← S)) with
  | .ok X, .ok Y => X.toList == Y.toList
  | _, _ => false

/-- `ldivBits` and `ldiv` of the same tables answer the same rows, both succeeding. -/
def sameLdiv (R S : List (Int64 × Int64)) (UB UC : List Int64) : Bool :=
  match (do Tab.ldivBits (← tab R) (← tab S) (← diag UB) (← diag UC)),
      (do Tab.ldiv (← tab R) (← tab S) (← diag UB) (← diag UC)) with
  | .ok X, .ok Y => X.toList == Y.toList
  | _, _ => false

-- duplicates on both sides; a key whose middle values meet no `S` row (an empty answer row)
#guard sameComp (tab [(1, 10), (1, 10), (2, 20), (1, 20)]) (tab [(10, 5), (20, 5), (20, 6), (20, 6)])
#guard sameComp (tab [(1, 10), (3, 30)]) (tab [(10, 7), (40, 8)])
-- an empty side
#guard sameComp (tab []) (tab [(1, 2)])
#guard sameComp (tab [(1, 2)]) (tab [])
-- a tuple-valued middle: `R : long ↔ long × long`, `S : long × long ↔ long`
#guard sameComp (do let R ← tab [(1, 10), (2, 20), (1, 20)]; pure (⟨R.n, R.key, (R.val, R.key)⟩ : Tab .long (.prod .long .long)))
  (do let S ← tab [(10, 1), (20, 2), (20, 1), (10, 5)]; pure (⟨S.n, (S.key, S.val), S.val⟩ : Tab (.prod .long .long) .long))
-- 40 keys by 97 values: a 3880-bit answer over four 1024-bit blocks, rows of 97 bits
#guard sameComp (tab ((rnd 1 300 40).map fun (a, b) => (a, b % 31))) (tab ((rnd 2 400 97).map fun (b, c) => (b % 31, c)))

-- `b = 10`: the keys `1 2` share `5`; `20`: key `1`'s `5 6`; `30`, no row of `R`: all of `ran UC`
#guard sameLdiv [(1, 10), (2, 10), (1, 20)] [(1, 5), (2, 5), (1, 6)] [10, 20, 30] [5, 6, 7]
-- `ran S` outside `ran UC`: `20` keeps `6`, the vacuous `30` only `5`
#guard sameLdiv [(1, 10), (2, 10), (1, 20)] [(1, 5), (2, 5), (1, 6)] [10, 20, 30] [5]
-- duplicates; an empty `R` (all vacuous); an empty `S`
#guard sameLdiv [(1, 10), (1, 10), (2, 10)] [(1, 5), (1, 5), (2, 5), (2, 6)] [10] [5, 6]
#guard sameLdiv [] [(1, 5)] [10, 20] [5, 6]
#guard sameLdiv [(1, 10)] [] [10, 20] [5, 6]
-- several blocks: 60 values of `B` by 70 of `C`, 4200 bits
#guard sameLdiv ((rnd 3 200 60).map fun (a, b) => (a % 9, b)) ((rnd 4 300 70).map fun (a, c) => (a % 9, c))
  ((List.range 60).map Int64.ofNat) ((List.range 70).map Int64.ofNat)

end Rel.BitsTest
