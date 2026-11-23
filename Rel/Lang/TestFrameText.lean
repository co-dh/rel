import Rel.Programs.Frame

/-! The text rows of `Rel.Programs.frame` (`doc/dataframe-design.zh.typ` F3): a string is `[C]`, `C` an object of
    `char`; `splitOn` (q's `vs`) and `match` (a regex given as its automaton), against rows worked by hand. -/

namespace Rel.Lang.TestFrameText

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameText where
    obj C : char
    obj N = 0…7
    obj Q = 0…1
    s : N ⟶ [C] ≜ {(0,"a,b"),(1,"a,,b"),(2,""),(3,"ab,"),(4,"x")}
    -- `,` cuts: "a,,b" has an empty piece between the commas, "ab," an empty last piece, "" one empty piece
    check s splitOn({(",",",")}) = {(0,"a" "b"),(1,"a" "" "b"),(2,[""]),(3,"ab" ""),(4,["x"])}
    -- a two-element separator, leftmost non-overlapping: "ababa" at "aba" is "" then "ba"; "abab" at "aba" "" "b"
    t : N ⟶ [C] ≜ {(0,"ababa"),(1,"abab"),(2,"xabay")}
    check t splitOn({("aba","aba")}) = {(0,"" "ba"),(1,"" "b"),(2,"x" "y")}
    -- `[0-9]+`: state 0 the start, 1 after a digit, 1 accepting; any other element has no step, so no run. The digits
    -- are their codes 48…57: a one-element `"0"` in a literal at `Q×C` reads as a text `[C]`, not a `char`
    dfa : Q×C ⟶ Q ≜ {((0,48),1),((0,49),1),((0,50),1),((0,51),1),((0,52),1),((0,53),1),((0,54),1),((0,55),1),
      ((0,56),1),((0,57),1),((1,48),1),((1,49),1),((1,50),1),((1,51),1),((1,52),1),((1,53),1),((1,54),1),
      ((1,55),1),((1,56),1),((1,57),1)}
    nums : N ⟶ [C] ≜ {(0,"2024"),(1,"12a"),(2,""),(3,"7"),(4,"a1")}
    -- "2024" and "7" are digits only; "" ends in the start state 0, not accepting
    check dom(nums match(dfa, {(∗,0)}, {(1,1)})) = {(0,0),(3,3)}

#guard frameText.failures.map toString == []

end Rel.Lang.TestFrameText
