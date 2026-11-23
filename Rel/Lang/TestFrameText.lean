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
    -- `[0-9]+`: state 0 the start, 1 after a digit, 1 accepting; any other element has no step, so no run. A
    -- one-character `"0"` at `Q×C` is a `char` (`Tup.char?`); at `N ⟶ [C]` below, `"7"` is a text
    dfa : Q×C ⟶ Q ≜ {((0,"0"),1),((0,"1"),1),((0,"2"),1),((0,"3"),1),((0,"4"),1),((0,"5"),1),((0,"6"),1),
      ((0,"7"),1),((0,"8"),1),((0,"9"),1),((1,"0"),1),((1,"1"),1),((1,"2"),1),((1,"3"),1),((1,"4"),1),((1,"5"),1),
      ((1,"6"),1),((1,"7"),1),((1,"8"),1),((1,"9"),1)}
    nums : N ⟶ [C] ≜ {(0,"2024"),(1,"12a"),(2,""),(3,"7"),(4,"a1")}
    -- "2024" and "7" are digits only; "" ends in the start state 0, not accepting
    check dom(nums match(dfa, {(∗,0)}, {(1,1)})) = {(0,0),(3,3)}
    -- every digit run, every piece of one included: "12a" has "1" "2" "12", "a1" has "1"
    check nums matchAll(dfa, {(∗,0)}, {(1,1)}) = {(0,"2"),(0,"0"),(0,"4"),(0,"20"),(0,"02"),(0,"24"),(0,"202"),
      (0,"024"),(0,"2024"),(1,"1"),(1,"2"),(1,"12"),(3,"7"),(4,"1")}

#guard frameText.failures.map toString == []

end Rel.Lang.TestFrameText
