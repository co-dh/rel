import Rel.Programs.FrameJoin

/-! q's date literal `2024.01.15` and time literal `2024.01.15D12:30:00.5` at an object of `date`, `datetime`
    (`Elab.qForm`): days, nanoseconds since 1970-01-01, proleptic Gregorian. Expected day numbers worked by hand:
    2024-01-01 is 54·365 + 13 leap days (1972…2020) = 19723, so 2024.01.15 = 19737 and 2024.02.29 = 19723 + 31 + 28 =
    19782; 2000.02.29 = 10957 + 59 = 11016; 1969.12.31 = -1; 1900.01.01 = -(70·365 + 17) = -25567. -/

namespace Rel.Lang.TestDateLit

open Rel.Db.Csv

/-- The CSV writer's day text at `.` read back by the literal's reader: every day of 1896–2104 (the century rule at
    1900, 2000, 2100) and both ends of the years 0001–9999. -/
#guard (List.range 76500).all fun k => let z := (k : Int) - 27100; ymd 46 (dayText 46 z) == some z
#guard [-719162, 2932896].all fun z => ymd 46 (dayText 46 z) == some z
#guard dayText 46 19737 == bytes "2024.01.15"

open Rel.Programs.prelude Rel.Programs.frame in
rel_program dateLitT where
    obj N
    obj D : date
    obj T : datetime
    -- a set literal, the day integer form beside it, the same rows
    d : N ⟶ D ≜ {(0,2024.01.15),(1,1969.12.31),(2,2024.02.29),(3,1970.01.01),(4,1900.01.01),(5,2000.02.29)}
    e : N ⟶ D ≜ {(0,19737),(1,-1),(2,19782),(3,0),(4,-25567),(5,11016)}
    check d = e
    -- a pair of dates
    check {(2024.01.15,2024.02.29)} = {(19737,19782)}
    -- `<` against the integer form: d(i) < e(j) for some j, every i but the largest, 2 (19782)
    check dom(d < e°) = {(0,0),(1,1),(3,3),(4,4),(5,5)}
    -- times: 19737·86400 + 12·3600 + 30·60 seconds and half of one; the last nanosecond before 1970
    t : N ⟶ T ≜ {(0,2024.01.15D12:30:00.5),(1,1969.12.31D23:59:59.999999999),(2,1970.01.01D00:00:00)}
    check t = {(0,1705321800500000000),(1,-1),(2,0)}

#guard dateLitT.failures.map toString == []

-- a date at an object of another atom
/-- error: x -/
#guard_msgs in
rel_program dateAtLongT where
    obj N
    x : N ⟶ N ≜ {(0,2024.01.15)}

/-- error: x -/
#guard_msgs in
rel_program dateAtFloatT where
    obj N
    obj F : f64
    x : N ⟶ F ≜ {(0,2024.01.15)}

-- no such day: February 30, month 13, February 29 of a century year not divisible by 400
/-- error: x -/
#guard_msgs in
rel_program feb30T where
    obj N
    obj D : date
    x : N ⟶ D ≜ {(0,2024.02.30)}

/-- error: x -/
#guard_msgs in
rel_program month13T where
    obj N
    obj D : date
    x : N ⟶ D ≜ {(0,2024.13.01)}

/-- error: x -/
#guard_msgs in
rel_program feb29T where
    obj N
    obj D : date
    x : N ⟶ D ≜ {(0,1900.02.29)}

-- beyond the range of `datetime`: nanoseconds from 1970 in `i64` end at 2262.04.11D23:47:16.854775807
/-- error: x -/
#guard_msgs in
rel_program stampRangeT where
    obj N
    obj T : datetime
    x : N ⟶ T ≜ {(0,2262.04.12D00:00:00)}

end Rel.Lang.TestDateLit
