import Rel.Lang.TestNative
import Rel.Programs.Mss

/-! The first program of `Rel/Programs` in the native gate (`test/native/progs.txt`): `Programs.mss` on its five inputs
    `x : K ⟶ [N]`, read from a table directory and the two sides `x mss` and `x scan` written beside it, from files to
    files. The gate compares the native run's files with `relc plan`'s and `relc run`'s. -/

namespace Rel.Lang.TestNativeApp

open Rel.Programs.prelude Programs.mss in
rel_program mssApp where
    input x : K ⟶ [N] from "x"
    xm : K ⟶ N ≜ x mss
    xs : K ⟶ N ≜ x scan
    output xm to "xm"
    output xs to "xs"

-- The inputs of `mssApp`, written to the current directory as the table directory `x` its own `output` writes: the
-- five inputs of `Programs.mss` (the gate's `relc run` names `mssInputs`, runs its `io`).
open Rel.Programs.prelude Programs.mss in
rel_program mssInputs where
    xo : K ⟶ [N] ≜ x
    output xo to "x"

end Rel.Lang.TestNativeApp
