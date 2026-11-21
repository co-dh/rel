# kchain handoff (stop at the call budget)

Branch `kchain` = ff3c4fc + merge of integ6 f000a93 (the fsqrt unary rows were NOT in ff3c4fc).

Done:
- `Rel/Kernel/Scan.lean`: `chain`, `chainAll`, `segAll`; `kscan op rev s t n (seg : Option Enc) es (pre post := [])`.
  Old calls with a variable `seg : Enc` type-check by the `Enc → Option Enc` coercion and the default chains; a
  literal dot constructor (`.pos`, `.foR …`) must be written `some .pos` (the expected type is `Option Enc`).
- Rust `crate/src/scan.rs` (`chain`, `Scan.seg : Option`, `pre` on every load, `post` on every answer block,
  div/mod steps refused), `crate/src/ffi/scan.rs` (9-arg export), `crate/src/lean.rs` (`B::unbox_u64`).
  `cargo test --features std --release kscan`: 4 passed.
- Laws: `raw_kscanChain` (general; `raw_kscan` its empty-chain case), `mapM_chain`, `chainAll_ok`, `chainAll_nil`,
  `kscan_last`, `kscan_closed`, `kscan_foR`, `colMap_chain` (RepCanon; `colMap_get`, `colMap_raw` its cases),
  `kscan_ok` (GenKBits; `seg : Option Enc`).
- `colMap op n a b t s pre post` = one `kscan … none [a, b] pre post`: no `colConst n 1` column.
- ScanTest: chained `#guard` with `seg = none` and a `decide` on `chain`; a div step refused.

Left (in order):
1. One-pass element-wise verbs in `Rel/Run/Arith.lean` (`wideCol`, `ftoCols`, `fstepCols`, `fmapCols`) and
   `Rel/Run/Cast.lean`: `colMap op n a b t s (pre := widen s) (post := extra ++ [(.fto t, 0)])`; the keep flag is a
   second pass `colMap .first n w w .u1 .i64 [] [(.ne, nulWord)]` (kscan writes one column; the flag is a function
   of the value column, so no second export). `widen`: f32 → `[(.f32to64, 0)]`, ordNum r → `[(.cast r .i64, 0)]`,
   else `[]`. `imod` keeps several passes (x used twice). Specs in `Rel/RepTabArith.lean` follow from `colMap_chain`.
2. Unary rows f32/f64 → f64, floor → i64 via `[(.ffloor,0), (.cast .f64 .i64,0)]` (check `castWord f64 i64` gives
   2^63 off-range so the keep flag drops it): `unaryDen` (Rel/Lang/Den.lean), `rowDens`, prims
   (Rel/Run/Lang/Syntax.lean), GenSound `rowOK_unary`, tests `unaryT`/`sqrtIntT` in Rel/Lang/TestFloatArith.lean.
3. Drop `canon` after `keep` in `Tab.unary`/`Tab.cast`; one lemma "keep of a canonical table is canonical"
   (`Tab.keep`, Rel/Run/SetOps.lean:20).
4. Measure sqrt over 10^6 f64 and f32 rows before (96326f9) and after with `CAP_JOB=… cap`.
5. Gates, PLAN.md S8, architecture §4, ffi export doc comment (still describes the 7-arg signature).
