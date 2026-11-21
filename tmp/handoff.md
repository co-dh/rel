# kchain handoff (checkpoint at call 40)

Branch `kchain` = ff3c4fc + merge of integ6 f000a93 (the fsqrt unary rows were NOT in ff3c4fc).

Done:
- `Rel/Kernel/Scan.lean`: `chain`, `chainAll`, `segAll`; `kscan op rev s t n (seg : Option Enc) es (pre post := [])`.
  Old calls type-check by the `Enc → Option Enc` coercion and the default chains. Elaborates alone.
- Rust `crate/src/scan.rs` (`chain`, `Scan.seg : Option`, `pre` on every load, `post` on every answer block,
  div/mod steps refused), `crate/src/ffi/scan.rs` (9-arg export), `crate/src/lean.rs` (`B::unbox_u64`).
  `cargo test --features std --release kscan`: 4 passed.

Left:
- Lean laws that unfold `kscan`: `Rel/KernelSpec/Scan.lean` raw_kscan (generalise to chains; old statement by
  specialisation), `Rel/KernelSpec/Closure.lean:111` kscan_closed, `Rel/RepCols.lean:321` kscan_foR,
  `Rel/RepCanon.lean:117` colMap_get, `Rel/Lang/GenKBits.lean:1100` kscan_ok.
- `colMap` (Rel/Run/Gather.lean:53) to `seg = none`; one-pass unary/cast/fstep in Rel/Run/Arith.lean, Cast.lean.
- Unary rows f64/i64 out; drop canon after keep; tests; measurement; docs.
