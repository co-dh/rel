# nullband4 handoff (branch of agent-acc666318eecd10c7, base b9b7f87 + merge --no-ff 4e9fbd9)

Done
- Expand.lean `objInfo` `.elems`: structure-instance fields moved to one column (parse error at 27:114).
- `Gen.oneV n : Vals .one n × Bool := ((), true)`; `Expand.valsE` `.one` emits it (was a bare `()`: kernel
  "application type mismatch Prod.fst ()" in every rel_program with a one-element object).
- `Vals.gather` `.one` gathers the positions `.pos` of `n` and drops them, so an index past `n` is refused as on every
  other side; `Vals.gather_row` `.one` arm from `Arr.gather_row`; `row_of_codes`/`codes_of_row` `.one` arms (RepCanon).
- CSV: a `1` column (key of `1 ⟶ N`) is a long column of code 0 with the element's name (`Expand.ioCols`
  `.base n, .one`; `Table.csvEncs` writes `colConst k 0` for `.inl k`; `toCsv`/`ofCsv` `.one` take one part; the
  `S+1` drops/adds the right `1`'s part (`(0, .pos)`); `encVals .one` takes its count from its part).
- cargo test --features std: 88 passed (before any crate change of this agent; none made).

Left
- Step 3 (Vals (.sum (.atom t) .one) = one in-band-null foR Arr) not started; see report.
