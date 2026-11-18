# Kernel replacement table (PLAN 6.0)

Input: the 99 rows of `/data/tmp/rel-gates/rel/extern.tsv` (= `crate/RELK.txt`) and the refactor index of
`/home/dh/repo/rel` at `1eee0d1`. Target: `doc/rel-architecture.zh.typ` §4 (primitives `scan`, `scatter`;
optimisations `gather`, `asc`, `distinct`; one `packed` encoding; atoms `u1 char i8 i16 i32 i64 f32 f64 sym`).

## 1. Method

- **Roots** (Rel's own runtime and programs): every non-theorem declaration in `Rel.Run.Lang.*`,
  `Rel.Run.CRel*Def`, `Rel.Run.AC3Def`, `Rel.Programs.*`, and `Rel.Lang.*` except the `*Spec` modules
  (tests, `EmitC`, `RelRep`, `Rows`, `Den`): 6382 declarations.
- **Reach**: closure of the roots along `dep` (`src → dst`), entering only non-theorem declarations, so a lemma
  that mentions a kernel does not pull it in: 7482 declarations.
- **Class R**: the export's `@[extern]` def is in the reach. **Class Q**: it is not (reached only from q code,
  q-only tests and lemmas, or from nothing).
- **Cone** of a Q export: closure along `dep` reversed (`dst → src`), all kinds. No cone member is in the reach,
  so deleting a cone breaks nothing that Rel runs.
- Every R export was checked by its shortest root path; all start at a Rel operator or program
  (`Alg.canonC`, `Cmap`, `Casc`, `CsymDiv`, `Alg.deltaStepC`, `Lang.Bits.*`, `Lang.Plan.abi`, `Cfilter`).
- "Users" below = distinct declarations that name the export (`use_site.parent`), lemmas included.

| class | exports |
| ----- | ------- |
| R     | 77      |
| Q     | 22      |

## 2. Class Q: deleted with their cones (step 6.0a)

| export                        | declaration   | users | cone (besides itself) |
| ----------------------------- | ------------- | ----- | --------------------- |
| qlean_coc_ew_val              | Ew.foRVal     | 2     | 1                     |
| qlean_coc_ew_val_atom         | Ew.foRValAtom | 2     | 1                     |
| qlean_coc_mask_cmp            | Ew.foRCmp     | 2     | 1                     |
| qlean_coc_mask_cmp_vv         | Ew.foRCmpVV   | 2     | 1                     |
| qlean_coc_match               | foRMatch      | 2     | 4                     |
| qlean_coc_scale               | Ew.foRScale   | 2     | 1                     |
| qlean_coc_val_vv              | Ew.foRValVV   | 2     | 1                     |
| qlean_ew_cast                 | Ew.castTo     | 1     | 0                     |
| qlean_ew_chain_enc            | Ew.chainEnc   | 2     | 2                     |
| qlean_ew_eq_ids               | Ew.eqIds      | 2     | 1                     |
| qlean_ew_floor                | Ew.floor      | 1     | 0                     |
| qlean_ew_mon                  | Ew.mon        | 1     | 0                     |
| qlean_group_cells             | groupCells    | 2     | 2                     |
| qlean_match_bytes             | matchBytes    | 4     | 6                     |
| qlean_match_syms              | matchSyms     | 2     | 4                     |
| qlean_over_groups             | overGroups    | 5     | 4                     |
| qlean_search_match_ids        | matchIds      | 2     | 4                     |
| qlean_search_match_syms_ids   | matchSymsIds  | 2     | 4                     |
| qlean_structural_scatter_ids  | scatterIds    | 4     | 3                     |
| qlean_structural_scatter_syms | scatterSyms   | 2     | 2                     |
| qlean_structural_shift        | shiftBytes    | 4     | 3                     |
| qlean_structural_shift_foR    | shiftFoR      | 2     | 1                     |

The union of the cones: 47 declarations (internal ones included), by module (`Rel.` and `Rel.Kernel.` dropped):

| module                | declarations deleted                                                                     |
| --------------------- | ---------------------------------------------------------------------------------------- |
| Elementwise           | Ew.eqIds Ew.foRCmp Ew.foRCmpVV Ew.foRScale Ew.foRVal Ew.foRValVV Ew.foRValAtom Ew.floor  |
|                       | Ew.castTo Ew.mon Ew.chainEnc Ew.Build.runEnc                                             |
| Search                | foRMatch matchBytes matchIds matchSyms matchSymsIds matchColumn sameEncoded              |
| Structural            | shiftBytes shiftFoR scatterIds scatterSyms assignSyms                                    |
| Reduce                | groupCells overGroups                                                                    |
| Eval.Val              | Eval.identical Eval.sameColumn                                                           |
| Run.Code              | Alg.Code.eqAt                                                                            |
| AlgTest               | Alg.instBEqQValue                                                                        |
| KernelSpec.EwEnc      | Verify.foRScale_spec Verify.shiftFoR_spec Verify.foRCmpVV_bitAt Verify.foRValAtom_spec   |
|                       | Verify.foRValVV_spec Verify.foRCmp_bitAt Verify.runEnc_elems Verify.shiftBytes_size      |
|                       | Verify.foRVal_spec                                                                       |
| KernelSpec.Group      | Verify.overGroups_spec Verify.overGroups_groupIds Verify.overGroups_buckets              |
|                       | Verify.overGroups_eq                                                                     |
| KernelSpec.Assign     | Verify.scatterIds_spec Verify.assignSyms_interned                                        |
| KernelSpec.Structural | Verify.groupCells_til                                                                    |

Not declarations, so not in `dep`, and deleted with the cone: the `#guard`/`decide` command sites naming a cone
member in `Kernel.ElementwiseTest` (6), `AlgTest` (1), `KernelSpec.EwEnc`, `KernelSpec.Assign`,
`KernelSpec.Structural`. `Verify.overStep_fold` (`KernelSpec.Group`) names a cone member in its syntax but has no
`dep` edge to it: re-check it after the deletion builds.

## 3. Class R: replacement by the five kernels

Recipes used by more than one row (each a composition of the five; the optimisation kernel's theorem ties it
to `scan`/`scatter` as in §4 of the design):

| recipe  | composition                                                                                          |
| ------- | ---------------------------------------------------------------------------------------------------- |
| CODE    | `asc(es)` → `distinct` → `scan(add)` numbers the group starts → `scatter` through the permutation    |
| DICT    | `asc` on the `arr char` column → `distinct`: the sorted dictionary without repeats                   |
| RANK    | `asc` → `scatter(perm, til)`                                                                         |
| CONCAT  | `scan(add)` of the part sizes gives offsets → per part `scatter(off + til, part, n)` into one output |
| LOOKUP  | concat `(hay, j)` and `(needle, i)` → `asc` → `scan(first)` fills the hay position forward →         |
|         | `scatter` back to `i`; absent needles keep the fill (the hay count): the `gather` recipe, i.e. a `≫` |
| EXPAND  | `scan(add)` of the widths → `scatter(i)` at the run starts → `scan(max)` fills → `gather` the source |
| WHERE   | `scan(add)` of the bits → `scatter(count − 1, til)`, a `0` bit sent to an index ≥ the output length  |
| SEGFOLD | `gather` the rows → segmented `scan(op)` → last element of each segment                              |

Class `encoding` = removed by the one `packed` encoding (6.2, 6.3): the operation is `Enc.raw`/`ofRaw` or a
block-layout detail of `pack.rs`, not a kernel. Class `R4` = a runtime export by owner decision R4.

| declaration           | class       | users | replacement                                                          |
| --------------------- | ----------- | ----- | -------------------------------------------------------------------- |
| Coc.over              | scan        | 3     | fold = last of `scan(op)`                                            |
| overBytes             | scan        | 7     | fold = last of `scan(op)`                                            |
| allBelow              | scan        | 5     | fold `scan(lt)` then fold `scan(and)`                                |
| Ew.foRShift           | scan        | 5     | map `scan(add)` by a constant                                        |
| Ew.val                | scan        | 77    | map `scan(add/sub/mul/min/max/fadd/…)`                               |
| Ew.bit                | scan        | 12    | map `scan(and/or/not)` on `u1`                                       |
| Ew.cmp                | scan        | 35    | map `scan(eq/lt)` (+ `not`, swapped operands)                        |
| enumIds               | scan        | 9     | map `scan` (null → `nullId`), fold `scan(min)` for the first bad row |
| enumIdsFoR            | scan        | 3     | map `scan` (null → `nullId`), fold `scan(min)` for the first bad row |
| tilLongs              | scan        | 87    | prefix `scan(add)` over the width-0 constant-1 column                |
| Scan.scan             | scan        | 3     | prefix `scan(add/mul/min/max/first)`                                 |
| scatterPacked         | scatter     | 7     | `scatter`                                                            |
| gatherBits            | gather      | 5     | `gather`                                                             |
| gatherBytes           | gather      | 14    | `gather`                                                             |
| gatherFoR             | gather      | 4     | `gather`                                                             |
| gatherPacked          | gather      | 18    | `gather`                                                             |
| gatherFoRIdx          | gather      | 2     | `gather` (index is `packed` too)                                     |
| gatherPackedFoR       | gather      | 2     | `gather` (index is `packed` too)                                     |
| gatherSyms            | gather      | 9     | `gather` of `sym` ids                                                |
| Order.grade           | asc         | 18    | permutation of `asc`                                                 |
| Order.gradeFoR        | asc         | 6     | permutation of `asc`                                                 |
| Order.gradeLane       | asc         | 5     | permutation of `asc`                                                 |
| Order.gradeSyms       | asc         | 4     | permutation of `asc` (`arr char`, MSD)                               |
| Order.gradeIds        | asc         | 4     | permutation of `asc` on order-preserving `sym` ids                   |
| runStarts             | distinct    | 6     | `distinct` (+ the row count as terminator)                           |
| runStartsBits         | distinct    | 4     | `distinct` (+ the row count as terminator)                           |
| runStartsIds          | distinct    | 3     | `distinct` (+ the row count as terminator)                           |
| Order.groupIds        | composition | 17    | CODE                                                                 |
| Order.groupIdsFoR     | composition | 6     | CODE                                                                 |
| Order.rankSlices      | composition | 8     | CODE on an `arr` column (`asc` lexicographic on `arr`)               |
| Order.groupIdsPair    | composition | 9     | CODE on two columns                                                  |
| Order.groupIdsPairIds | composition | 8     | CODE on two columns                                                  |
| Order.idGroups        | composition | 11    | CODE, plus `gather` of the permutation at `distinct`                 |
| Order.groupSizes      | composition | 5     | CODE, then `scan(sub)` of adjacent `distinct` positions              |
| concatBits            | composition | 8     | CONCAT                                                               |
| concatBytes           | composition | 43    | CONCAT                                                               |
| concatFoR             | composition | 6     | CONCAT                                                               |
| hashConcat            | composition | 10    | CONCAT of dictionaries, then DICT and CODE (intern)                  |
| Order.distinctSyms    | composition | 9     | DICT                                                                 |
| Order.internSyms      | composition | 16    | DICT, then CODE (intern)                                             |
| expandBytes           | composition | 33    | EXPAND                                                               |
| findBit               | composition | 5     | LOOKUP                                                               |
| findBitVec            | composition | 3     | LOOKUP                                                               |
| findIdsVec            | composition | 4     | LOOKUP                                                               |
| findScalar            | composition | 6     | LOOKUP                                                               |
| findVec               | composition | 7     | LOOKUP                                                               |
| findSymScalar         | composition | 12    | LOOKUP on order-preserving `sym` ids (inside DICT)                   |
| binBytes              | composition | 6     | LOOKUP with `≤`/`<` (fill from the last hay row)                     |
| memberBits            | composition | 3     | LOOKUP, then map `scan(lt n)`                                        |
| memberIdsVec          | composition | 4     | LOOKUP, then map `scan(lt n)`                                        |
| memberVec             | composition | 5     | LOOKUP, then map `scan(lt n)`                                        |
| Order.ranks           | composition | 7     | RANK                                                                 |
| Order.ranksFoR        | composition | 3     | RANK                                                                 |
| Order.invert          | composition | 6     | RANK on a permutation: `scatter(p, til)`                             |
| bitRowsOver           | composition | 8     | SEGFOLD with `and/or`                                                |
| whereBits             | composition | 55    | WHERE                                                                |
| concatIds             | composition | 9     | `gather` (id remap per part), then CONCAT                            |
| cycleBits             | composition | 4     | `gather` at `(off + til) mod m`: needs an integer `mod` `Op`         |
| cycleIds              | composition | 4     | `gather` at `(off + til) mod m`: needs an integer `mod` `Op`         |
| Ew.chain              | composition | 6     | sequence of map `scan`s (a fused form needs its theorem)             |
| Coc.alpEncode32       | encoding    | 6     | ALP form deleted                                                     |
| Coc.alpEncode64       | encoding    | 7     | ALP form deleted                                                     |
| Coc.alpEncodeBelow32  | encoding    | 5     | ALP form deleted                                                     |
| Coc.alpEncodeBelow64  | encoding    | 6     | ALP form deleted                                                     |
| concatALP             | encoding    | 6     | ALP form deleted (its non-ALP case is CONCAT)                        |
| gatherAlp             | encoding    | 4     | ALP form deleted (its non-ALP case is `gather`)                      |
| Coc.alpDecode32       | encoding    | 5     | ALP form deleted; f32 is an order-preserving code                    |
| Coc.alpDecode64       | encoding    | 6     | ALP form deleted; f64 is an order-preserving code                    |
| longRows              | encoding    | 6     | `Enc.raw` read of an index column                                    |
| Coc.encodeBelow       | encoding    | 6     | `ofRaw` picks each block's width; no "below" variant                 |
| Column.blockStart     | encoding    | 27    | block index of `packed` (`pack.rs`, internal)                        |
| Order.idLongs         | encoding    | 4     | ids are codes; no fixed lane width to widen from                     |
| Ew.widen              | encoding    | 18    | width is per block; f32→f64 needs a conversion `Op`                  |
| Db.ownWrite           | R4          | 3     | runtime export: IO, writes a column file                             |
| Coc.decode            | R4          | 55    | runtime export: `packed` decode (`Enc.raw`)                          |
| Coc.encode            | R4          | 25    | runtime export: `packed` encode (`ofRaw`)                            |
| stop                  | R4          | 11    | runtime export: abort with a message                                 |

| class       | R exports |
| ----------- | --------- |
| scan        | 11        |
| scatter     | 1         |
| gather      | 7         |
| asc         | 5         |
| distinct    | 3         |
| composition | 33        |
| encoding    | 13        |
| R4          | 4         |

## 4. Groups for 6.10: reached direct callers, by module

A caller is a reached declaration with a `dep` edge to an R export; one 6.10 step per module row.

| module             | callers | R exports called                                                                      |
| ------------------ | ------- | ------------------------------------------------------------------------------------- |
| Run.Code           | 38      | Ew.cmp Ew.foRShift Ew.val Ew.widen Order.grade Order.gradeLane Order.groupIds         |
|                    |         | Order.groupIdsPair Order.groupIdsPairIds Order.groupSizes Order.idGroups              |
|                    |         | Order.rankSlices Scan.scan concatBits concatBytes concatIds cycleBits cycleIds        |
|                    |         | enumIds enumIdsFoR expandBytes findBitVec findIdsVec findVec gatherBits gatherBytes   |
|                    |         | gatherPacked longRows memberBits memberIdsVec memberVec overBytes runStarts           |
|                    |         | runStartsBits runStartsIds tilLongs whereBits                                         |
| Run.Alg            | 26      | Ew.bit Ew.cmp Ew.val Ew.widen concatBits concatBytes gatherBytes tilLongs whereBits   |
| Kernel.Structural  | 16      | Column.blockStart Coc.decode Coc.encode Order.internSyms allBelow concatALP           |
|                    |         | concatBits concatBytes concatFoR concatIds enumIds findSymScalar gatherAlp gatherBits |
|                    |         | gatherBytes gatherFoR gatherFoRIdx gatherPacked gatherPackedFoR gatherSyms hashConcat |
|                    |         | overBytes                                                                             |
| Run.Lang.Bits      | 10      | Ew.bit Ew.val Order.groupSizes bitRowsOver concatBytes gatherPacked scatterPacked     |
|                    |         | tilLongs whereBits                                                                    |
| Kernel.Sort        | 10      | Coc.decode Order.distinctSyms Order.grade Order.gradeFoR Order.gradeIds               |
|                    |         | Order.gradeSyms Order.groupIds Order.groupIdsFoR Order.groupIdsPair Order.idGroups    |
|                    |         | Order.idLongs Order.internSyms Order.invert Order.ranks Order.ranksFoR findSymScalar  |
| Kernel.Coc         | 9       | Column.blockStart Coc.alpDecode32/64 Coc.alpEncode32/64 Coc.alpEncodeBelow32/64       |
|                    |         | Coc.decode Coc.encode Coc.encodeBelow                                                 |
| Kernel.Search      | 6       | findBit findScalar findVec memberVec                                                  |
| Kernel.Elementwise | 4       | Coc.alpDecode32/64 Coc.decode Coc.encode Ew.bit Ew.chain Ew.cmp Ew.val Ew.widen       |
| Run.Core           | 3       | Coc.decode Ew.bit binBytes tilLongs                                                   |
| Kernel.Value       | 3       | Column.blockStart                                                                     |
| Lang.EmitC         | 2       | Db.ownWrite Ew.bit Ew.cmp Ew.val Order.groupIds Order.idGroups gatherBytes whereBits  |
| Run.Lang.Plan      | 1       | Ew.bit Ew.cmp Ew.val gatherBytes whereBits                                            |
| Run.CRelDef        | 1       | tilLongs                                                                              |
| Kernel.Reduce      | 1       | Coc.over                                                                              |
| Kernel.Need        | 1       | stop                                                                                  |

## 5. Findings for the owner

- **Not writable with the five kernels**: only the four R4 runtime exports, `Db.ownWrite` (IO), `stop` (abort),
  `Coc.encode` and `Coc.decode` (the `packed` codec itself). Every other R export is one of the five or a
  composition of them.
- **The design's "moved out of rel" list contradicts the index**: `til` (`tilLongs`, 87 users, reached from
  `Alg.canonC`, `Casc`, `CRelDef`), `cycle` (`Alg.Code.cut` ← `Alg.codes` ← `Alg.canonC`), `find`/`member`/`bin`
  (`Cmap`, `Alg.deltaStepC`, `CsymDiv`) are reached from Rel operators. They stay in rel as compositions
  (prefix `scan`, `gather`, LOOKUP), not as q verbs.
- **`Op` needs more than the design lists**: an integer `mod` (or `div`) for `cycle`'s index, and a float
  widening conversion (`f32 → f64`) for `Ew.widen`'s `real → float` case.
- **`asc` on `arr` of any atom**: `Order.rankSlices` compares `i64` segments lexicographically; the design names
  only `arr char`.
- **`scatter` must drop an index ≥ `n`**: WHERE and LOOKUP send unselected rows there; the design's
  `scatter(ix, e, n, fill)` does not state what an out-of-range index does.
- **Fused kernels without a theorem today**: `Ew.chain` (a list of maps) and `hashConcat` (intern by a kept hash
  table, `Except` fallback). Under §4 each is either dropped for its recipe or kept with `k = recipe`.
