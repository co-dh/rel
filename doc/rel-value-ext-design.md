# Extension parameter on rel's value types

qlean needs guid; rel deleted it (bc34d39). Option B: rel's value types take a parameter `X` for values rel knows
nothing about, rel is at `X := Empty`, qlean instantiates `X` and owns guid's storage, codes, wire format and kernels.

## 1. Shapes and their price in rel

All counts are from `.lake/build/refactor-index.db` at bc34d39, over this view (user declarations only):

```sql
create temp view nu as select d.src, d.module, d.dst, d.in_type from dep d
  join decl_info i on i.name = d.src and i.module = d.module and i.internal = 0 and i.kind in ('def','thm','opaque');
-- S(T): signatures naming a type of T   select count(distinct src) from nu where in_type = 1 and dst in T;
-- C(t): tactic `cases`/`rcases` sites   select count(distinct src) from nu where dst = t || '.casesOn';
```

| count                                              | QAtomicType | QAtom | QValue | Enc | QTable |
|----------------------------------------------------|-------------|-------|--------|-----|--------|
| S: signatures naming it                            | 330         | 83    | 93     | 216 | 22     |
| C: user proofs that `cases` on it                  | 80          | 5     | 9      | 54  | 0      |
| matcher definitions over it (`%.match_%`, casesOn) | 11          | 4     | 5      | 5   | 6      |

| S by layer                         | Kernel | KernelSpec | Run | Rel (rest) | total | modules |
|------------------------------------|--------|------------|-----|------------|-------|---------|
| `{QValue, Enc, QTable}`            | 85     | 13         | 88  | 98         | 284   | 47      |
| the above + `{QAtomicType, QAtom}` | 170    | 19         | 140 | 194        | 523   | 62      |

Facts every shape rests on, each checked by compiling a scratch file with this toolchain (Lean 4.28.0):
- A `match` over `T Empty` needs **no** arm for `ext (e : Empty)`: the match compiler closes the missing case itself.
  A tactic `cases v` does produce the goal, with `e : Empty` in context, and it needs `nomatch e` where the
  combinator after `<;>` does not close it. So the arm count is the C row, not the matcher row.
- A type parameter on an `@[extern]` def is erased from the C signature (`size_t f(size_t, lean_object*)` with or
  without `{X}`), so making a kernel generic changes nothing in `crate/`.
- Inside `namespace N`, `abbrev N.QValue := M.QValue A` takes precedence over an opened `M.QValue`, while
  `QValue.atom`, `.atom` and `v.f` still reach `M.QValue`'s constructors and functions. So a layer fixed at one `X`
  keeps every signature it has today.

| shape | what changes                                  | signatures  | `cases` | other cost                     |
|-------|-----------------------------------------------|-------------|---------|--------------------------------|
| (a)   | `X` and `ext` on QAtomicType, QAtom, Enc      | 189 generic | 139     | QAtomicType no longer an enum  |
| (b)   | QValue over a (type, atom, kind) triple       | 284         | 0       | 56 declarations through a view |
| (c)   | one constructor `QValue.ext : X → QValue X`   | 98 generic  | 9       | at most 7 arms in generic code |
| (d)   | `opaque Ext : Type` as `IndexCell` is, no `X` | 0           | 9       | live arm; no proofs about guid |

- **(a)** With the abbrev fact above only the Kernel and KernelSpec signatures change (170 + 19); Run and Rel stay.
  `QAtomicType` is today an enumeration, a `UInt8` scalar field of `QValue.vector`/`slices` and `DecidableEq` by
  `ctorIdx`; with `ext : X → …` it becomes a boxed object, so the layout the Rust reads changes and `DecidableEq`
  needs `[DecidableEq X]`. Requirement 3 then fails unless `width (.ext _) = none`, which makes every reader treat an
  extension column apart from the fixed-width ones anyway: the parameter on the atom types buys nothing (c) lacks.
- **(b)** A function matching `.vector .long n e a` needs the type argument to *be* `QAtomicType`, so rel at
  `QAtomicType` and qlean at `QAtomicType ⊕ G` share no function unless each such match goes through an injection
  class. 56 declarations name a `QValue.vector/atom/slices` together with a `QAtomicType` or `QAtom` constructor
  (`nu a join nu b` on `src`, `a.dst` one of the three, `b.dst` a constructor of the two).
- **(d)** is not option B: an opaque type is inhabited, so rel's matches need a real arm, and nothing is provable.

## 2. Chosen shape (c), and what it is an instance of

```lean
namespace Rel.Ext            -- the family; `Rel.QValue` stays the name of rel's own instance
mutual
inductive QValue (X : Type) | atom … | vector … | dict … | table … | keyed … | slices … | func … | err … | enum …
  | ext : X → QValue X       -- last, so constructor tags 0–8 and every field layout are unchanged
inductive QTable (X : Type) | mk : Array String → Array (QValue X) → UInt8 → QTable X
inductive Enc (X : Type) | bytes … | bits … | syms … | foR … | alp … | enum … | gen : Array (QValue X) → Enc X
end
end Rel.Ext
abbrev Rel.QValue := Ext.QValue Empty     -- likewise Rel.QTable, Rel.Enc
```

- Existing concepts tried first. `general`/`Enc.gen` (boxed elements): a guid column would be one heap object per
  element, and there is no guid atom to box because `QAtom` is closed. A new `Enc` kind: `Enc` carries no type, the
  header `t : QAtomicType` does, so it needs `QAtomicType.ext` too and becomes (a).
- The concept reused is `QValue.slices`: a list kept as one packed payload under a `QValue` constructor of its own,
  beside the boxed form. `ext` is that, with the payload type supplied by the caller. The gap that makes it a new
  constructor: `slices` fixes its payload to `Enc` under a `QAtomicType` header, and guid has neither in rel.
- `X` is the whole extension *value*, atom or column, so one constructor serves both and `QAtomicType`, `QAtom`,
  `QAtom.type`, `width`, `code`, `Coc.nullOf`, `Dep.Carrier.null`, `atomOfBits`, `bitsOf` stay closed and total.
- `Enc` and `QTable` take `X` only because `gen` and `mk` hold `QValue X`; no constructor of theirs is added.

`code`, `width`, null and order are not extended inside rel. rel has no `ofCode` or `letter` (no index hit), and
`QAtomicType.code` has one dependent. qlean extends each table over the sum type with `Sum.elim`, an existing
concept: `code := Sum.elim QAtomicType.code fun _ => 2`. rel's interface to `X` is one class, holding only what a
rel function that recurses through `gen`, `dict` or `table` must do at an `ext`:

```lean
class Rel.ValueExt (X : Type) where
  identical : X → X → Bool      -- q's `~`, read by `Eval.identicalFuel`
  WF : X → Prop                 -- read by `QValue.WFAt`
instance : Rel.ValueExt Empty := ⟨nofun, nofun⟩
```

The QValue-recursive functions of the kernel layer are `Eval.identicalFuel`, `QValue.WFAt`, `QValue.marking`,
`Dep.Carrier.of?`, `Db.ownFile`, `Kernel.internConcat`, `QValue.slicesExpand` (the 7 arms); only the first two act
on an `ext`. A field is added when another one must.

## 3. What becomes generic, and why requirement 3 holds by the types

| layer                        | at      | signatures changed | new `ext` arms          |
|------------------------------|---------|--------------------|-------------------------|
| `Rel.Kernel.*`               | `{X}`   | 85                 | at most 7               |
| `Rel.KernelSpec.*`           | `{X}`   | 13                 | 0                       |
| `Rel.Run.*`, the rest of Rel | `Empty` | 0 of 186           | 0 arms, 9 `cases` goals |

- 98 is an upper bound: a kernel is generalised when qlean applies it to its own values, one declaration at a time,
  and every `Empty` caller still elaborates because `X` unifies.
- No extension byte reaches a kernel. `X` occurs only under `QValue.ext`; `QAtomicType`, `QAtom` and the six
  byte-payload constructors of `Enc` do not mention it; a function generic in `X` can move an `x : X` and nothing
  else, and `ValueExt` has no field returning bytes or a width.
- No width above 8 reaches a kernel. Add `QAtomicType.width_le : t.width = some w → w ≤ 8` and give `findVec`,
  `memberVec`, `gatherBytes` (`Rel/Kernel/Search.lean` 48, 91, 78) the erased hypothesis `(hw : w.toNat ≤ 8)`. Their
  `else` branches and the Rust `u128` paths (`crate/src/search.rs`: `Kind::U128`, `Ptab<u128>`, the 16-byte order at
  1103) are then unreachable and deleted. Dependents to thread `hw` through: 7, 5 and 34.

## 4. What qlean writes

```lean
namespace QLean
open Rel Rel.Ext
structure Guid where (hi lo : UInt64) deriving DecidableEq
inductive GuidExt                                    -- X: a guid atom, or a packed column of 16 * n bytes
  | atom (g : Guid)
  | vector (n : USize) (b : ByteArray) (attr : Option (UInt8 × IndexCell))
instance : ValueExt GuidExt := ⟨GuidExt.identical, GuidExt.WF⟩     -- `identical` is an `@[extern "qrs_guid_…"]`
abbrev QValue := Ext.QValue GuidExt                  -- shadows Rel.QValue inside QLean: no signature changes
abbrev QTable := Ext.QTable GuidExt;  abbrev Enc := Ext.Enc GuidExt
@[match_pattern] abbrev QValue.guid (g : Guid) : QValue := .ext (.atom g)
@[match_pattern] abbrev QValue.guids (n : USize) (b : ByteArray) (a : Option (UInt8 × IndexCell)) : QValue :=
  .ext (.vector n b a)
abbrev Atom := QAtom ⊕ Guid                          -- requirement 1: rel's atoms plus guid, no constructor copied
abbrev AtomTy := QAtomicType ⊕ Unit
def AtomTy.code : AtomTy → Int8 := Sum.elim QAtomicType.code fun _ => 2
end QLean
```

A qlean verb matches `.guid g` or `.guids n b a` first and calls its qrs kernel (find, member, eq, gather, wire),
then falls through to rel's generic kernel. It cannot pass guid bytes to `findVec`: `16 ≤ 8` has no proof.

## 5. Choice and migration

- (c) is the only parametrised shape where `QAtomicType` and `QAtom` are untouched: the 330 and 83 signatures naming
  them, the 85 `cases` proofs on them and the enumeration layout the Rust reads are kept.
- Requirement 3 is a consequence of where `X` occurs plus one hypothesis, not a rule callers follow.
- rel's programs and theorems read as today: `Empty` needs no arm in a `match`, and the abbrev keeps their names.
- Cost in rel: at most 98 signatures, 7 arms, 9 `cases` goals, 46 dependents of the three dense kernels.

Commits, each green on `lake build RelCore RelKernel RelRun Rel rel-native`:

| # | commit                                                                                   | diff (lines) | agent  |
|---|------------------------------------------------------------------------------------------|--------------|--------|
| 1 | `Value.lean`: family in `Rel.Ext` with `X` and `ext`, the three abbrevs, `ValueExt`;     | 130          | opus   |
|   | `open Rel.Ext` in each module naming a constructor qualified (at most 62); the 9 goals   |              |        |
| 2 | `Value.lean`: its own `Column.*`, `Enc.WF`, `Enc.raw`, `QValue.*` to `{X}`; `WFAt` arm   | 150          | opus   |
| 3 | rest of `Rel.Kernel.*` and `Rel.KernelSpec.*` to `{X}`; `identicalFuel` arm              | 150          | opus   |
| 4 | `width_le`, `hw` on the three dense kernels, their `else` branches deleted               | 120          | opus   |
| 5 | `crate/src/search.rs`: `u128` kinds, tables and tests deleted; `sh crate/build.sh syms`  | 150          | sonnet |
| 6 | qlean (its own repository): section 4, its qrs kernels, an arm per verb that takes guid  | not priced   | opus   |

- 1 is one commit because the abbrevs break qualified constructor names until the `open` lines are in. The `open`
  lines are typing a sonnet agent can do once the opus agent has `Value.lean` building. It must also confirm that
  `crate/` builds no `QValue` constructor by a tag past 8 and that `relc`'s output is unchanged.
- 2 and 3 are mostly signature edits (`Enc` to `Enc X` under `variable {X : Type}`), but a proof that breaks on the
  new case is Lean proving, so they are dispatched as opus with the module list in the prompt.
- 4 and 5 do not depend on 1 to 3 and can land first; 5 needs 4.
- Not checked here: that qlean's sources sit in `namespace QLean` with `open Rel` (the abbrev shadowing needs it),
  and which of the 98 kernel signatures qlean calls; qlean's index predates the split and names `QLean.QValue`.
