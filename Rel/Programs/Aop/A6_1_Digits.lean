/-! # Digits of a number, B&dM §6.1 (`AOP/A6_1_Digits.lean`), in Rel: no row ported

`Decimal ::= wrap Digit⁺ | snoc (Decimal, Digit)` is a host inductive datatype with its own initial algebra; Rel has no
recursive datatype object other than the array `[α]`, so `val`, `digits` and `⦇[g,h]⦈` over `Decimal` have no term. -/

-- not ported: cata_converse_eq (Freyd.Alg.RelSet.Digits.cata_converse_eq, 06-recursive.typ:16): `⦇g,h⦈° = g° wrap ∪ h° (⦇g,h⦈°×𝟙) snoc` is the fold of the `Decimal` initial algebra; no `Decimal` object, and the list instance `⦇[nil,snoc]⦈` is already `foldUP`
-- not ported: val_converse_eq (…Digits.val_converse_eq, 06-recursive.typ:23): the same equation at `val = ⦇[embed,op]⦈`, over `Decimal`
-- not ported: op_recip_iff (…, 06-recursive.typ:31): `↔` between two pointwise statements about `op`, which reads `10·n + d` on host `Nat`
-- not ported: op_recip_defined (…, 06-recursive.typ:34): element quantifier over `Nat`/`Digit`, same `op`
-- not ported: embed_recip_defined (…, 06-recursive.typ:37): element quantifier over `Digit⁺`, no `Digit⁺` object
