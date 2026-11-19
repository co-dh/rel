import Rel.Lang.Test.Common
import Rel.Lang.Test.Kern45

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-- The kernel body `k` and the old body `o` run on what `K` knows of their sides, as equal sets of rows. -/
def sameOn {A B : Obj} [BEq (A.El × B.El)] (k o : Rel A B) (K : Known A B) : Bool :=
  match k.runE K, o.run K with
  | .ok a, some b => sameSet a.toList b.toList
  | _, _ => false

/-- The value column of the definition `d` of `kernT45` as a known domain: `x`'s holds the cell `1 2` twice and the
    empty cell, `pa`'s the pair `(3 1, 2)` twice. -/
def knownOf (d : String) (A B : Obj) {C : Obj} : Known B C :=
  match get kernT45.expanded d A B with
  | some t => ⟨some ⟨t.n, t.val⟩, none⟩
  | none => {}

-- the rows on the keys `X` given (`ofVals`, `after`), with empty cells and duplicate rows, at atom, tuple and `arr`
-- value sides
#guard sameOn (GenK.ofVals _ _ fun X => Tab.mem X) (Gen.ofVals _ _ fun X => CRel.mem X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.length X) (Gen.ofVals _ _ fun X => CRel.length X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.sum X) (Gen.ofVals _ _ fun X => CRel.Arr.sum X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.setify X) (Gen.ofVals _ _ fun X => CRel.setify X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.atPos .long 1) (Gen.atPos .long 1) (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.nil _ .long) (Gen.nil _ .long) (knownOf "x" .long (.arr .long))
#guard sameOn (GenK.ofVals _ _ fun X => Tab.uncons X) (Gen.ofVals _ _ fun X => CRel.uncons X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.unsnoc X) (Gen.ofVals _ _ fun X => CRel.unsnoc X)
    (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.uncat X) (Gen.ofVals _ _ fun X => CRel.uncat X) (knownOf "x" .long (.arr .long))
#guard sameOn (GenK.ofVals _ _ fun X => Tab.tau X) (Gen.ofVals _ _ fun X => CRel.τ X) (knownOf "r" .long .long) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.tau X) (Gen.ofVals _ _ fun X => CRel.τ X) (knownOf "x" .long (.arr .long)) &&
  sameOn (GenK.ofVals _ _ fun X => Tab.tau X) (Gen.ofVals _ _ fun X => CRel.τ X)
    (knownOf "w" .long (.prod .long .long))
#guard sameOn (GenK.after _ _ fun P => Tab.snoc P) (Gen.after _ _ fun P => CRel.snoc P)
    (knownOf "pa" .long (.prod (.arr .long) .long)) &&
  sameOn (GenK.after _ _ fun P => Tab.cons P) (Gen.after _ _ fun P => CRel.cons P)
    (knownOf "pc" .long (.prod .long (.arr .long))) &&
  sameOn (GenK.after _ _ fun P => Tab.cat P) (Gen.after _ _ fun P => CRel.cat P)
    (knownOf "pp" .long (.prod (.arr .long) (.arr .long))) &&
  sameOn (GenK.after _ _ fun P => Tab.zip P) (Gen.after _ _ fun P => CRel.zip P)
    (knownOf "pp" .long (.prod (.arr .long) (.arr .long)))
-- `Λ`, `E` at an atom and a tuple side; `Λ` on every key of `N` (`un`'s), so cells `[]` occur: on keys `D` that
-- miss part of `dom R` the old `CRel.lamOn` also keeps `R`'s other keys (`r.val`: `(1, [2])`), the kernel body
-- only `D ≫ Λ(R)`; the program's `≫` cuts the old rows to the same set (`lr` above)
#guard match get kernT45.expanded "r" .long .long, get kernT45.expanded "w" .long (.prod .long .long),
    get kernT45.expanded "un" .long .long with
  | some r, some w, some u =>
    sameOn (GenK.lam _ _ false (.tab (.ok r))) (Gen.lam _ _ false (.tab (.ok r))) ⟨some ⟨u.n, u.key⟩, none⟩ &&
    sameOn (GenK.lam _ _ false (.tab (.ok w))) (Gen.lam _ _ false (.tab (.ok w))) ⟨some ⟨u.n, u.key⟩, none⟩ &&
    sameOn (GenK.E _ _ false (.tab (.ok r))) (Gen.E _ _ false (.tab (.ok r))) (knownOf "x" .long (.arr .long)) &&
    sameOn (GenK.E _ _ false (.tab (.ok w))) (Gen.E _ _ false (.tab (.ok w))) (knownOf "x" .long (.arr .long))
  | _, _, _ => false
-- `est`, `thin` on the pair test `𝟙 ∩ q` (`q` the pairs `b ≤ c` of `1…3`), on the keys `X` with duplicate rows
#guard match get kernT45.expanded "q" (.prod .long .long) (.prod .long .long) with
  | some q =>
    let qk := GenK.meet _ _ true false (GenK.id _) (.tab (.ok q))
    let qo := Gen.meet _ _ true false (Gen.id _) (.tab (.ok q))
    sameOn (GenK.est .long qk) (Gen.est .long qo) (knownOf "x" .long (.arr .long)) &&
    sameOn (GenK.thin .long qk) (Gen.thin .long qo) (knownOf "x" .long (.arr .long))
  | none => false
-- `≤`, `<` with both sides known, one, or none (`r`'s value column holds `3` twice); `succ` on the keys
def cmpK (k o : Rel .long .long → Rel .long .long) (i : Nat) : Bool :=
  match get kernT45.expanded "r" .long .long, get kernT45.expanded "un" .long .long with
  | some r, some u =>
    let K := [(⟨some ⟨r.n, r.key⟩, some ⟨r.n, r.val⟩⟩ : Known .long .long), ⟨none, some ⟨r.n, r.val⟩⟩,
      ⟨some ⟨r.n, r.val⟩, none⟩, {}]
    sameOn (k (.tab (.ok u))) (o (.tab (.ok u))) (K.getD i {})
  | _, _ => false
#guard (List.range 4).all (cmpK GenK.leq Gen.leq)
#guard (List.range 4).all (cmpK GenK.lt Gen.lt)
#guard cmpK GenK.succ Gen.succ 2

end Rel.Lang.Test
