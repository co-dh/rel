module

public import Rel.Run.Struct
public import Rel.Run.List
public import Rel.Run.Div

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The fixed points `νX : top ∩ f(X)` and `μX : f(X)` of `Tab` (`doc/rel-architecture.zh.typ` §4): a Lean loop
calling the operations until the row count stops, the rule of the old `CRel.fixOn` (`Rel/Run/CRelLoopDef.lean`)
over the five-kernel `Tab.inter` and `Tab.union` (`Rel/Run/SetOps.lean`). Each round is met with (`ν`) or joined to
(`μ`) the table before it, so the rounds form a chain whatever `f` is, and on a chain of canonical tables an equal row
count is an equal relation. -/

namespace Rel

namespace Tab
variable {A B : Obj}

/-- `step` from `X`, at most `n` rounds, until a round leaves the row count `size` as it was; that round's state,
each round's payloads cut (`pack`, `Tab.pack`: `∪` and `canon` keep every input payload whole, so a carried table would
hold the dead elements of all its rounds). The state is the table (`nu`, `mu`) or the table with its frontier
(`star`). A round of `step` that fails fails the loop, and `n` rounds with the count still moving fail it with `out`:
never a truncated chain passed off as the answer. -/
def fixOn {σ : Type} (size : σ → USize) (pack : σ → Except String σ) (out : String) (step : σ → Except String σ) :
    Nat → σ → Except String σ
  | 0, _ => throw out
  | n + 1, X => do let Y ← step X >>= pack; if size Y == size X then pure Y else fixOn size pack out step n Y

/-- **`νX : top ∩ f(X)`**: rounds `X ↦ X ∩ f(X)` from `top` made canonical. A strict round drops a row of the
canonical `top`, so its row count plus one rounds reach the fixed point; the old `Gen.nu`'s `+ 2` is kept. -/
def nu (f : Tab A B → Except String (Tab A B)) (top : Tab A B) : Except String (Tab A B) := do
  let T ← top.canon
  fixOn Tab.n Tab.pack s!"Tab.nu: the row count still moved at {T.n} rows of top" (fun X => f X >>= X.inter)
    (T.n.toNat + 2) T

/-- The most rounds a loop with no bound of its own runs (`star`, the `μ` of `GenK.hylo`): `Int64`'s greatest value,
past the rows any table holds. `USize.size` is `2^64`, a GMP `Nat` that every round's count-down subtracts from. -/
@[noinline] def roundsMax : Nat := 2 ^ 63 - 1

/-- What the `μ` `what` reports when its rounds reach its cap `n`, on either path (`Expand.mus`, `Tab.mu`). -/
def capMsg (what : String) (n : Nat) : String := s!"{what} ran its cap of {n} rounds without reaching a fixed point"

/-- **`μX : f(X)`**: rounds `X ↦ X ∪ f(X)` from `𝟘`, fewer than `cap` of them, the old `Gen.mu`'s bound: `cap`
rounds run fails with `capMsg what cap`, the chain has no fixed point that the program's bound admits. -/
def mu (what : String) (cap : Nat) (f : Tab A B → Except String (Tab A B)) : Except String (Tab A B) := do
  fixOn Tab.n Tab.pack (capMsg what cap) (fun X => f X >>= X.union) (cap - 1) (← Tab.zero)

/-- **`μX : f(X)`, `f` additive in `X`** (`f(X ∪ Y) ⊑ f(X) ∪ f(Y)`, `Tm.linIn`), semi-naive (architecture §4): the
state `(X, Δ)` from `(𝟘, 𝟘)`, a round `T = f(Δ)` (packed), `X' = X ∪ T` and `Δ' = T − X` (packed) from one sort of
`X ++ T` (`unionDiff`), so `f` reads only the rows the round before added; `X` first, so its blocks are moved whole. `X'` is `mu`'s round `X ∪ f(X)`
(`f(X) ⊑ X ∪ f(Δ)` by additivity), hence the same rounds, cap and error; `T` is packed before the `∪`, so `X'`'s
payload is `X`'s and `T`'s live elements, and `Δ'` after, since `−` keeps all of `T ++ X`'s payload. -/
def muLin (what : String) (cap : Nat) (f : Tab A B → Except String (Tab A B)) : Except String (Tab A B) := do
  let Z ← Tab.zero
  let r ← fixOn (fun s => s.1.n) pure (capMsg what cap)
    (fun s => do let p ← s.1.unionDiff (← (← f s.2).pack); pure (p.1, ← p.2.pack)) (cap - 1) (Z, Z)
  pure r.1

/-- **`P ≫ star(R)`** = `P ≫ μX : 𝟙 ∪ R X`, semi-naive (architecture §4.5): the state `(X, Δ)` from `(P, P)`, `P`
made canonical; a round composes only the frontier, `N = Δ ≫ R` (`step` given `ran Δ`, as `loop`'s), `Δ' = N − X`,
`X' = X ∪ Δ'`. `≫` distributes over `∪`, so this is exact for the linear body, where `mu` composes all of `X` each
round. It stops when `X` keeps its row count (`fixOn`), so `Δ'` is empty; each other round adds a row of `X`. -/
def star {K B : Obj} (step : Tab B B → Except String (Tab B B)) (P : Tab K B) : Except String (Tab K B) := do
  let P ← P.canon
  let r ← fixOn (fun s => s.1.n) (fun s => do pure (← s.1.pack, ← s.2.pack)) (capMsg "star" roundsMax)
    (fun s => do let D ← (← s.2.comp (← step (← s.2.ran))).diff s.1; pure (← s.1.union D, D)) roundsMax (P, P)
  pure r.1

/-- **The rounds of a fold** (`fold`, `foldr`, `foldI`), at most `f`: `rest` holds at each key `k` the part of its
array not yet read, `P` its values so far. A round moves the rows of `P` whose key has no element left (`P − dom(el) P`)
to `out`, `peel` splits each `rest` into the element read now and the rest (`cons°` or `snoc°`), and `step` gives the
next values. `P` and `out` have their payloads cut (`Tab.pack`): a step joining two tables that share a payload
(`merge`'s `∪` of its two branches, each carrying `x`) would double it every round, and `out`'s `∪` keeps the payload
of every round's `P`; it ends when `P` is empty, so one round more than the longest array. -/
def foldRounds {K E V : Obj} (peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E)))
    (step : Tab K V → Tab K E → Except String (Tab K V)) :
    Nat → Tab K (.arr E) → Tab K V → Tab K V → Except String (Tab K V)
  | 0, _, P, _ => throw s!"Tab.foldRounds: {P.n} rows still folding when the rounds ran out"
  | f + 1, rest, P, out => do
    if P.n == 0 then return out
    let (el, rest') ← peel rest
    foldRounds peel step f rest' (← (← step P el).pack) (← (← out.union (← P.diff (← (← el.dom).comp P))).pack)

/-- Round `k` of a left fold: `cons°` of what is left of each array, its head read now (index `k` from the start). -/
def peelL {K E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← uncons rest.val)
  pure (← c.comp (← outl c.val), ← c.comp (← outr c.val))
/-- Round `k` of a right fold: `snoc°`, its last element read now (index `k` from the end). -/
def peelR {K E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← unsnoc rest.val)
  pure (← c.comp (← outr c.val), ← c.comp (← outl c.val))

/-- **`P ≫ loop(F)`**: on each `(c, ys)` of `ran P`, the left fold of `F` along `ys` from `c` (`foldRounds`, `peelL`),
a round's step `p ≫ F(ran p)`, `p` the pairs `(acc, y)` it meets; `F` given only those pairs. -/
def loop {K X Y : Obj} (F : Tab (.prod X Y) (.prod X Y) → Except String (Tab (.prod X Y) X))
    (P : Tab K (.prod X (.arr Y))) : Except String (Tab K X) := do
  let D ← P.ran
  P.comp (← foldRounds peelL (fun S el => do let p ← S.pair el; p.comp (← F (← p.ran))) (D.val.2.1.toNat + 2)
    (← D.comp (← outr D.val)) (← D.comp (← outl D.val)) (← zero))

/-- **`P ≫ merge(Q)`**: on each `(x, y)` of `ran P`, the states `((x, y), acc)` from `((x, y), [])`, one round per
element of `cat(x, y)` (`foldRounds`, `peelL` of it as the clock), so `|x| + |y|` rounds. A round takes the head `a`
of `x` where `(a, b) Q (a, b)` (`l = dom(⟨a, b⟩ ≫ diag(Q))`, `Q` given the pairs of heads, read on the diagonal as
`front` reads it) or `y` is empty, else the head `b` of `y`,
and `snoc`s it to `acc`; the result is `acc`. -/
def mergeRound {K B : Obj} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (S : Tab K (.prod (.prod (.arr B) (.arr B)) (.arr B))) (_ : Tab K B) :
    Except String (Tab K (.prod (.prod (.arr B) (.arr B)) (.arr B))) := do
  let xy ← S.comp (← outl S.val); let acc ← S.comp (← outr S.val)
  let x ← xy.comp (← outl xy.val); let y ← xy.comp (← outr xy.val)
  let ux ← x.comp (← uncons x.val); let uy ← y.comp (← uncons y.val)
  let a ← ux.comp (← outl ux.val); let b ← uy.comp (← outl uy.val)
  let h ← a.pair b
  let l ← (← h.comp (← diag q (← h.ran))).dom
  let dy ← uy.dom
  let tx ← l.union (← (← ux.dom).diff dy); let ty ← dy.diff l
  let sx ← (← (← ux.comp (← outr ux.val)).pair y).pair (← snoc (← acc.pair a))
  let sy ← (← x.pair (← uy.comp (← outr uy.val))).pair (← snoc (← acc.pair b))
  (← tx.comp sx).union (← ty.comp sy)

@[inherit_doc mergeRound]
def merge {K B : Obj} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (P : Tab K (.prod (.arr B) (.arr B))) : Except String (Tab K (.arr B)) := do
  let D ← P.ran
  let out ← foldRounds peelL (mergeRound q) (D.val.1.1.toNat + D.val.2.1.toNat + 2) (← cat D)
    (← D.pair (← nil D.key)) (← zero)
  P.comp (← out.comp (← outr out.val))

/-- **`thinL(Q)` on the arrays `X`** = `⦇nil, bump(Q)⦈ʳ` (`thinLDen`: `ys[t]` is `xs[t]` bumped into `ys[t+1]`), the
right fold by `foldRounds` and `peelR`. `bump(Q)` on the pairs `E = (x, ys)` a round meets, `u = ys ≫ cons°` its
`(b, bs)`: `x :: bs` where `(x, b) Q (x, b)` (`up`), `ys` where `(b, x) Q (b, x)` (`down`), `x :: ys` where `ys` is
empty or neither (`lone`); `Q` given only the pairs `(x, b)`, `(b, x)` asked, read on the diagonal (`diag`). -/
def bump {B : Obj} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (p : Tab (.arr B) (.prod B (.arr B))) : Except String (Tab (.arr B) (.arr B)) := do
  let E ← p.ran
  let x ← E.comp (← outl E.val); let ys ← E.comp (← outr E.val)
  let u ← ys.comp (← uncons ys.val)
  let b ← u.comp (← outl u.val)
  let ab ← x.pair b; let ba ← b.pair x
  let up ← (← ab.comp (← diag q (← ab.ran))).dom
  let down ← (← ba.comp (← diag q (← ba.ran))).dom
  let du ← u.dom
  let lone ← (← E.diff du).union (← (← du.diff up).diff down)
  let bs ← u.comp (← outr u.val)
  let r ← (← (← cons lone).union (← up.comp (← cons (← x.pair bs)))).union (← down.comp ys)
  p.comp r

@[inherit_doc bump]
def thinL {B : Obj} {n : USize} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) :=
  do foldRounds peelR (fun P el => do bump q (← el.pair P)) (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

open Rel.Ext Rel.Kernel in
/-- **`F(R)` on the cells `X`** (`mapDen`: `xs F(R) ys` iff `|ys| = |xs|` and `xs[i] R ys[i]`), `R` given on the
elements of the cells. One pass where `R` is a function on them: the elements EXPANDed into a flat payload `v` of `T`
rows (as `sum`), `⟨pos, v⟩ ≫ R` keyed by position, and where each of the `T` positions has exactly one image those
images in position order are the new payload under the same widths (`Vals.cells`). Where some element has no image or
two, the relator is the left fold `⦇nil, ⟨π₁, π₂ ≫ R⟩ ≫ snoc⦈` (`foldRounds`, `peelL`): a cell with an element of no
image drops out, one with `k` images of an element is `k` ways, one round per element of the longest cell. -/
def map {A B : Obj} {n : USize} (R : Tab A B) (X : Vals (.arr A) n) : Except String (Tab (.arr A) (.arr B)) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"map: {n} cells over {m} elements past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    let (T, G, u) ← expand n w
    let v ← Vals.gather T (← colMap .add T (← kgather T G n lo.enc) u) f
    let C ← (⟨T, ← Arr.pos T, v⟩ : Tab .long A).comp R
    if C.n == T && (← C.dom).n == T then canon (⟨n, X, ← Vals.cells n w C.val⟩ : Tab (.arr A) (.arr B))
    else
      foldRounds peelL (fun acc el => do snoc (← acc.pair (← el.comp R))) (m.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`concat` on the cells of cells `X`** = `⦇nil, cat⦈` (the prelude's `concat`, B&dM p.129): the rounds of a left
fold from `[]`, each `(acc, xs) ↦ acc ++ xs`. -/
def flatten {n : USize} (X : Vals (.arr (.arr B)) n) : Except String (Tab (.arr (.arr B)) (.arr B)) := do
  foldRounds peelL (fun acc el => do cat (← acc.pair el)) (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`filter(p)` on the cells `X`**, `P` the relation `p` = `⦇nil, dom(π₂p) snoc ∪ (𝟙 − dom(π₂p)) π₁⦈` (the prelude's
`filter`, B&dM p.66): a left fold, `x` appended where it is a key of `P` (`k = el ≫ dom P`), else `acc` kept; the
`𝟙 − dom(π₂p)` part is `(dom el − dom k) acc`, only keys still folding, so `foldRounds` ends. -/
def filter {n : USize} (P : Tab B B) (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let D ← P.dom
  foldRounds peelL (fun acc el => do
      let k ← el.comp D
      (← snoc (← acc.pair k)).union (← (← (← el.dom).diff (← k.dom)).comp acc))
    (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`takewhile(p)` on the cells `X`**, `P` the relation `p` = `⦇nil, dom(π₁p) cons ∪ (𝟙 − dom(π₁p)) nil⦈ʳ` (the
prelude's `takewhile`, B&dM p.174): a right fold, `x :: acc` where `x` is a key of `P`, else `[]` on `dom el − dom k`. -/
def takewhile {n : USize} (P : Tab B B) (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let D ← P.dom
  foldRounds peelR (fun acc el => do
      let k ← el.comp D
      (← cons (← k.pair acc)).union (← (← (← (← el.dom).diff (← k.dom)).comp acc).comp (← nil acc.val)))
    (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

end Tab

end Rel
