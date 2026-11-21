import Rel.Lang.GenKFold
import Rel.RepWhere
import Rel.RepAsc
import Rel.RepSums
import Rel.Lang.GenKEst
import Rel.Lang.GenKFix
import Rel.Lang.GenKHylo
import Rel.Lang.Den
import Rel.Run.Lang.Expand
import Rel.RepCast

/-! `Tm.gen`: `Expand.node` as a Lean function from a term to its `GenK` code, one `GenK` op per constructor with
    `Expand.node`'s argument order, and `Tm.code` as `Expand.code` (a closed part memoised, `GenK.memo`). Then
    `Tm.gen_sound`: on every term, under `Sound`, the code represents `Tm.den` in every context (an error table
    represents anything: where `Tm.hasCode` is false the run fails), each case one `GenK.*_sound` (`GenKSpec`, `GenKBits`). A bit matrix the code passes on is `Rel.Wf`
    (`Tm.gen_wf`) (`Tab.ofBits` reads back what `compSelM`, `compTabMat`, `ldivTabMat` build); the order law of each
    `Λ` is a theorem (`Vals.lamLaw`: `kasc`'s order is `Obj.lt`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The code each variable `k` reads at the objects a term asks for: `Val`'s twin, what `Expand.node`'s `ρ` binds. -/
abbrev Code := Nat → (A B : Obj) → Rel A B

/-- No variable bound: `Val.empty`'s twin, what a `share` is built under. -/
def Code.empty : Code := fun _ A B => GenK.zero A B

/-- `η` with `k` bound to `r`, `Val.bind`'s twin: a use at other objects reads `𝟘`. -/
def Code.bind (η : Code) (k : Nat) {A B : Obj} (r : Rel A B) : Code := fun j A' B' =>
  if j = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ r else GenK.zero A' B') else η j A' B'

/-- The code environment `η` represents the meaning environment `ρ`, at every variable and object, in every
    context, and every bit matrix it holds is `Rel.Wf`. -/
def Sound (η : Code) (ρ : Val) : Prop := (∀ k A B K, (η k A B).Reps K (ρ k A B)) ∧ ∀ k A B, (η k A B).Wf

/-- `η` with `k` bound to a `Wf` code `r` that represents `X` represents `ρ` with `k` bound to `X`: a fixed point's
    round (`GenK.const` of its table) or a call's argument (`Sound.args`). -/
theorem Sound.bind {η : Code} {ρ : Val} (hs : Sound η ρ) (k : Nat) {A B : Obj} {r : Rel A B} {X : Den A B}
    (hr : ∀ K, r.Reps K X) (hw : r.Wf) : Sound (η.bind k r) (ρ.bind k X) := by
  refine ⟨fun j A' B' K => ?_, fun j A' B' => ?_⟩
  · by_cases hj : j = k
    · simp only [Code.bind, Val.bind, hj, if_true]
      by_cases ho : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := ho
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]; exact hr K
      · rw [dif_neg ho, dif_neg ho]; exact GenK.zero_sound K
    · simp only [Code.bind, Val.bind, hj, if_false]; exact hs.1 j A' B' K
  · by_cases hj : j = k
    · simp only [Code.bind, hj, if_true]
      by_cases ho : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := ho; rw [dif_pos ⟨rfl, rfl⟩]; exact hw
      · rw [dif_neg ho]; trivial
    · simp only [Code.bind, hj, if_false]; exact hs.2 j A' B'

/-- **A program's run-time names bound in statement order** (IO design A.3, the environment `n.io` computes in):
    each `(k, A, B, r, X)` of `bs` bound in turn, `r` a `Wf` code that represents `X` (an input's table,
    `GenK.val_sound`; a run-time definition's code, `Tm.gen_sound` of its body at the names before it), leaves the
    environment sound; then `Tm.gen_sound` of an output's term gives that its table represents its meaning. -/
theorem Sound.inputs {η : Code} {ρ : Val} (hs : Sound η ρ) :
    ∀ bs : List (Nat × (A : Obj) × (B : Obj) × (Rel A B × Den A B)),
      (∀ b ∈ bs, (∀ K, b.2.2.2.1.Reps K b.2.2.2.2) ∧ b.2.2.2.1.Wf) →
      Sound (bs.foldl (fun η b => η.bind b.1 b.2.2.2.1) η) (bs.foldl (fun ρ b => ρ.bind b.1 b.2.2.2.2) ρ)
  | [], _ => hs
  | b :: bs, h => Sound.inputs (hs.bind b.1 (h b (.head _)).1 (h b (.head _)).2) bs fun c hc => h c (.tail _ hc)

/-! ### A row's code: `Expand.primE` run once per row of `kernRows`, at its object variables -/

/-- A row's relations' codes, each with its objects (`Expand.primOf`'s `Res`, as code). -/
abbrev Codes := List ((X : Obj) × (Y : Obj) × Rel X Y)

/-- The codes `xs` bound to the variables `ks`, one for one, the first outermost: `Val.args`'s twin, what a kernel
    twin's parameters are bound to (`Expand.emit`: `Once.binds.zip`, read by `List.lookup`, which finds the first). -/
def Code.args : List Nat → Codes → Code
  | k :: ks, ⟨_, _, x⟩ :: xs => (Code.args ks xs).bind k x
  | _, _ => Code.empty

/-- Every code `Code.args` binds is `Wf` when every argument is. -/
theorem Code.args_wf : ∀ (ks : List Nat) (xs : Codes), (∀ x ∈ xs, x.2.2.Wf) → ∀ j A B, (Code.args ks xs j A B).Wf
  | k :: ks, ⟨X, Y, x⟩ :: xs, hw, j, A', B' => by
    simp only [Code.args, Code.bind]
    split
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hw _ List.mem_cons_self
      · trivial
    · exact Code.args_wf ks xs (fun y hy => hw y (List.mem_cons_of_mem _ hy)) j A' B'
  | [], _, _, _, _, _ | _ :: _, [], _, _, _, _ => trivial

/-- The pattern `o` at the objects `σ` of the variables `vs` (in order), a declared name `.long` (F6): `Prim.objs`
    read backwards. -/
def OExp.at (vs : List String) (σ : List Obj) : OExp → Obj
  | .var _ n => σ.getD (vs.idxOf n) .long
  | .name .. => .long
  | .prod a b => .prod (a.at vs σ) (b.at vs σ)
  | .sum a b => .sum (a.at vs σ) (b.at vs σ)
  | .list a => .arr (a.at vs σ)

/-- The `i`-th code of `xs` when it is at `X ⟶ Y`. -/
def Codes.at (xs : Codes) (i : Nat) (X Y : Obj) : Option (Rel X Y) := match xs[i]? with
  | some ⟨X', Y', x⟩ => if h : X' = X ∧ Y' = Y then some (h.1 ▸ h.2 ▸ x) else none
  | none => none

/-! `rowGens`: each row of `kernRows` with its code as a function of its objects `σ` (`Prim.objs` order) and its
    relations' codes, generated by running `Expand.primE` itself at the placeholders `varObj k` and binding each
    to `σ.getD k .long`, as `Expand.emit` binds them to a generic constant's objects; a variable the constant
    reads only at `.long` (`sum`) stays `.long`, fewest such first. So `rowGens` is `primE`'s choice, not a copy. -/

open Lean Meta Elab Term Expand in
run_elab do
  let pl (k : Nat) := oE ((varObj varAtoms k).getD .long)
  let el (s : Lean.Term) : TermElabM Lean.Expr := do
    let e ← elabTerm s none; synthesizeSyntheticMVarsNoPostponing; instantiateMVars e
  let some' ← el (← `(fun (A B : Obj) (v : Rel A B) => (some ⟨A, B, v⟩ : Option ((A : Obj) × (B : Obj) × Rel A B))))
  let codesTy ← el (← `(Codes))
  let genTy ← el (← `(List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)))
  let bindE := Lean.mkConst ``Option.bind [0, 0]
  let atE ← el (← `(Codes.at))
  let resTy ← el (← `((A : Obj) × (B : Obj) × Rel A B))
  let es ← kernRows.mapM fun (s, _) => do
    let some r := prims.find? (·.sym == s) | throwError "rowGens: the kernel row `{s}` is no row of `prims`"
    let vs := r.vars
    let choices := ((List.range (2 ^ vs.length)).map fun m => (List.range vs.length).map m.testBit).mergeSort
      fun a b => a.count true ≤ b.count true
    let some e ← choices.findSomeM? fun lg => do
        let σ := (List.range vs.length).map fun k => if lg.getD k false then .long else (varObj varAtoms k).getD .long
        let inst (o : OExp) := o.at vs σ
        -- a parameter taken as its pair test (`some true`, §a) is a code at `X×Y ⟶ X×Y`, as `rowDens` reads it
        let ps := r.sig.1.map fun ((x, y), fm) =>
          if fm == some true then (.prod (inst x) (inst y), .prod (inst x) (inst y)) else (inst x, inst y)
        let ts := ps.toArray.map fun (X, Y) => g ``Gen.Fn #[bE true, oE X, oE Y]
        withLocalDeclsDND (ts.map (`x, ·)) fun xs => do
          let some f ← primFit r (inst r.sig.2.1) (inst r.sig.2.2) ts | return none
          let v := f.beta xs
          withLocalDeclD `σ (mkApp (mkConst ``List [0]) (mkConst ``Obj)) fun σv =>
          withLocalDeclD `xs codesTy fun xsv => do
            let body ← (ps.zip xs.toList).zipIdx.foldrM (init := (mkApp3 some' (oE (inst r.sig.2.1)) (oE (inst r.sig.2.2)) v).headBeta)
              fun (((X, Y), x), i) b => do
                let ty := g ``Rel.Rel #[oE X, oE Y]
                pure (mkAppN bindE #[ty, resTy, mkApp4 atE xsv (toExpr i) (oE X) (oE Y), ← mkLambdaFVars #[x] b])
            let sub (z : Lean.Expr) := z.replace fun z => (List.range vs.length).findSome? fun k =>
              if !lg.getD k false && z == pl k then some (mkApp4 (mkConst ``List.getD [0]) (mkConst ``Obj) σv
                (toExpr k) (oE .long)) else none
            return some (← mkLambdaFVars #[σv, xsv] (sub (← instantiateMVars body)))
      | throwError "rowGens: the kernel row `{s}` fits none of {primWrappers} at any choice of its objects"
    pure (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) genTy (toExpr s) e)
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) genTy)
  let val ← mkListLit (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) genTy) es
  addAndCompile (.defnDecl (mkDefinitionValEx `Rel.Lang.rowGens [] ty val .abbrev .safe [`Rel.Lang.rowGens]))

/-- The number of relations row `s` is given: its `prims` entry's, the one `rowGens` was generated from. -/
def rowArity (s : String) : Nat := ((prims.find? (·.sym == s)).map (·.sig.1.length)).getD 0

/-- Row `r`'s code at `A ⟶ B` given its relations' codes `xs`: its `rowGens` entry at `r.objs A B`, as `primE`
    fits it; an error table where it has none there, or where `xs` are not as many as it takes (a `rowGens` entry
    ignores a code past them, which `Prim.den` reads). -/
def primGen (r : Prim) (A B : Obj) (xs : Codes) : Rel A B :=
  if xs.length ≠ rowArity r.sym then .tab (.error s!"Tm.gen: the row `{r.sym}` is given {xs.length} relations") else
  match rowGens.lookup r.sym, r.objs A B with
  | some f, some σ => match f σ xs with
    | some ⟨A', B', v⟩ => if h : A' = A ∧ B' = B then h.1 ▸ h.2 ▸ v else
      .tab (.error s!"Tm.gen: the row `{r.sym}` is not at its objects")
    | none => .tab (.error s!"Tm.gen: the row `{r.sym}` is given relations not at its objects")
  | _, _ => .tab (.error s!"Tm.gen: the row `{r.sym}` has no kernel body at these objects")

#guard rowGens.length = kernRows.length

mutual
/-- `Expand.code` without the constant sharing: a `t` that needs no keys memoised (`GenK.memo`), any other its node. -/
def Tm.code (η : Code) {A B : Obj} (t : Tm A B) : Rel A B :=
  if !t.dem then GenK.memo A B (t.gen η) else t.gen η
termination_by 2 * t.size + 1

/-- `Expand.node`: `t`'s own `GenK` op, its parts by `Tm.code`. A fixed point's variable reads its round's table
    (`GenK.const`); `share` is built under no variable; a row is its `rowGens` entry (`Expand.primE` run once per
    row); a call is its body's code with its arguments' codes bound at `ks` (`Code.args`): what `Expand.spine`'s
    kernel twin computes, the two bound by the differential test (`test/TestCompile.lean`). -/
def Tm.gen (η : Code) {A B : Obj} (t : Tm A B) : Rel A B :=
  match A, B, t with
  | A, B, .val R => GenK.val A B (R, true)
  | A, _, .uni (m := m) U => GenK.uni A m (U, true)
  | A, B, .zero => GenK.zero A B
  | A, _, .id => GenK.id A
  | A, B, .top V => GenK.top A B (V.code η)
  | .prod A B, _, .outl => GenK.outl A B
  | .prod A B, _, .outr => GenK.outr A B
  | A, C, .comp (B := B) R S => GenK.comp A B C S.dem (R.code η) (S.code η)
  | B, A, .conv R => GenK.conv A B (R.code η)
  | A, B, .meet R S => GenK.meet A B R.dem S.dem (R.code η) (S.code η)
  | A, B, .join R S => GenK.join A B R.dem S.dem (R.code η) (S.code η)
  | A, B, .diff R S => GenK.diff A B R.dem S.dem (R.code η) (S.code η)
  | A, _, .dom (B := B) R => GenK.dom A B R.dem (R.code η)
  | B, _, .ran (A := A) R => GenK.ran A B (R.code η)
  | B, C, .ldiv (A := A) R S UB UC => GenK.ldiv A B C (R.code η) (S.code η) (UB.code η) (UC.code η)
  | A, B, .rdiv (C := C) R S UA UB => GenK.rdiv A B C (R.code η) (S.code η) (UA.code η) (UB.code η)
  | A, .prod B C, .pair R S => GenK.pair A B C R.dem S.dem (R.code η) (S.code η)
  | .prod A C, .prod B D, .prod R S => GenK.prod A B C D (R.code η) (S.code η)
  | A, .arr B, .lam R => GenK.lam A B R.dem (R.code η)
  | .arr A, .arr B, .E R => GenK.E A B R.dem (R.code η)
  | _, B, .est Q => GenK.est B (Q.code η)
  | _, .arr B, .thin Q => GenK.thin B (Q.code η)
  | A, .arr B, .nil => GenK.nil A B
  | .arr B, _, .atPos k => GenK.atPos B k
  | _, _, .own R => R.code η
  | _, _, .succ U => GenK.succ (U.code η)
  | _, _, .arith t k U => GenK.arith t k (U.code η)
  | _, _, .leq t U => GenK.leq t (U.code η)
  | _, _, .lt t U => GenK.lt t (U.code η)
  | .arr Y, V, .foldr e S => GenK.foldr Y V S.dem (e.code η) (S.code η)
  | .arr Y, V, .fold e S => GenK.fold Y V S.dem (e.code η) (S.code η)
  | _, _, .share _ R => R.code Code.empty
  | .prod I (.arr Y), V, .foldI e S => GenK.foldI I Y V e.dem S.dem (e.code η) (S.code η)
  | A, B, .var _ k => η k A B
  | A, B, .nu k S b => GenK.nu A B (S.code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .mu k w n b => GenK.mu A B w n fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  -- children `Tm.kids` reads in no shape bound no recursion: `Expand.node` refuses it, as here
  | A, B, .hylo k w b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    if (b.kids k A).isNone then .tab (.error s!"Tm.gen: {w} gives the hylo no children (Tm.kids)") else
    GenK.hylo A B w ((b.kids k A).getD .zero).dem b.dem (((b.kids k A).getD .zero).code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .prim r => primGen r A B []
  | _, _, .arg f x => f.argGen η [⟨_, _, x.code η⟩]
  | _, _, .call ks _ _ b | _, _, .callCv ks _ _ _ b _ => b.code (Code.args ks [])
termination_by 2 * t.size
decreasing_by all_goals simp only [Tm.size] at *; omega

/-- A spine `f` given its later relations' codes `xs` (`Expand.primOf`, `Expand.spine`), in the order `Tm.argDen`
    reads their meanings: a row's code of all of them, or a call's body's code with them bound at its `ks`; `share`
    seen through, built under no variable. A spine headed by neither is an error table. -/
def Tm.argGen (η : Code) {A B : Obj} (t : Tm A B) (xs : Codes) : Rel A B :=
  match A, B, t with
  | A, B, .prim r => primGen r A B xs
  | _, _, .arg f x => f.argGen η (⟨_, _, x.code η⟩ :: xs)
  | _, _, .share _ R => R.argGen Code.empty xs
  | _, _, .call ks _ _ b | _, _, .callCv ks _ _ _ b _ => b.code (Code.args ks xs)
  | _, _, _ => .tab (.error "Tm.gen: a spine headed by neither a row nor a call")
termination_by 2 * t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
end

/-- Whether `primGen r A B` given codes at the objects `xs` returns code, not its error table: the same lookups.
    A `rowGens` entry reads only its codes' objects (`Codes.at`), so `𝟘` at each stands for any code there. -/
def primHasCode (r : Prim) (A B : Obj) (xs : List (Obj × Obj)) : Bool :=
  xs.length == rowArity r.sym && match rowGens.lookup r.sym, r.objs A B with
  | some f, some σ => match f σ (xs.map fun (X, Y) => ⟨X, Y, GenK.zero X Y⟩) with
    | some ⟨A', B', _⟩ => decide (A' = A ∧ B' = B)
    | none => false
  | _, _ => false

mutual
/-- Whether `Tm.gen` emits real code at every node of `t`, by `Tm.gen`'s case split: false exactly where some node's
    `gen` (or `argGen`) returns its error table, where `Tm.gen_sound` holds because the code fails. -/
def Tm.hasCode {A B : Obj} (t : Tm A B) : Bool :=
  match A, B, t with
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. => true
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .est R
  | _, _, .thin R | _, _, .own R | _, _, .succ R | _, _, .arith _ _ R | _, _, .leq _ R | _, _, .lt _ R
  | _, _, .share _ R | _, _, .mu _ _ _ R => R.hasCode
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .foldr R S | _, _, .fold R S | _, _, .foldI R S
  | _, _, .nu _ R S => R.hasCode && S.hasCode
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.hasCode && S.hasCode && U.hasCode && V.hasCode
  | A, _, .hylo k _ b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    (b.kids k A).isSome && ((b.kids k A).getD .zero).hasCode && b.hasCode
  | A, B, .prim r => primHasCode r A B []
  | _, _, .arg (C := C) (D := D) f x => f.argHasCode [(C, D)] && x.hasCode
  | _, _, .call _ _ _ b | _, _, .callCv _ _ _ _ b _ => b.hasCode
termination_by t.size
decreasing_by all_goals simp only [Tm.size] at *; omega

/-- `Tm.argGen`'s case split: the spine `f` given later relations at the objects `xs` has code. -/
def Tm.argHasCode {A B : Obj} (t : Tm A B) (xs : List (Obj × Obj)) : Bool :=
  match A, B, t with
  | A, B, .prim r => primHasCode r A B xs
  | _, _, .arg (C := C) (D := D) f x => f.argHasCode ((C, D) :: xs) && x.hasCode
  | _, _, .share _ R => R.argHasCode xs
  | _, _, .call _ _ _ b | _, _, .callCv _ _ _ _ b _ => b.hasCode
  | _, _, _ => false
termination_by t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
end

#guard (Tm.comp (Tm.call (A := .long) (B := .long) [] `c [] .zero) .id).hasCode
#guard !(Tm.call [] `c [] (Tm.arg (Tm.zero (A := .long) (B := .long)) (Tm.id (A := .long)))).hasCode
#guard !(Tm.arg (Tm.zero (A := .long) (B := .long)) (Tm.id (A := .long))).hasCode
#guard (Tm.ldiv (A := .long) (B := .long) (C := .long) .id .id .id .id).hasCode

/-- The rows whose case of `Tm.gen_sound` is proved (`rowsProved_ok`), each with the objects, as a function of the
    row's `A ⟶ B`, at which its proof reads `LamLaw` (`Tm.LamLawsAt`): none, `A ⟶ [B']` where its table is a `Λ` into
    `B = [B']` (`τ`, `setify`, `inits`), `[σ] ⟶ [[σ] × [σ]]` where it is `Λ(cat°)` on `A = [σ]` (`tails`), `ℕ ⟶ B` itself where
    it numbers a set in `canon`'s order (`asc`). -/
def rowsProved : List (String × (Obj → Obj → List (Obj × Obj))) :=
  let no : Obj → Obj → List (Obj × Obj) := fun _ _ => []
  let cod : Obj → Obj → List (Obj × Obj) := fun A B => match B with | .arr B' => [(A, B')] | _ => []
  [("∋", no), ("inl", no), ("inr", no), ("τ", cod), ("setify", cod), ("snoc", no), ("cons", no), ("cat", no),
   ("uncat", no), ("prefix", no), ("suffix", no), ("uncons", no), ("unsnoc", no), ("inits", cod), ("zip", no), ("length", no), ("sum", no), ("loop", no), ("filter", no), ("concat", no), ("merge", no),
   ("thinL", no), ("F", no), ("positions", no), ("asc", fun A B => [(A, B)]), ("inl°", no), ("inr°", no), ("tails", fun A _ => match A with | .arr σ => [(.arr σ, .prod (.arr σ) (.arr σ))] | _ => []),
   ("takewhile", no), ("sums", no), ("flat", no), ("$", no)] ++ unaryOps.map fun (s, _) => (s, no)

/-- What `Tm.gen_sound` asks of `t`, with `L` for the order law of a `Λ`: `L` at each `Λ`
    and `E` (`E(R) = Λ(∋ ≫ R)`, at `[A] ⟶ [B]`) and at each row `rowsProved` marks, and the body of each fixed
    point positive in its variable (`Tm.pol`, which `Tm.den_mono` reads). -/
def Tm.LamLawsAt (L : Obj → Obj → Prop) : {A B : Obj} → Tm A B → Prop
  | A, B, .prim r => ∀ f, rowsProved.lookup r.sym = some f → ∀ p ∈ f A B, L p.1 p.2
  | _, _, .lam (A := A) (B := B) R => L A B ∧ R.LamLawsAt L
  | _, _, .E (A := A) (B := B) R => L (.arr A) B ∧ R.LamLawsAt L
  | _, .arr B, .thin Q => L (.arr B) B ∧ Q.LamLawsAt L
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R | _, _, .succ R | _, _, .arith _ _ R
  | _, _, .leq _ R | _, _, .lt _ R | _, _, .share _ R | _, _, .est R | _, _, .call _ _ _ R
  | _, _, .callCv _ _ _ _ R _ => R.LamLawsAt L
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S => R.LamLawsAt L ∧ S.LamLawsAt L
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.LamLawsAt L ∧ S.LamLawsAt L ∧ U.LamLawsAt L ∧ V.LamLawsAt L
  | _, _, .arg f x => f.LamLawsAt L ∧ x.LamLawsAt L
  | _, _, .nu k S b => b.pol true k = true ∧ S.LamLawsAt L ∧ b.LamLawsAt L
  -- the children's term asks no more than the body (`Tm.lamLawsAt_kids`)
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k = true ∧ b.LamLawsAt L
  -- every other constructor spelled out: a catch-all's equation lemmas time `simp` out
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. => True

/-- `Tm.LamLawsAt` with nothing asked at a `Λ`, the premise of `Tm.gen_sound`: each fixed point's body positive.
    `Λ`'s order law is a theorem (`Vals.lamLaw`), so only `Tm.monoOK` is left of it (`Tm.monoOK_iff`). -/
abbrev Tm.LamLaws {A B : Obj} (t : Tm A B) : Prop := t.LamLawsAt fun _ _ => True

/-- The decidable part of `Tm.LamLawsAt`, every conjunct but `L` (`Tm.monoOK_iff`): what `GenSoundTest` evaluates
    beside `Tm.hasCode`, since `LamLawsAt L` implies it for every `L` (`Tm.LamLawsAt.mono`). -/
def Tm.monoOK : {A B : Obj} → Tm A B → Bool
  | _, _, .lam R | _, _, .E R | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ _ R | _, _, .leq _ R | _, _, .lt _ R | _, _, .share _ R
  | _, _, .est R | _, _, .thin R | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.monoOK
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .arg R S => R.monoOK && S.monoOK
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.monoOK && S.monoOK && U.monoOK && V.monoOK
  | _, _, .nu k S b => b.pol true k && S.monoOK && b.monoOK
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k && b.monoOK
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. | _, _, .prim _ => true

theorem Tm.monoOK_iff {A B : Obj} (t : Tm A B) : t.monoOK = true ↔ t.LamLawsAt fun _ _ => True := by
  induction t <;> simp [Tm.monoOK, Tm.LamLawsAt, and_assoc, *]

theorem Tm.LamLawsAt.mono {L L' : Obj → Obj → Prop} (h : ∀ A B, L A B → L' A B) {A B : Obj} (t : Tm A B) :
    t.LamLawsAt L → t.LamLawsAt L' := by
  induction t <;> simp only [Tm.LamLawsAt] <;> intro hx
  all_goals first
    | exact fun f e p hp => h _ _ (hx f e p hp)
    | exact ⟨h _ _ hx.1, by simp_all⟩
    | simp_all

/-- The children's term of `t` (`Tm.kids`) asks no more than `t`: `kids` builds it of `t`'s parts, `𝟙`, `𝟘`, `∪`,
    `juncD` and `∋`, none of which asks anything. -/
theorem Tm.lamLawsAt_kids {L : Obj → Obj → Prop} (k : Nat) (A : Obj) {C D : Obj} (t : Tm C D)
    (h : t.LamLawsAt L) : ((t.kids k A).getD .zero).LamLawsAt L := by
  induction t
  case arg f x _ _ =>
    cases f <;> unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;>
      simp_all (config := {decide := true}) [Tm.LamLawsAt, rowsProved, memRow]
  all_goals unfold Tm.kids <;> (try dsimp only) <;> (repeat' split) <;> (try subst_vars) <;>
    simp_all [Tm.LamLawsAt]

namespace GenK

theorem memo_sound {A B : Obj} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.memo A B R).Reps K X := fun K => by
  cases R with
  | tab t => exact hR K
  | lazy f =>
    simp only [GenK.memo]; split
    next t h =>
      refine (reps_iff _ _ _).2 fun t' h' x y _ _ _ => ?_
      cases h'; exact (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl trivial
    next => exact hR K
  | bits => exact (reps_iff _ _ _).2 fun t h x y _ _ _ => (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl trivial

theorem memo_wf {A B : Obj} {R : Rel A B} (h : R.Wf) : (GenK.memo A B R).Wf := by
  cases R with
  | lazy f => simp only [GenK.memo]; split <;> first | trivial | exact h
  | _ => trivial

end GenK

theorem Tm.code_of {η : Code} {A B : Obj} {t : Tm A B} {X : Core.Rel A.El B.El} (h : ∀ K, (t.gen η).Reps K X) :
    ∀ K, (t.code η).Reps K X := by
  rw [Tm.code]; split
  · exact GenK.memo_sound h
  · exact h

/-! ### The rows: `Prim.den` unfolded once, then one `Tab` law per row -/

/-- The codes `xs` represent the meanings `ss`, one for one at the same objects, in every context. -/
def CodesRep : Codes → List Sem → Prop
  | [], [] => True
  | ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss =>
    (if h : X' = X ∧ Y' = Y then ∀ K, x.Reps K (h.1 ▸ h.2 ▸ T) else False) ∧ CodesRep xs ss
  | _, _ => False

/-- `Wf` codes `xs` that represent `ss`, bound at `ks`, represent `ss` bound at `ks`: what a call's body is built
    and read under (`Sound.bind` per argument). -/
theorem Sound.args : ∀ (ks : List Nat) (xs : Codes) (ss : List Sem), (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
    Sound (Code.args ks xs) (Val.args ks ss)
  | k :: ks, ⟨X, Y, x⟩ :: xs, ⟨X', Y', T⟩ :: ss, hw, hr => by
    simp only [CodesRep] at hr
    split at hr
    · rename_i h; obtain ⟨rfl, rfl⟩ := h
      exact (Sound.args ks xs ss (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hr.2).bind k hr.1
        (hw _ List.mem_cons_self)
    · exact hr.1.elim
  | [], _, _, _, _ | _ :: _, [], [], _, _ => ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial⟩
  | _ :: _, [], _ :: _, _, hr | _ :: _, _ :: _, [], _, hr => by simp [CodesRep] at hr

/-- Row `s`'s cases of `Tm.gen_wf` and `Tm.gen_sound`: at every objects, given as many relation codes `xs` as it
    takes, each `Wf`, its code is `Wf`, and represents its meaning of any `ss` that `xs` represent, given
    `Tm.LamLaws`. -/
def RowOK (s : String) : Prop := ∀ (r : Prim) (A B : Obj) (xs : Codes), r.sym = s → xs.length = rowArity s →
  (∀ x ∈ xs, x.2.2.Wf) → (primGen r A B xs).Wf ∧ ∀ ss, CodesRep xs ss →
    (Tm.prim (A := A) (B := B) r).LamLaws → ∀ K, (primGen r A B xs).Reps K (Prim.den r A B ss)

/-- `Prim.den` and `primGen` unfolded through the `rowDens` and `rowGens` lookups: a row is `RowOK` when its
    generated code at each `σ` and `xs` is `Wf`, and at the row's objects `c.ty σ` represents its meaning `D σ ss`
    of the `ss` that `xs` represent. -/
theorem rowOK_args {s : String} {c : RowCode} {D : RowDen c}
    {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (xs : Codes) (A B : Obj) (v : Rel A B), r.sym = s → xs.length = rowArity s →
      (∀ x ∈ xs, x.2.2.Wf) → f σ xs = some ⟨A, B, v⟩ → v.Wf ∧ ∀ ss, CodesRep xs ss →
        (Tm.prim (A := A) (B := B) r).LamLaws →
          ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, v.Reps K (hc.1 ▸ hc.2 ▸ D σ ss)) : RowOK s := by
  intro r A B xs hs hn hw
  have err (e : String) (X : List Sem → Den A B) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss,
      CodesRep xs ss → (Tm.prim (A := A) (B := B) r).LamLaws → ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K (X ss) :=
    ⟨trivial, fun _ _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
  unfold primGen Prim.den; rw [hs, if_neg fun h => h hn, hf, hD]
  cases hσ : r.objs A B with
  | none => exact err _ _
  | some σ =>
    dsimp only; split
    · next A' B' v hv =>
      split
      · next he =>
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hw, hR⟩ := h r σ xs A' B' v hs hn hw hv
        refine ⟨hw, fun ss hss hl K => ?_⟩
        obtain ⟨hc, hR⟩ := hR ss hss hl
        rw [dif_pos hc]; exact hR K
      · exact err _ _
    · exact err _ _

/-- `rowOK_args` for a row given no relation (`rowArity s = 0`): only `xs = ss = []`. -/
theorem rowOK_of {s : String} {c : RowCode} {D : RowDen c} {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (hD : rowDens.find? (·.1.sym == s) = some ⟨c, D⟩) (hf : rowGens.lookup s = some f)
    (h : ∀ (r : Prim) σ (A B : Obj) (v : Rel A B), r.sym = s → f σ [] = some ⟨A, B, v⟩ → v.Wf ∧
      ((Tm.prim (A := A) (B := B) r).LamLaws →
        ∃ hc : (c.ty σ).1 = A ∧ (c.ty σ).2 = B, ∀ K, v.Reps K (hc.1 ▸ hc.2 ▸ D σ [])))
    (h0 : rowArity s = 0 := by decide) : RowOK s :=
  rowOK_args hD hf fun r σ xs A B v hs hn _ hv => by
    cases xs with
    | cons => simp [h0] at hn
    | nil =>
      obtain ⟨hw, hR⟩ := h r σ A B v hs hv
      refine ⟨hw, fun ss hss hl => ?_⟩
      cases ss with
      | nil => exact hR hl
      | cons => simp [CodesRep] at hss

theorem rowOK_mem : RowOK "∋" := rowOK_of (c := RowCode.mem) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h⟩⟩

theorem rowOK_inl : RowOK "inl" := rowOK_of (c := RowCode.inl) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inl_holds h⟩⟩

theorem rowOK_inr : RowOK "inr" := rowOK_of (c := RowCode.inr) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inr_holds h⟩⟩

theorem rowOK_inlC : RowOK "inl°" := rowOK_of (c := RowCode.inlC) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inlConv_holds h⟩⟩

theorem rowOK_inrC : RowOK "inr°" := rowOK_of (c := RowCode.inrC) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inrConv_holds h⟩⟩

theorem rowOK_tau : RowOK "τ" := rowOK_of (c := RowCode.tau) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tau_den h⟩

theorem rowOK_setify : RowOK "setify" := rowOK_of (c := RowCode.setify) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.setify_den h⟩

/-- An array is below itself extended by a non-empty one (`Obj.lt` on `[B]`: a proper prefix first). -/
theorem arr_lt_append (B : Obj) : ∀ (xs ys : List B.El), ys ≠ [] → (Obj.arr B).lt xs (xs ++ ys)
  | [], [], h => (h rfl).elim
  | [], y :: ys, _ => Obj.lt_nil_cons B y ys
  | x :: xs, ys, h => (Obj.lt_cons B x x xs (xs ++ ys)).2 (Or.inr ⟨rfl, arr_lt_append B xs ys h⟩)

/-- A shorter prefix of `xs` is below a longer one (`Obj.lt` on `[B]`). -/
theorem arr_lt_take (B : Obj) (xs : List B.El) {i j : Nat} (hij : i < j) (hj : j ≤ xs.length) :
    (Obj.arr B).lt (xs.take i) (xs.take j) := by
  have h := arr_lt_append B (xs.take i) ((xs.take j).drop i) fun h0 => by
    have := congrArg List.length h0; simp at this; omega
  have e : xs.take i ++ (xs.take j).drop i = xs.take j := by
    have t := List.take_append_drop i (xs.take j)
    rwa [List.take_take, Nat.min_eq_left (by omega)] at t
  rwa [e] at h

/-- **`Λ(T)` at `a` is `L`** when `L` ascends strictly in `Obj.lt` and its members are the image of `a` under `T`. -/
theorem lamDen_eq {A B : Obj} {T : Den A B} {a : A.El} {L : List B.El} (hL : L.Pairwise B.lt)
    (hm : ∀ b, b ∈ L ↔ T a b) (zs : List B.El) : lamDen T a zs ↔ zs = L :=
  ⟨fun ⟨hp, hz⟩ => pairwise_eq_of_mem (Obj.lt_irrefl _) (fun _ _ => Obj.lt_asymm _) hp hL
    fun b => (hz b).trans (hm b).symm, fun h => h ▸ ⟨hL, hm⟩⟩

/-- **`Λ(cat°)` at `xs`**: the one list strictly ascending in `Obj.lt` of the splits `(p₁, p₂)` of `xs` is the splits by
increasing split point, since a shorter first part is a proper prefix of a longer one. -/
theorem lamDen_splits {B : Obj} {T : Den (.arr B) (.prod (.arr B) (.arr B))} (xs : List B.El)
    (hT : ∀ p, T xs p ↔ xs = p.1 ++ p.2) (zs : List (Obj.prod (.arr B) (.arr B)).El) :
    lamDen T xs zs ↔ zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) :=
  lamDen_eq ((pairwise_map_range_iff _ _ _).2 fun _ _ hij hj =>
    (Obj.lt_prod _ _ _ _ _ _).2 (Or.inl (arr_lt_take B xs hij (by omega)))) (fun p => by
    rw [hT, List.mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩; exact (List.take_append_drop k xs).symm
    · intro h; subst h; exact ⟨p.1.length, by simp; omega, by simp⟩) zs

/-- **`Λ(prefix)` at `xs`**: the one list strictly ascending in `Obj.lt` of the prefixes of `xs` is its prefixes by
increasing length. -/
theorem lamDen_inits {B : Obj} {T : Den (.arr B) (.arr B)} (xs : List B.El) (hT : ∀ ys, T xs ys ↔ ys <+: xs)
    (zs : List (List B.El)) : lamDen T xs zs ↔ zs = (List.range (xs.length + 1)).map fun k => xs.take k :=
  lamDen_eq ((pairwise_map_range_iff _ _ _).2 fun _ _ hij hj => arr_lt_take B xs hij (by omega)) (fun ys => by
    rw [hT, List.mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩; exact List.take_prefix k xs
    · intro h
      exact ⟨ys.length, List.mem_range.2 (Nat.lt_succ_of_le h.length_le), (List.prefix_iff_eq_take.1 h).symm⟩) zs

/-- **`tails` on the cells `X`** (`Tab.tails`) = `Λ(cat°) ≫ F(π₂)`: each array of `X` to its suffixes by decreasing
length. -/
theorem Tab.tails_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.tails X = .ok T) (xs : List B.El)
    (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  unfold Tab.tails at h
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨L, hL, h⟩ := GenK.bind_ok h
  rcases L with ⟨N, key, m, lo, hi, f⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- the cells of `⟨m, lo, hi, f.2⟩` are those of `⟨m, lo, hi, f⟩` mapped by `Prod.snd`
  have hrow : ∀ i, Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, f.2⟩ i =
      (Vals.row (A := .arr (.prod (.arr B) (.arr B))) ⟨m, lo, hi, f⟩ i).map Prod.snd := fun i => by
    rw [Vals.row_arr, Vals.row_arr, List.map_map]
    congr 1; funext k; simp only [Function.comp_apply, apply_dite Prod.snd]; rfl
  have hs : ∀ (hx : ∃ i, X.row i = xs) zs, lamDen U.Holds xs zs ↔
      zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) :=
    fun hx => lamDen_splits xs fun p => (Tab.uncat_holds hU xs p).trans (and_iff_right hx)
  constructor
  · rintro ⟨i, hk, hv⟩
    obtain ⟨hx, hd⟩ := (Tab.lam_den hL xs _).1 ⟨i, hk, rfl⟩
    refine ⟨hx, ?_⟩
    rw [← hv, hrow, (hs hx _).1 hd, List.map_map]; rfl
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hk, hv⟩ := (Tab.lam_den hL xs _).2 ⟨hx, (hs hx _).2 rfl⟩
    exact ⟨i, hk, by rw [hrow]; simp only at hv; rw [hv, List.map_map]; rfl⟩

theorem rowOK_tails : RowOK "tails" := rowOK_of (c := RowCode.tails) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tails_den h⟩

/-- A row run after the keys (`GenK.after`) represents `P` when `f D`, on the keys' coreflexive `D`, holds `D ≫ P`. -/
theorem GenK.after_row_sound {A B : Obj} {f : {K : Obj} → Tab K A → Except String (Tab K B)}
    {P : Core.Rel A.El B.El}
    (hf : ∀ {K : Obj} (D : Tab K A) t, f D = .ok t → ∀ k b, t.Holds k b ↔ ∃ a, D.Holds k a ∧ P a b) :
    ∀ K, (GenK.after A B f).Reps K P :=
  GenK.ofVals_row_sound fun _ X t h a b => by
    cases hD : Tab.idU X with
    | error e => rw [hD] at h; exact nomatch h
    | ok D =>
    rw [hD] at h
    rw [hf D t h]
    constructor
    · rintro ⟨a', ha', hp⟩; obtain ⟨rfl, hx⟩ := (Tab.idU_holds hD a a').1 ha'; exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩; exact ⟨a, (Tab.idU_holds hD a a).2 ⟨rfl, hx⟩, hp⟩

theorem rowOK_snoc : RowOK "snoc" := rowOK_of (c := RowCode.snoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.snoc_holds h⟩⟩

theorem rowOK_cons : RowOK "cons" := rowOK_of (c := RowCode.cons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.cons_holds h⟩⟩

theorem rowOK_cat : RowOK "cat" := rowOK_of (c := RowCode.cat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.cat_holds h⟩⟩

theorem rowOK_uncat : RowOK "uncat" := rowOK_of (c := RowCode.uncat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.uncat_holds h⟩⟩

/-- **`cat° ≫ graph f`** on the cells `X` (`Tab.prefix`, `Tab.suffix`): `uncat`'s splits composed with a table `g` of
them that holds `graph f`. -/
theorem Tab.uncat_comp_holds {B : Obj} {n : USize} {X : Vals (.arr B) n}
    {g : {m : USize} → Vals (.prod (.arr B) (.arr B)) m → Except String (Tab (.prod (.arr B) (.arr B)) (.arr B))}
    {f : (Obj.prod (.arr B) (.arr B)).El → List B.El}
    (hg : ∀ m (P : Vals (.prod (.arr B) (.arr B)) m) t, g P = .ok t → ∀ p ys,
      t.Holds p ys ↔ (∃ i, P.row i = p) ∧ Core.Rel.graph f p ys)
    {T : Tab (.arr B) (.arr B)} (h : (do let u ← Tab.uncat X; u.comp (← g u.val)) = .ok T) (xs ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ∃ p : (Obj.prod (.arr B) (.arr B)).El, xs = p.1 ++ p.2 ∧ ys = f p := by
  obtain ⟨U, hU, h⟩ := GenK.bind_ok h
  obtain ⟨G, hG, h⟩ := GenK.bind_ok h
  rw [Tab.comp_holds h]
  constructor
  · rintro ⟨p, hp, hq⟩
    exact ⟨((Tab.uncat_holds hU xs p).1 hp).1, p, ((Tab.uncat_holds hU xs p).1 hp).2, ((hg _ _ _ hG p ys).1 hq).2⟩
  · rintro ⟨hx, p, he, rfl⟩
    have hp := (Tab.uncat_holds hU xs p).2 ⟨hx, he⟩
    obtain ⟨i, -, hv⟩ := hp
    exact ⟨p, (Tab.uncat_holds hU xs p).2 ⟨hx, he⟩, (hg _ _ _ hG p _).2 ⟨⟨i, hv⟩, rfl⟩⟩

/-- **`prefix`** (`Tab.prefix`) = `cat° ≫ π₁`: each array of `X` to its initial segments. -/
theorem Tab.prefix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.prefix X = .ok T) (xs ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <+: xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outl P) (f := Prod.fst) (fun _ _ _ h => Tab.outl_holds h) h]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.2, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(ys, t), ht.symm, rfl⟩⟩

/-- **`suffix`** (`Tab.suffix`) = `cat° ≫ π₂`: each array of `X` to its final segments. -/
theorem Tab.suffix_holds {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)}
    (h : Tab.suffix X = .ok T) (xs ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys <:+ xs := by
  rw [Tab.uncat_comp_holds (g := fun P => Tab.outr P) (f := Prod.snd) (fun _ _ _ h => Tab.outr_holds h) h]
  exact and_congr_right fun _ => ⟨fun ⟨p, he, hy⟩ => ⟨p.1, by rw [hy, he]⟩, fun ⟨t, ht⟩ => ⟨(t, ys), ht.symm, rfl⟩⟩

theorem rowOK_prefix : RowOK "prefix" := rowOK_of (c := RowCode.prefix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.prefix_holds h⟩⟩

theorem rowOK_suffix : RowOK "suffix" := rowOK_of (c := RowCode.suffix) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.suffix_holds h⟩⟩

theorem rowOK_uncons : RowOK "uncons" := rowOK_of (c := RowCode.uncons) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.uncons_holds h⟩⟩

theorem rowOK_unsnoc : RowOK "unsnoc" := rowOK_of (c := RowCode.unsnoc) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.unsnoc_holds h⟩⟩

/-- **`inits` on the cells `X`** (`Tab.inits`) = `Λ(prefix)`: each array of `X` to its prefixes by increasing length. -/
theorem Tab.inits_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.inits X = .ok T) (xs : List B.El) (yss : List (List B.El)) :
    T.Holds xs yss ↔ (∃ i, X.row i = xs) ∧ yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  unfold Tab.inits at h
  obtain ⟨P, hP, h⟩ := GenK.bind_ok h
  rw [Tab.lam_den h]
  exact and_congr_right fun hx => lamDen_inits xs (fun ys => (Tab.prefix_holds hP xs ys).trans (and_iff_right hx)) yss

theorem rowOK_inits : RowOK "inits" := rowOK_of (c := RowCode.inits) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.inits_den h⟩

theorem rowOK_zip : RowOK "zip" := rowOK_of (c := RowCode.zip) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | _⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.after_row_sound fun _ _ h => Tab.zip_holds h⟩⟩

theorem rowOK_concat : RowOK "concat" := rowOK_of (c := RowCode.concat) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.flatten_holds h⟩⟩

theorem rowOK_length : RowOK "length" := rowOK_of (c := RowCode.length) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.length_holds h⟩⟩

/-- `$` at the objects `σ` names: the graph `castDen`, no ordering hypothesis. -/
theorem rowOK_cast : RowOK "$" := rowOK_of (c := RowCode.cast) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
    exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.cast_den h⟩⟩

/-- A `unaryOps` row at the object `σ` names: the graph `unaryDen` of its `Op`, one case per row. -/
theorem rowOK_unary {s : String} (hs : s ∈ unaryOps.map (·.1)) : RowOK s := by
  simp only [unaryOps, List.map, List.mem_cons, List.not_mem_nil, or_false] at hs
  repeat' (rcases hs with rfl | hs)
  all_goals first | (subst hs) | skip
  all_goals
    exact rowOK_of (c := ⟨_, fun σ => (σ₁ σ, σ₂ σ)⟩) rfl rfl fun _ σ _ _ _ _ hv => by
      cases hv
      rcases σ with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
        exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.unary_den rfl h⟩⟩

theorem rowOK_sum : RowOK "sum" := rowOK_of (c := RowCode.sum) rfl rfl fun _ σ _ _ _ _ hv => by
  cases hv
  cases σ <;> exact ⟨GenK.ofVals_wf, fun _ => ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.sum_holds h⟩⟩

theorem rowOK_loop : RowOK "loop" := rowOK_args (c := RowCode.loop) rfl rfl fun _ σ xs _ _ _ _ hn hw hv => by
  have h1 : rowArity "loop" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.stepAfter GenK.after; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.loop_sound hss (hw _ (List.mem_singleton_self _))
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_filter : RowOK "filter" := rowOK_args (c := RowCode.filter) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "filter" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.filter_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_takewhile : RowOK "takewhile" :=
  rowOK_args (c := RowCode.takewhile) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "takewhile" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.takewhile_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_positions : RowOK "positions" :=
  rowOK_args (c := RowCode.positions) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "positions" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.positions_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_asc : RowOK "asc" :=
  rowOK_args (c := RowCode.asc) rfl rfl fun _ σ xs _ _ _ hs hn _ hv => by
  have h1 : rowArity "asc" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.ofRel; exact GenK.lift1_wf _, fun ss hss hl => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss fun _ _ h hr => by subst hr; exact Tab.asc_holds h
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_sums : RowOK "sums" :=
  rowOK_args (c := RowCode.sums) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "sums" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, σ⟩⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.ofRel; exact GenK.lift1_wf _, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss fun _ _ h hr => by subst hr; exact Tab.sums_den h
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

theorem rowOK_F : RowOK "F" := rowOK_args (c := RowCode.map) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "F" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, σ⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.elems; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.map_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `merge(Q)`, `Expand.primE`'s fit of the row (`testAfter`, `Tab.merge`): each `(x, y)` in demand to
`List.merge x y` under `Q`'s meaning `TQ` as the test, `Q` run on the pairs of heads it is asked about (`est`'s rule). -/
theorem GenK.merge_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ) :
    ∀ K, (GenK.testAfter B (.prod (.arr B) (.arr B)) (.arr B) Q fun q P => Tab.merge q P).Reps K
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.after_row_sound fun _ _ h k zs => Tab.merge_holds (fun D _ hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl trivial)
    h k zs

theorem rowOK_merge : RowOK "merge" := rowOK_args (c := RowCode.merge) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "merge" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.testAfter GenK.after; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.merge_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

open Classical in
/-- `thinL(Q)`, `Expand.primE`'s fit of the row (`testVals`, `Tab.thinL`): each array in demand to `thinLDen` under
`Q`'s meaning `TQ` as the test, `Q` run on the pairs it is asked about (`est`'s rule). -/
theorem GenK.thinL_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ) :
    ∀ K, (GenK.testVals B (.arr B) (.arr B) Q fun q X => Tab.thinL q X).Reps K
      (thinLDen fun a b => decide (TQ (a, b) (a, b))) :=
  GenK.ofVals_row_sound fun _ _ _ h xs w => Tab.thinL_holds (fun D _ hT p hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl trivial)
    h xs w

theorem rowOK_thinL : RowOK "thinL" := rowOK_args (c := RowCode.thinL) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "thinL" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, σ⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.testVals; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.thinL_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

/-- `Rᴵ`, `Expand.primE`'s fit of the row (`onKeys`, `Tab.flat`): the `(a', b)` of `R` at the key of each pair in
demand, kept where `a'` is its source, `R` run on the keys in demand. -/
theorem GenK.flat_sound {I A B : Obj} {d : Bool} {R : Rel I (.prod A B)} {X : Core.Rel I.El (Obj.prod A B).El}
    (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.onKeys I A B (.prod A B) d R fun X r => Tab.flat X r).Reps K (flatDen X) :=
  GenK.ofVals_sound fun _ _ Xs _ hK h p b hp _ _ => by
    obtain ⟨r, hr, ht⟩ := GenK.bind_ok h
    have er := (GenK.reps_iff _ _ _).1 (hR _) r hr
    obtain ⟨i, rfl⟩ := (GenK.side_some hK p).1 hp
    exact (Tab.flat_holds ht _ b).trans ((and_iff_right ⟨i, rfl⟩).trans
      (er _ _ ((GenK.side_some rfl _).2 ⟨i, rfl⟩) rfl trivial))

theorem rowOK_flat : RowOK "flat" := rowOK_args (c := RowCode.flat) rfl rfl fun _ σ xs _ _ _ _ hn _ hv => by
  have h1 : rowArity "flat" = 1 := by decide
  rcases xs with _ | ⟨⟨X, Y, x⟩, _ | ⟨_, _⟩⟩ <;> simp only [List.length_cons, List.length_nil, h1] at hn <;>
    try omega
  rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, σ⟩⟩⟩ <;>
    simp only [Codes.at, List.getElem?_cons_zero, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hv
  all_goals
    split at hv
    case isFalse => simp at hv
    rename_i he; revert hv; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hv
    cases hv
    refine ⟨by unfold GenK.onKeys; exact GenK.ofVals_wf, fun ss hss _ => ⟨⟨rfl, rfl⟩, ?_⟩⟩
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.flat_sound hss
    · rename_i h; exact absurd ⟨rfl, rfl⟩ h

/-- Every row of `rowsProved` is `RowOK`: the obligations enumerated from the list `rowGens_proved` checks. -/
theorem rowsProved_ok (r : Prim) (h : (rowsProved.lookup r.sym).isSome) : RowOK r.sym := by
  by_cases h1 : r.sym = "∋"; · rw [h1]; exact rowOK_mem
  by_cases h2 : r.sym = "inl"; · rw [h2]; exact rowOK_inl
  by_cases h3 : r.sym = "inr"; · rw [h3]; exact rowOK_inr
  by_cases h4 : r.sym = "τ"; · rw [h4]; exact rowOK_tau
  by_cases h5 : r.sym = "setify"; · rw [h5]; exact rowOK_setify
  by_cases h6 : r.sym = "snoc"; · rw [h6]; exact rowOK_snoc
  by_cases h7 : r.sym = "cons"; · rw [h7]; exact rowOK_cons
  by_cases h8 : r.sym = "cat"; · rw [h8]; exact rowOK_cat
  by_cases h9 : r.sym = "uncat"; · rw [h9]; exact rowOK_uncat
  by_cases h10 : r.sym = "zip"; · rw [h10]; exact rowOK_zip
  by_cases h11 : r.sym = "length"; · rw [h11]; exact rowOK_length
  by_cases h12 : r.sym = "loop"; · rw [h12]; exact rowOK_loop
  by_cases h13 : r.sym = "filter"; · rw [h13]; exact rowOK_filter
  by_cases h14 : r.sym = "concat"; · rw [h14]; exact rowOK_concat
  by_cases h15 : r.sym = "merge"; · rw [h15]; exact rowOK_merge
  by_cases h16 : r.sym = "thinL"; · rw [h16]; exact rowOK_thinL
  by_cases h17 : r.sym = "tails"; · rw [h17]; exact rowOK_tails
  by_cases h18 : r.sym = "sum"; · rw [h18]; exact rowOK_sum
  by_cases h19 : r.sym = "F"; · rw [h19]; exact rowOK_F
  by_cases h20 : r.sym = "positions"; · rw [h20]; exact rowOK_positions
  by_cases h21 : r.sym = "asc"; · rw [h21]; exact rowOK_asc
  by_cases h22 : r.sym = "inl°"; · rw [h22]; exact rowOK_inlC
  by_cases h23 : r.sym = "inr°"; · rw [h23]; exact rowOK_inrC
  by_cases h24 : r.sym = "prefix"; · rw [h24]; exact rowOK_prefix
  by_cases h25 : r.sym = "suffix"; · rw [h25]; exact rowOK_suffix
  by_cases h26 : r.sym = "uncons"; · rw [h26]; exact rowOK_uncons
  by_cases h27 : r.sym = "unsnoc"; · rw [h27]; exact rowOK_unsnoc
  by_cases h28 : r.sym = "inits"; · rw [h28]; exact rowOK_inits
  by_cases h29 : r.sym = "takewhile"; · rw [h29]; exact rowOK_takewhile
  by_cases h30 : r.sym = "sums"; · rw [h30]; exact rowOK_sums
  by_cases h31 : r.sym = "flat"; · rw [h31]; exact rowOK_flat
  by_cases h32 : r.sym = "$"; · rw [h32]; exact rowOK_cast
  by_cases hu : r.sym ∈ unaryOps.map (·.1); · exact rowOK_unary hu
  have hu' : ∀ p ∈ unaryOps, (r.sym == p.1) = false := fun p hp =>
    beq_false_of_ne fun he => hu (he ▸ List.mem_map_of_mem hp)
  simp only [unaryOps, List.forall_mem_cons] at hu'
  simp [rowsProved, List.lookup, unaryOps, hu', beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4,
    beq_false_of_ne h5, beq_false_of_ne h6, beq_false_of_ne h7, beq_false_of_ne h8, beq_false_of_ne h9,
    beq_false_of_ne h10, beq_false_of_ne h11, beq_false_of_ne h12, beq_false_of_ne h13, beq_false_of_ne h14,
    beq_false_of_ne h15, beq_false_of_ne h16, beq_false_of_ne h17, beq_false_of_ne h18,
    beq_false_of_ne h19, beq_false_of_ne h20, beq_false_of_ne h21, beq_false_of_ne h22, beq_false_of_ne h23,
    beq_false_of_ne h24, beq_false_of_ne h25, beq_false_of_ne h26, beq_false_of_ne h27, beq_false_of_ne h28,
    beq_false_of_ne h29, beq_false_of_ne h30, beq_false_of_ne h31, beq_false_of_ne h32] at h

/-- Every row `rowGens` has a code for is in `rowsProved`. -/
theorem rowGens_proved {s : String} {f : List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B)}
    (h : rowGens.lookup s = some f) : (rowsProved.lookup s).isSome := by
  suffices ∀ l : List (String × (List Obj → Codes → Option ((A : Obj) × (B : Obj) × Rel A B))),
      (∀ p ∈ l, (rowsProved.lookup p.1).isSome) → l.lookup s = some f → (rowsProved.lookup s).isSome from
    this _ (by decide) h
  intro l; induction l with
  | nil => intro _ h; nomatch h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    intro hl h
    simp only [List.lookup] at h
    split at h
    · next he => rw [beq_iff_eq.1 he]; exact hl _ List.mem_cons_self
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h

/-- Every row's code given `Wf` codes is `Wf` and represents its meaning: `RowOK` where it is given as many
    relations as it takes and `rowGens` has it (`rowGens_proved`), an error table elsewhere. -/
theorem primGen_ok (r : Prim) (A B : Obj) (xs : Codes) (hw : ∀ x ∈ xs, x.2.2.Wf) : (primGen r A B xs).Wf ∧
    ∀ ss, CodesRep xs ss → (Tm.prim (A := A) (B := B) r).LamLaws → ∀ K, (primGen r A B xs).Reps K (Prim.den r A B ss) := by
  have err (e : String) : (Rel.tab (A := A) (B := B) (.error e)).Wf ∧ ∀ ss, CodesRep xs ss →
      (Tm.prim (A := A) (B := B) r).LamLaws → ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K (Prim.den r A B ss) :=
    ⟨trivial, fun _ _ _ _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h⟩
  by_cases hn : xs.length = rowArity r.sym
  · cases hg : rowGens.lookup r.sym with
    | some f => exact rowsProved_ok r (rowGens_proved hg) r A B xs rfl hn hw
    | none => unfold primGen; rw [if_neg fun h => h hn, hg]; exact err _
  · unfold primGen; rw [if_pos hn]; exact err _

theorem Tm.code_wf {η : Code} {A B : Obj} {t : Tm A B} (h : (t.gen η).Wf) : (t.code η).Wf := by
  rw [Tm.code]; split
  · exact GenK.memo_wf h
  · exact h

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`**: only `comp` builds one (`GenK.comp_wf`), a variable reads
    `η`'s, and every other op returns tables. -/
theorem Tm.gen_wf_spine {A B : Obj} (t : Tm A B) :
    (∀ η : Code, (∀ k A B, (η k A B).Wf) → (t.gen η).Wf) ∧
    ∀ (η : Code) (xs : Codes), (∀ k A B, (η k A B).Wf) → (∀ x ∈ xs, x.2.2.Wf) → (t.argGen η xs).Wf := by
  induction t
  case prim r =>
    refine ⟨fun η _ => ?_, fun η xs _ hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).1
    · exact (primGen_ok r _ _ xs hx).1
  case arg f x ihf ihx =>
    refine ⟨fun η hη => ?_, fun η xs hη hx => ?_⟩ <;>
      simp only [Tm.gen, Tm.argGen] <;> refine ihf.2 η _ hη fun y hy => ?_ <;>
      rcases List.mem_cons.1 hy with rfl | hy
    any_goals exact code_wf (ihx.1 η hη)
    all_goals first | exact hx y hy | simp at hy
  case share _ R ih =>
    refine ⟨fun η _ => ?_, fun η xs _ hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact code_wf (ih.1 Code.empty fun _ _ _ => trivial)
    · exact ih.2 Code.empty xs (fun _ _ _ => trivial) hx
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η _ => ?_, fun η xs _ hx => ?_⟩ <;> simp only [Tm.gen, Tm.argGen]
    · exact code_wf (ih.1 _ (Code.args_wf ks [] fun _ h => nomatch h))
    · exact code_wf (ih.1 _ (Code.args_wf ks xs hx))
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η hη => ?_, fun η xs _ _ => by unfold Tm.argGen; exact trivial⟩
  all_goals simp only [Tm.gen]
  case comp R S ihR ihS => exact GenK.comp_wf _ (code_wf (ihS.1 η hη))
  case ldiv R S U V ihR ihS ihU ihV => exact GenK.ldiv_wf _ _ _ (code_wf (ihS.1 η hη))
  case own R ih => exact code_wf (ih.1 η hη)
  case var k => exact hη k _ _
  case hylo => split <;> first | trivial | exact fun _ => trivial | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])
  all_goals first
    | trivial
    | exact GenK.ofVals_wf
    | exact GenK.top_wf
    | exact GenK.id_wf
    | exact GenK.meet_wf _ _
    | exact GenK.diff_wf _ _
    | exact GenK.pair_wf _ _
    | exact GenK.lift1_wf _
    | exact GenK.lift2_wf _ _
    | exact fun _ => trivial
    | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** (`Tm.gen_wf_spine`, its first half). -/
theorem Tm.gen_wf {A B : Obj} (t : Tm A B) :
    ∀ η : Code, (∀ k A B, (η k A B).Wf) → (t.gen η).Wf := (Tm.gen_wf_spine t).1

/-- `Tm.gen_sound` with its spine half: a spine given codes `xs` that are `Wf` and represent `ss` generates code
    that represents its meaning of `ss` (`Tm.argGen`, `Tm.argDen`). -/
theorem Tm.gen_sound_spine {A B : Obj} (t : Tm A B) :
    (∀ (η : Code) (ρ : Val), t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
    ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem),
      t.LamLaws → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
        ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) := by
  -- strong induction on `Tm.size`: a `hylo`'s children's term (`Tm.kids`) is no subterm, only no larger than its body
  suffices H : ∀ n {A B : Obj} (t : Tm A B), t.size ≤ n →
      (∀ (η : Code) (ρ : Val), t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
      ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem),
        t.LamLaws → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
          ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) from H _ t (Nat.le_refl _)
  -- a fixed point's round binds its variable to its table (`Sound.bind`)
  have hconst {A B : Obj} (Y : Tab A B) : ∀ K, (GenK.const A B (.ok Y)).Reps K (rep Y) :=
    fun _ => (GenK.reps_iff _ _ _).2 fun t ht x y _ _ _ => by cases ht; exact Iff.rfl
  -- an error table runs to no table, so it represents every meaning
  have herr {A B : Obj} (e : String) (X : Den A B) : ∀ K, (Rel.tab (A := A) (B := B) (.error e)).Reps K X :=
    fun _ => (GenK.reps_iff _ _ _).2 fun t h => by simp [Rel.Rel.runE] at h
  intro n
  induction n
  case zero => intro A B t h; cases t <;> simp [Tm.size] at h
  rename_i n H
  intro A B t
  induction t <;> intro hn <;> simp only [Tm.size] at hn
  case prim r =>
    refine ⟨fun η ρ hl _ => ?_, fun η ρ xs ss hl _ hx hr => ?_⟩ <;>
      simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact (primGen_ok r _ _ [] fun _ h => nomatch h).2 [] trivial hl
    · exact (primGen_ok r _ _ xs hx).2 ss hr hl
  case arg C D f x ihf ihx =>
    have step (η ρ) (xs : Codes) (ss : List Sem)
        (hl : f.LamLaws ∧ x.LamLaws) (hs : Sound η ρ) (hx : ∀ y ∈ xs, y.2.2.Wf) (hr : CodesRep xs ss) :
        ∀ K, (f.argGen η (⟨C, D, x.code η⟩ :: xs)).Reps K (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) :=
      (ihf (by omega)).2 η ρ _ _ hl.1 hs (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact code_wf (gen_wf x η hs.2)
          · exact hx y hy)
        ⟨by rw [dif_pos ⟨rfl, rfl⟩]; exact code_of ((ihx (by omega)).1 η ρ hl.2 hs), hr⟩
    refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss hl hs hx hr => ?_⟩ <;>
      simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact step η ρ [] [] hl hs (fun _ h => nomatch h) trivial
    · exact step η ρ xs ss hl hs hx hr
  case share _ R ih =>
    have he : Sound Code.empty Val.empty := ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial⟩
    refine ⟨fun η ρ hl _ => ?_, fun η ρ xs ss hl _ hx hr => ?_⟩ <;>
      simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact code_of ((ih (by omega)).1 Code.empty Val.empty hl he)
    · exact (ih (by omega)).2 Code.empty Val.empty xs ss hl he hx hr
  -- the body under its arguments bound at `ks` (`Sound.args`), whatever the caller's `η`, `ρ`
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η ρ hl _ => ?_, fun η ρ xs ss hl _ hx hr => ?_⟩ <;>
      simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact code_of ((ih (by omega)).1 _ _ hl (Sound.args ks [] [] (fun _ h => nomatch h) trivial))
    · exact code_of ((ih (by omega)).1 _ _ hl (Sound.args ks xs ss hx hr))
  -- a spine headed by neither a row nor a call is an error table
  all_goals refine ⟨fun η ρ hl hs => ?_, fun η ρ xs ss _ _ _ _ => by unfold Tm.argGen; exact herr _ _⟩
  all_goals simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den]
  case val R => exact GenK.val_sound (R, true)
  case uni U => exact GenK.uni_sound (U, true)
  case zero => exact GenK.zero_sound
  case id => exact GenK.id_sound
  case top V ih => exact GenK.top_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case outl => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
  case outr => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outr_holds h
  case comp R S ihR ihS =>
    exact GenK.comp_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case conv R ih => exact GenK.conv_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case meet R S ihR ihS =>
    exact GenK.meet_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf R η hs.2)) (code_wf (gen_wf S η hs.2))
  case join R S ihR ihS => exact GenK.join_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case diff R S ihR ihS => exact GenK.diff_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case dom R ih => exact GenK.dom_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case ran R ih => exact GenK.ran_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case rdiv R S U V ihR ihS ihU ihV =>
    exact GenK.rdiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
  case ldiv R S U V ihR ihS ihU ihV =>
    exact GenK.ldiv_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hl.2.2.2 hs))
      (code_wf (gen_wf S η hs.2))
  case pair R S ihR ihS => exact GenK.pair_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case prod R S ihR ihS => exact GenK.prod_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
  case fold R S ihR ihS =>
    exact GenK.fold_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case foldr R S ihR ihS =>
    exact GenK.foldr_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hl.2 hs))
      (code_wf (gen_wf S η hs.2))
  case foldI R S ihR ihS =>
    exact GenK.foldI_sound (code_of ((ihR (by omega)).1 η ρ hl.1 hs)) (code_wf (gen_wf R η hs.2))
      (code_of ((ihS (by omega)).1 η ρ hl.2 hs)) (code_wf (gen_wf S η hs.2))
  case lam R ih => exact GenK.lam_sound (code_of ((ih (by omega)).1 η ρ hl.2 hs))
  case E R ih =>
    exact GenK.lam_sound (GenK.comp_sound (GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h)
      (code_of ((ih (by omega)).1 η ρ hl.2 hs)) (code_wf (gen_wf R η hs.2)))
  case nil => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.nil_holds h
  case own R ih => exact code_of ((ih (by omega)).1 η ρ hl hs)
  case succ U ih => exact GenK.succ_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case arith U ih => exact GenK.arith_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case leq U ih => exact GenK.cmp_sound (s := false) (code_of ((ih (by omega)).1 η ρ hl hs))
  case lt U ih => exact GenK.cmp_sound (s := true) (code_of ((ih (by omega)).1 η ρ hl hs))
  case var k => exact hs.1 k _ _
  case est Q ih => exact GenK.est_sound (code_of ((ih (by omega)).1 η ρ hl hs))
  case thin Q ih => exact GenK.thin_sound (code_of ((ih (by omega)).1 η ρ hl.2 hs))
  case atPos k => exact GenK.atPos_sound k
  case nu k S b ihS ihb =>
    exact GenK.nu_sound (code_of ((ihS (by omega)).1 η ρ hl.2.1 hs))
      (fun X => code_of ((ihb (by omega)).1 _ _ hl.2.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  case mu k w m b ih =>
    exact GenK.mu_sound (fun X => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  -- children `Tm.kids` reads in no shape: `Tm.gen`'s error table
  case hylo A' B' k w b ih =>
    have hc := Tm.lamLawsAt_kids k A' b hl.2
    have hsz := Tm.size_kids k A' b
    revert hc hsz
    cases hk : b.kids k A' with
    | none => intro _ _; simp only [Option.isNone_none, ↓reduceIte]; exact herr _ _
    | some c =>
      intro hc hsz
      simp only [Option.isNone_some, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hc hsz ⊢
      exact GenK.hylo_sound ((H c (by omega)).1 η ρ hc hs |> code_of) (code_wf (gen_wf c η hs.2))
        (fun Y => code_of ((ih (by omega)).1 _ _ hl.2 (hs.bind k (hconst Y) (by trivial))))
        (fun Y => code_wf (gen_wf b _ (hs.bind k (hconst Y) (by trivial)).2))
        (fun _ _ h => Tm.den_mono hl.1 h) (fun X Y a h => Tm.den_local k ρ X Y b c hk a h)

/-- **`Tm.gen` is sound**: the code of every term represents its meaning in every context, given `LamLaw` at each
    `Λ`, and an environment `η` that represents `ρ`; where the code is an error table (`Tm.hasCode` false) the run
    fails, which represents every meaning. -/
theorem Tm.gen_sound {A B : Obj} (t : Tm A B) :
    ∀ (η : Code) (ρ : Val), t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ) :=
  (Tm.gen_sound_spine t).1

end Rel.Lang
