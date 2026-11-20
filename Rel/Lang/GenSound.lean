import Rel.Lang.GenKFold
import Rel.RepWhere
import Rel.RepAsc
import Rel.Lang.GenKEst
import Rel.Lang.GenKFix
import Rel.Lang.GenKHylo
import Rel.Lang.Den
import Rel.Run.Lang.Expand

/-! `Tm.gen`: `Expand.node` as a Lean function from a term to its `GenK` code, one `GenK` op per constructor with
    `Expand.node`'s argument order, and `Tm.code` as `Expand.code` (a closed part memoised, `GenK.memo`). Then
    `Tm.gen_sound`: on a term with no `Tm.gap` constructor, under `Sound`, the code represents `Tm.den` in every
    context, each case one `GenK.*_sound` (`GenKSpec`, `GenKBits`). A bit matrix the code passes on is `Rel.Wf`
    (`Tm.gen_wf`) (`Tab.ofBits` reads back what `compSelM`, `compTabMat`, `ldivTabMat` build); the order law of each
    `Λ` (`LamLaw`, false at a float atom) is a hypothesis. -/

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

/-- The hypothesis of `Tab.lam_den` at `A ⟶ [B]`: two rows of one key whose codes ascend strictly hold values
    ascending in `B.lt`. It fails at a float atom, so it is asked per `Λ`, never for every object. -/
def LamLaw (A B : Obj) : Prop := ∀ (m : USize) (x : Vals (.prod A B) m) es, Vals.cols x = .ok es →
  ∀ i i' : Fin m.toNat, (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true →
    seenKey m es i ≠ seenKey m es i' → B.lt (x.row i).2 (x.row i').2

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
  let pl (k : Nat) := oE ((varObj k).getD .long)
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
        let σ := (List.range vs.length).map fun k => if lg.getD k false then .long else (varObj k).getD .long
        let inst (o : OExp) := o.at vs σ
        -- a parameter taken as its pair test (`some true`, §a) is a code at `X×Y ⟶ X×Y`, as `rowDens` reads it
        let ps := r.sig.1.map fun ((x, y), fm) =>
          if fm == some true then (.prod (inst x) (inst y), .prod (inst x) (inst y)) else (inst x, inst y)
        let ts := ps.toArray.map fun (X, Y) => g ``Gen.Fn #[bE true, oE X, oE Y]
        withLocalDeclsDND (ts.map (`x, ·)) fun xs => do
          let some v ← primE r (inst r.sig.2.1) (inst r.sig.2.2) (xs.zip ts) | return none
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

/-- Row `r`'s code at `A ⟶ B` given its relations' codes `xs`: its `rowGens` entry at `r.objs A B`, as `primE`
    fits it; an error table where it has none there. -/
def primGen (r : Prim) (A B : Obj) (xs : Codes) : Rel A B :=
  match rowGens.lookup r.sym, r.objs A B with
  | some f, some σ => match f σ xs with
    | some ⟨A', B', v⟩ => if h : A' = A ∧ B' = B then h.1 ▸ h.2 ▸ v else
      .tab (.error s!"Tm.gen: the row `{r.sym}` is not at its objects")
    | none => .tab (.error s!"Tm.gen: the row `{r.sym}` is given relations not at its objects")
  | _, _ => .tab (.error s!"Tm.gen: the row `{r.sym}` has no kernel body at these objects")

#guard rowGens.length = kernRows.length

mutual
/-- `Expand.code` without the constant sharing: a closed `t` memoised (`GenK.memo`), any other its node. -/
def Tm.code (η : Code) {A B : Obj} (t : Tm A B) : Rel A B :=
  if Expand.closed t then GenK.memo A B (t.gen η) else t.gen η
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
  | _, _, .arith k U => GenK.arith k (U.code η)
  | _, _, .leq U => GenK.leq (U.code η)
  | _, _, .lt U => GenK.lt (U.code η)
  | .arr Y, V, .foldr e S => GenK.foldr Y V S.dem (e.code η) (S.code η)
  | .arr Y, V, .fold e S => GenK.fold Y V S.dem (e.code η) (S.code η)
  | _, _, .share _ R => R.code Code.empty
  | .prod I (.arr Y), V, .foldI e S => GenK.foldI I Y V e.dem S.dem (e.code η) (S.code η)
  | .prod I A, B, .flat R => GenK.flat I A B R.dem (R.code η)
  | A, B, .var _ k => η k A B
  | A, B, .nu k S b => GenK.nu A B (S.code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .mu k w n b => GenK.mu A B w n fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .hylo k w b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    GenK.hylo A B w ((b.kids k A).getD .zero).dem b.dem (((b.kids k A).getD .zero).code η) fun X => b.code (η.bind k (GenK.const A B (.ok X)))
  | A, B, .prim r => primGen r A B []
  | _, _, .arg f x => f.argGen η [⟨_, _, x.code η⟩]
  | _, _, .call ks _ _ b | _, _, .callCv ks _ _ _ b _ => b.code (Code.args ks [])
termination_by 2 * t.size
decreasing_by all_goals simp only [Tm.size] at *; omega

/-- A spine `f` given its later relations' codes `xs` (`Expand.primOf`, `Expand.spine`), in the order `Tm.argDen`
    reads their meanings: a row's code of all of them, or a call's body's code with them bound at its `ks`; `share`
    seen through, built under no variable. A spine headed by neither is an error table, in the gap. -/
def Tm.argGen (η : Code) {A B : Obj} (t : Tm A B) (xs : Codes) : Rel A B :=
  match A, B, t with
  | A, B, .prim r => primGen r A B xs
  | _, _, .arg f x => f.argGen η (⟨_, _, x.code η⟩ :: xs)
  | _, _, .share _ R => R.argGen Code.empty xs
  | _, _, .call ks _ _ b | _, _, .callCv ks _ _ _ b _ => b.code (Code.args ks xs)
  | _, _, _ => .tab (.error "Tm.gen: a spine headed by neither a row nor a call is in the gap")
termination_by 2 * t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
end

/-- Whether `primGen r A B` given codes at the objects `xs` returns code, not its error table: the same lookups.
    A `rowGens` entry reads only its codes' objects (`Codes.at`), so `𝟘` at each stands for any code there. -/
def primHasCode (r : Prim) (A B : Obj) (xs : List (Obj × Obj)) : Bool :=
  match rowGens.lookup r.sym, r.objs A B with
  | some f, some σ => match f σ (xs.map fun (X, Y) => ⟨X, Y, GenK.zero X Y⟩) with
    | some ⟨A', B', _⟩ => decide (A' = A ∧ B' = B)
    | none => false
  | _, _ => false

mutual
/-- Whether `Tm.gen` emits real code at every node of `t`, by `Tm.gen`'s case split: false exactly where some node's
    `gen` (or `argGen`) returns its error table. Not `Tm.gap`, which says what is proved. -/
def Tm.hasCode {A B : Obj} (t : Tm A B) : Bool :=
  match A, B, t with
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. => true
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .est R
  | _, _, .thin R | _, _, .own R | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R | _, _, .flat R
  | _, _, .share _ R | _, _, .mu _ _ _ R => R.hasCode
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .foldr R S | _, _, .fold R S | _, _, .foldI R S
  | _, _, .nu _ R S => R.hasCode && S.hasCode
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.hasCode && S.hasCode && U.hasCode && V.hasCode
  | A, _, .hylo k _ b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    ((b.kids k A).getD .zero).hasCode && b.hasCode
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
    `B = [B']` (`τ`, `setify`), `[σ] ⟶ [[σ] × [σ]]` where it is `Λ(cat°)` on `A = [σ]` (`tails`), `ℕ ⟶ B` itself where
    it numbers a set in `canon`'s order (`asc`). -/
def rowsProved : List (String × (Obj → Obj → List (Obj × Obj))) :=
  let no : Obj → Obj → List (Obj × Obj) := fun _ _ => []
  let cod : Obj → Obj → List (Obj × Obj) := fun A B => match B with | .arr B' => [(A, B')] | _ => []
  [("∋", no), ("inl", no), ("inr", no), ("τ", cod), ("setify", cod), ("snoc", no), ("cons", no), ("cat", no),
   ("uncat", no), ("zip", no), ("length", no), ("sum", no), ("loop", no), ("filter", no), ("concat", no), ("merge", no),
   ("thinL", no), ("F", no), ("positions", no), ("asc", fun A B => [(A, B)]), ("inl°", no), ("inr°", no), ("tails", fun A _ => match A with | .arr σ => [(.arr σ, .prod (.arr σ) (.arr σ))] | _ => [])]

/-- The number of relations row `s` is given: its `prims` entry's, the one `rowGens` was generated from. A
    `rowGens` entry ignores a code past them, where `Prim.den` (`Sem.one`) is `𝟘`. -/
def rowArity (s : String) : Nat := ((prims.find? (·.sym == s)).map (·.sig.1.length)).getD 0

/-- Row `r` at `A ⟶ B` given relations at the objects `os` has a proved case: it is in `rowsProved`, given as many
    relations as it takes, and has code there (`primHasCode`), so no case holds through an error table. -/
def Prim.proved (r : Prim) (A B : Obj) (os : List (Obj × Obj)) : Bool :=
  (rowsProved.lookup r.sym).isSome && os.length == rowArity r.sym && primHasCode r A B os

mutual
/-- Some node of `t` has no proved case in `Tm.gen_sound`: no `GenK` lemma yet (`thin`), a `hylo` whose children's term
    (`Tm.kids`) is none or has a gap node, a row not `Prim.proved` at its relations' objects
    (`Tm.argGap`), or a spine headed by neither a row nor a call. A call reads its body (`Tm.size` counts it). -/
def Tm.gap : {A B : Obj} → Tm A B → Bool
  | A, B, .prim r => !r.proved A B []
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. => false
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R | _, _, .flat R | _, _, .share _ R
  | _, _, .est R | _, _, .mu _ _ _ R | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.gap
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .nu _ R S => R.gap || S.gap
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.gap || S.gap || U.gap || V.gap
  | _, _, .arg (C := C) (D := D) f x => f.argGap [(C, D)] || x.gap
  | _, _, .thin _ => true
  -- the children's term is no subterm (`Tm.kids`), only no larger than the body (`Tm.size_kids`)
  | A, _, .hylo k _ b =>
    have : ((b.kids k A).getD .zero).size ≤ b.size := Tm.size_kids k A b
    b.gap || (b.kids k A).isNone || ((b.kids k A).getD .zero).gap
termination_by _ _ t => t.size
decreasing_by all_goals simp only [Tm.size] at *; omega

/-- `Tm.argGen`'s case split: the spine `t` given later relations at the objects `os` has a gap node. -/
def Tm.argGap : {A B : Obj} → Tm A B → List (Obj × Obj) → Bool
  | A, B, .prim r, os => !r.proved A B os
  | _, _, .arg (C := C) (D := D) f x, os => f.argGap ((C, D) :: os) || x.gap
  | _, _, .share _ R, os => R.argGap os
  | _, _, .call _ _ _ R, _ | _, _, .callCv _ _ _ _ R _, _ => R.gap
  | _, _, _, _ => true
termination_by _ _ t _ => t.size
decreasing_by all_goals simp only [Tm.size] at *; omega
end

/-- The head of the spine `t` (`Expand.spine`): its row's symbol, or `call`. -/
def Tm.spineHead : {A B : Obj} → Tm A B → String
  | _, _, .prim r => r.sym
  | _, _, .arg f _ | _, _, .share _ f => f.spineHead
  | _, _, .call .. | _, _, .callCv .. => "call"
  | _, _, _ => "no row"

mutual
/-- The kinds of `t`'s gap nodes, by `Tm.gap`'s case split (`Tm.gap_eq`): a constructor's name, `prim s` for a row
    `s` not in `rowsProved`, `arg s` for an argument given to a spine headed by `s`. -/
def Tm.gapKinds : {A B : Obj} → Tm A B → List String
  | A, B, .prim r => if r.proved A B [] then [] else ["prim " ++ r.sym]
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. => []
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .lam R | _, _, .E R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R | _, _, .flat R | _, _, .share _ R
  | _, _, .est R | _, _, .mu _ _ _ R | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.gapKinds
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .nu _ R S =>
    R.gapKinds ++ S.gapKinds
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.gapKinds ++ S.gapKinds ++ U.gapKinds ++ V.gapKinds
  | _, _, .thin _ => ["thin"]
  -- a `hylo` whose children `Tm.kids` reads in no shape, or whose children's term has a gap node
  | A, _, .hylo k _ b =>
    b.gapKinds ++ if (b.kids k A).isNone || ((b.kids k A).getD .zero).gap then ["hylo"] else []
  | _, _, .arg (C := C) (D := D) f x => f.argGapKinds [(C, D)] ++ x.gapKinds

/-- `Tm.argGap`'s kinds: `arg s` for a spine headed by `s` that is no `Prim.proved` row at its relations. -/
def Tm.argGapKinds : {A B : Obj} → Tm A B → List (Obj × Obj) → List String
  | A, B, .prim r, os => if r.proved A B os then [] else ["arg " ++ r.sym]
  | _, _, .arg (C := C) (D := D) f x, os => f.argGapKinds ((C, D) :: os) ++ x.gapKinds
  | _, _, .share _ R, os => R.argGapKinds os
  | _, _, .call _ _ _ R, _ | _, _, .callCv _ _ _ _ R _, _ => R.gapKinds
  | _, _, t, _ => ["arg " ++ t.spineHead]
end

theorem Tm.gap_eq_spine {A B : Obj} (t : Tm A B) :
    t.gap = !t.gapKinds.isEmpty ∧ ∀ os, t.argGap os = !(t.argGapKinds os).isEmpty := by
  induction t
  case prim r =>
    refine ⟨?_, fun os => ?_⟩
    · simp only [Tm.gap, Tm.gapKinds]; split <;> simp_all
    · simp only [Tm.argGap, Tm.argGapKinds]; split <;> simp_all
  case arg f x ihf ihx =>
    refine ⟨?_, fun os => ?_⟩ <;>
      simp only [Tm.gap, Tm.gapKinds, Tm.argGap, Tm.argGapKinds, ihf.2, ihx.1] <;>
      exact (fun a b => by cases a <;> cases b <;> rfl :
        ∀ a b : List String, (!a.isEmpty || !b.isEmpty) = !(a ++ b).isEmpty) _ _
  case share _ R ih =>
    exact ⟨by simp only [Tm.gap, Tm.gapKinds, ih.1], fun os => by simp only [Tm.argGap, Tm.argGapKinds, ih.2 os]⟩
  case call _ _ _ b ih | callCv _ _ _ _ b _ ih _ =>
    exact ⟨by simp only [Tm.gap, Tm.gapKinds, ih.1], fun _ => by simp only [Tm.argGap, Tm.argGapKinds, ih.1]⟩
  all_goals refine ⟨?_, fun os => by simp [Tm.argGap, Tm.argGapKinds]⟩
  all_goals simp only [Tm.gap, Tm.gapKinds, *]
  all_goals first
    | rfl
    | (rw [Bool.eq_iff_iff]; simp [Decidable.imp_iff_not_or, or_assoc])
    | (split <;> simp_all [Bool.or_assoc])

theorem Tm.gap_eq {A B : Obj} (t : Tm A B) : t.gap = !t.gapKinds.isEmpty := (Tm.gap_eq_spine t).1

/-- What `Tm.gen_sound` asks of `t` besides no `Tm.gap` node, with `L` for the order law of a `Λ`: `L` at each `Λ`
    and `E` (`E(R) = Λ(∋ ≫ R)`, at `[A] ⟶ [B]`) and at each row `rowsProved` marks, and the body of each fixed
    point positive in its variable (`Tm.pol`, which `Tm.den_mono` reads). -/
def Tm.LamLawsAt (L : Obj → Obj → Prop) : {A B : Obj} → Tm A B → Prop
  | A, B, .prim r => ∀ f, rowsProved.lookup r.sym = some f → ∀ p ∈ f A B, L p.1 p.2
  | _, _, .lam (A := A) (B := B) R => L A B ∧ R.LamLawsAt L
  | _, _, .E (A := A) (B := B) R => L (.arr A) B ∧ R.LamLawsAt L
  | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R | _, _, .succ R | _, _, .arith _ R
  | _, _, .leq R | _, _, .lt R | _, _, .flat R | _, _, .share _ R | _, _, .est R | _, _, .call _ _ _ R
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
  | _, _, .atPos _ | _, _, .var .. | _, _, .thin _ => True

/-- `Tm.LamLawsAt` with `LamLaw`, the premise of `Tm.gen_sound`. -/
abbrev Tm.LamLaws {A B : Obj} (t : Tm A B) : Prop := t.LamLawsAt LamLaw

/-- The decidable part of `Tm.LamLawsAt`, every conjunct but `L` (`Tm.monoOK_iff`): what `GenSoundTest` evaluates
    beside `Tm.gap`, since `LamLawsAt L` implies it for every `L` (`Tm.LamLawsAt.mono`). -/
def Tm.monoOK : {A B : Obj} → Tm A B → Bool
  | _, _, .lam R | _, _, .E R | _, _, .top R | _, _, .conv R | _, _, .dom R | _, _, .ran R | _, _, .own R
  | _, _, .succ R | _, _, .arith _ R | _, _, .leq R | _, _, .lt R | _, _, .flat R | _, _, .share _ R
  | _, _, .est R | _, _, .call _ _ _ R | _, _, .callCv _ _ _ _ R _ => R.monoOK
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S | _, _, .pair R S | _, _, .prod R S
  | _, _, .fold R S | _, _, .foldr R S | _, _, .foldI R S | _, _, .arg R S => R.monoOK && S.monoOK
  | _, _, .ldiv R S U V | _, _, .rdiv R S U V => R.monoOK && S.monoOK && U.monoOK && V.monoOK
  | _, _, .nu k S b => b.pol true k && S.monoOK && b.monoOK
  | _, _, .mu k _ _ b | _, _, .hylo k _ b => b.pol true k && b.monoOK
  | _, _, .val _ | _, _, .uni _ | _, _, .zero | _, _, .id | _, _, .outl | _, _, .outr | _, _, .nil
  | _, _, .atPos _ | _, _, .var .. | _, _, .thin _ | _, _, .prim _ => true

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
      refine (reps_iff _ _ _).2 fun t' h' x y _ _ => ?_
      cases h'; exact (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl
    next => exact hR K
  | bits => exact (reps_iff _ _ _).2 fun t h x y _ _ => (reps_iff _ _ _).1 (hR {}) t h x y rfl rfl

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
  unfold primGen Prim.den; rw [hs, hf, hD]
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
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;> have hB := hl _ (by rw [hs]; rfl) _ (List.mem_singleton_self _) <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tau_den h hB⟩

theorem rowOK_setify : RowOK "setify" := rowOK_of (c := RowCode.setify) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;> have hB := hl _ (by rw [hs]; rfl) _ (List.mem_singleton_self _) <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.setify_den h hB⟩

/-- An array is below itself extended by a non-empty one (`Obj.lt` on `[B]`: a proper prefix first). -/
theorem arr_lt_append (B : Obj) : ∀ (xs ys : List B.El), ys ≠ [] → (Obj.arr B).lt xs (xs ++ ys)
  | [], [], h => (h rfl).elim
  | [], y :: ys, _ => Obj.lt_nil_cons B y ys
  | x :: xs, ys, h => (Obj.lt_cons B x x xs (xs ++ ys)).2 (Or.inr ⟨rfl, arr_lt_append B xs ys h⟩)

/-- **`Λ(cat°)` at `xs`**: the one list strictly ascending in `Obj.lt` of the splits `(p₁, p₂)` of `xs` is the splits by
increasing split point, since a shorter first part is a proper prefix of a longer one. -/
theorem lamDen_splits {B : Obj} {T : Den (.arr B) (.prod (.arr B) (.arr B))} (xs : List B.El)
    (hT : ∀ p, T xs p ↔ xs = p.1 ++ p.2) (zs : List (Obj.prod (.arr B) (.arr B)).El) :
    lamDen T xs zs ↔ zs = (List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k) := by
  have hL : ((List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k)).Pairwise
      (Obj.prod (.arr B) (.arr B)).lt := (pairwise_map_range_iff _ _ _).2 fun i j hij hj => by
    have h := arr_lt_append B (xs.take i) ((xs.take j).drop i) fun h0 => by
      have := congrArg List.length h0; simp at this; omega
    have e : xs.take i ++ (xs.take j).drop i = xs.take j := by
      have t := List.take_append_drop i (xs.take j)
      rwa [List.take_take, Nat.min_eq_left (by omega)] at t
    rw [e] at h
    exact (Obj.lt_prod _ _ _ _ _ _).2 (Or.inl h)
  have hmem : ∀ p, p ∈ ((List.range (xs.length + 1)).map fun k => (xs.take k, xs.drop k)) ↔ T xs p := fun p => by
    rw [hT, List.mem_map]
    constructor
    · rintro ⟨k, -, rfl⟩; exact (List.take_append_drop k xs).symm
    · intro h; subst h; exact ⟨p.1.length, by simp; omega, by simp⟩
  exact ⟨fun ⟨hp, hm⟩ => pairwise_eq_of_mem (Obj.lt_irrefl _) (fun _ _ => Obj.lt_asymm _) hp hL
    fun p => (hm p).trans (hmem p).symm, fun h => h ▸ ⟨hL, hmem⟩⟩

/-- **`tails` on the cells `X`** (`Tab.tails`) = `Λ(cat°) ≫ F(π₂)`: each array of `X` to its suffixes by decreasing
length, given the order law of `Λ` at `[B] ⟶ [[B] × [B]]`. -/
theorem Tab.tails_den {B : Obj} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr (.arr B))}
    (h : Tab.tails X = .ok T) (hB : LamLaw (.arr B) (.prod (.arr B) (.arr B))) (xs : List B.El)
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
    obtain ⟨hx, hd⟩ := (Tab.lam_den hL hB xs _).1 ⟨i, hk, rfl⟩
    refine ⟨hx, ?_⟩
    rw [← hv, hrow, (hs hx _).1 hd, List.map_map]; rfl
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hk, hv⟩ := (Tab.lam_den hL hB xs _).2 ⟨hx, (hs hx _).2 rfl⟩
    exact ⟨i, hk, by rw [hrow]; simp only at hv; rw [hv, List.map_map]; rfl⟩

theorem rowOK_tails : RowOK "tails" := rowOK_of (c := RowCode.tails) rfl rfl fun _ σ _ _ _ hs hv => by
  cases hv
  cases σ <;> refine ⟨GenK.ofVals_wf, fun hl => ?_⟩ <;>
    have hB := hl _ (by rw [hs]; rfl) _ (List.mem_singleton_self _) <;>
    exact ⟨⟨rfl, rfl⟩, GenK.ofVals_row_sound fun _ _ _ h => Tab.tails_den h hB⟩

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
    have hB := hl _ (by rw [hs]; rfl) _ (List.mem_singleton_self _)
    rcases ss with _ | ⟨⟨X', Y', T⟩, _ | ⟨_, _⟩⟩ <;> simp only [CodesRep, and_true, and_false] at hss
    split at hss
    case isFalse => exact hss.elim
    rename_i he; revert hss; obtain ⟨h1, h2⟩ := he; subst h1; subst h2; intro hss
    simp only [Sem.one]
    split
    · exact GenK.ofRel_sound hss fun _ _ h hr => by subst hr; exact Tab.asc_holds h hB
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
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (∃ c, TQ (a, b) c)) :=
  GenK.after_row_sound fun _ _ h k zs => Tab.merge_holds (fun D _ hT p _ hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl) h k zs

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
      (thinLDen fun a b => decide (∃ c, TQ (a, b) c)) :=
  GenK.ofVals_row_sound fun _ _ _ h xs w => Tab.thinL_holds (fun D _ hT p _ hp =>
    (GenK.reps_iff ⟨some ⟨D.n, D.val⟩, none⟩ _ _).1 (hQ _) _ hT p _ ((GenK.side_some rfl p).2 hp) rfl) h xs w

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

/-- Every row of `rowsProved` is `RowOK`: the obligations enumerated from the list `Tm.gap` reads. -/
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
  simp [rowsProved, List.lookup, beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4,
    beq_false_of_ne h5, beq_false_of_ne h6, beq_false_of_ne h7, beq_false_of_ne h8, beq_false_of_ne h9,
    beq_false_of_ne h10, beq_false_of_ne h11, beq_false_of_ne h12, beq_false_of_ne h13, beq_false_of_ne h14,
    beq_false_of_ne h15, beq_false_of_ne h16, beq_false_of_ne h17, beq_false_of_ne h18,
    beq_false_of_ne h19, beq_false_of_ne h20, beq_false_of_ne h21, beq_false_of_ne h22, beq_false_of_ne h23] at h

/-- A `Prim.proved` row is `RowOK`, given as many relations as it takes. -/
theorem Prim.proved_ok {r : Prim} {A B : Obj} {os : List (Obj × Obj)} (h : (!r.proved A B os) = false) :
    RowOK r.sym ∧ os.length = rowArity r.sym := by
  simp only [Prim.proved, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨rowsProved_ok r h.1.1, h.1.2⟩

theorem Tm.code_wf {η : Code} {A B : Obj} {t : Tm A B} (h : (t.gen η).Wf) : (t.code η).Wf := by
  rw [Tm.code]; split
  · exact GenK.memo_wf h
  · exact h

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** off the gap: only `comp` builds one (`GenK.comp_wf`), a
    variable reads `η`'s, and every other op returns tables. -/
theorem Tm.gen_wf_spine {A B : Obj} (t : Tm A B) :
    (∀ η : Code, t.gap = false → (∀ k A B, (η k A B).Wf) → (t.gen η).Wf) ∧
    ∀ (η : Code) (xs : Codes), t.argGap (xs.map fun x => (x.1, x.2.1)) = false → (∀ k A B, (η k A B).Wf) →
      (∀ x ∈ xs, x.2.2.Wf) → (t.argGen η xs).Wf := by
  induction t
  case prim r =>
    refine ⟨fun η hg _ => ?_, fun η xs hg _ hx => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.gen, Tm.argGen] <;> obtain ⟨ok, hn⟩ := Prim.proved_ok hg
    · exact (ok r _ _ [] rfl hn (fun _ h => nomatch h)).1
    · exact (ok r _ _ xs rfl (by simpa using hn) hx).1
  case arg f x ihf ihx =>
    refine ⟨fun η hg hη => ?_, fun η xs hg hη hx => ?_⟩ <;> simp only [Tm.gap, Tm.argGap, Bool.or_eq_false_iff] at hg <;>
      simp only [Tm.gen, Tm.argGen] <;> refine ihf.2 η _ hg.1 hη fun y hy => ?_ <;>
      rcases List.mem_cons.1 hy with rfl | hy
    any_goals exact code_wf (ihx.1 η hg.2 hη)
    all_goals first | exact hx y hy | simp at hy
  case share _ R ih =>
    refine ⟨fun η hg _ => ?_, fun η xs hg _ hx => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.gen, Tm.argGen]
    · exact code_wf (ih.1 Code.empty hg fun _ _ _ => trivial)
    · exact ih.2 Code.empty xs hg (fun _ _ _ => trivial) hx
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η hg _ => ?_, fun η xs hg _ hx => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.gen, Tm.argGen]
    · exact code_wf (ih.1 _ hg (Code.args_wf ks [] fun _ h => nomatch h))
    · exact code_wf (ih.1 _ hg (Code.args_wf ks xs hx))
  all_goals refine ⟨fun η hg hη => ?_, fun η xs hg => by simp [Tm.argGap] at hg⟩
  all_goals simp only [Tm.gap, Bool.or_eq_false_iff, Bool.true_eq_false] at hg <;> simp only [Tm.gen]
  case comp R S ihR ihS => exact GenK.comp_wf _ (code_wf (ihS.1 η hg.2 hη))
  case ldiv R S U V ihR ihS ihU ihV => exact GenK.ldiv_wf _ _ _ (code_wf (ihS.1 η hg.1.1.2 hη))
  case own R ih => exact code_wf (ih.1 η hg hη)
  case var k => exact hη k _ _
  all_goals first
    | trivial
    | exact GenK.ofVals_wf
    | exact GenK.top_wf
    | exact GenK.meet_wf _ _
    | exact GenK.diff_wf _ _
    | exact GenK.lift1_wf _
    | exact GenK.lift2_wf _ _
    | exact fun _ => trivial
    | (intro K; cases h : K.dom <;> simp [h, Rel.Rel.Wf])

/-- **Every bit matrix `Tm.gen` passes on is `Rel.Wf`** off the gap (`Tm.gen_wf_spine`, its first half). -/
theorem Tm.gen_wf {A B : Obj} (t : Tm A B) :
    ∀ η : Code, t.gap = false → (∀ k A B, (η k A B).Wf) → (t.gen η).Wf := (Tm.gen_wf_spine t).1

/-- `Tm.gen_sound` with its spine half: a spine with no gap node, given codes `xs` that are `Wf` and represent
    `ss`, generates code that represents its meaning of `ss` (`Tm.argGen`, `Tm.argDen`). -/
theorem Tm.gen_sound_spine {A B : Obj} (t : Tm A B) :
    (∀ (η : Code) (ρ : Val), t.gap = false → t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
    ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem), t.argGap (xs.map fun x => (x.1, x.2.1)) = false →
      t.LamLaws → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
        ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) := by
  -- strong induction on `Tm.size`: a `hylo`'s children's term (`Tm.kids`) is no subterm, only no larger than its body
  suffices H : ∀ n {A B : Obj} (t : Tm A B), t.size ≤ n →
      (∀ (η : Code) (ρ : Val), t.gap = false → t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)) ∧
      ∀ (η : Code) (ρ : Val) (xs : Codes) (ss : List Sem), t.argGap (xs.map fun x => (x.1, x.2.1)) = false →
        t.LamLaws → Sound η ρ → (∀ x ∈ xs, x.2.2.Wf) → CodesRep xs ss →
          ∀ K, (t.argGen η xs).Reps K (t.argDen ρ ss) from H _ t (Nat.le_refl _)
  -- a fixed point's round binds its variable to its table (`Sound.bind`)
  have hconst {A B : Obj} (Y : Tab A B) : ∀ K, (GenK.const A B (.ok Y)).Reps K (rep Y) :=
    fun _ => (GenK.reps_iff _ _ _).2 fun t ht x y _ _ => by cases ht; exact Iff.rfl
  intro n
  induction n
  case zero => intro A B t h; cases t <;> simp [Tm.size] at h
  rename_i n H
  intro A B t
  induction t <;> intro hn <;> simp only [Tm.size] at hn
  case prim r =>
    refine ⟨fun η ρ hg hl _ => ?_, fun η ρ xs ss hg hl _ hx hr => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen] <;> obtain ⟨ok, hn⟩ := Prim.proved_ok hg
    · exact (ok r _ _ [] rfl hn (fun _ h => nomatch h)).2 [] trivial hl
    · exact (ok r _ _ xs rfl (by simpa using hn) hx).2 ss hr hl
  case arg C D f x ihf ihx =>
    have step (η ρ) (xs : Codes) (ss : List Sem)
        (hg : f.argGap ((C, D) :: xs.map fun x => (x.1, x.2.1)) = false ∧ x.gap = false)
        (hl : f.LamLaws ∧ x.LamLaws) (hs : Sound η ρ) (hx : ∀ y ∈ xs, y.2.2.Wf) (hr : CodesRep xs ss) :
        ∀ K, (f.argGen η (⟨C, D, x.code η⟩ :: xs)).Reps K (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) :=
      (ihf (by omega)).2 η ρ _ _ hg.1 hl.1 hs (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact code_wf (gen_wf x η hg.2 hs.2)
          · exact hx y hy)
        ⟨by rw [dif_pos ⟨rfl, rfl⟩]; exact code_of ((ihx (by omega)).1 η ρ hg.2 hl.2 hs), hr⟩
    refine ⟨fun η ρ hg hl hs => ?_, fun η ρ xs ss hg hl hs hx hr => ?_⟩ <;>
      simp only [Tm.gap, Tm.argGap, Bool.or_eq_false_iff] at hg <;> simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;>
      simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact step η ρ [] [] hg hl hs (fun _ h => nomatch h) trivial
    · exact step η ρ xs ss hg hl hs hx hr
  case share _ R ih =>
    have he : Sound Code.empty Val.empty := ⟨fun _ _ _ => GenK.zero_sound, fun _ _ _ => trivial⟩
    refine ⟨fun η ρ hg hl _ => ?_, fun η ρ xs ss hg hl _ hx hr => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact code_of ((ih (by omega)).1 Code.empty Val.empty hg hl he)
    · exact (ih (by omega)).2 Code.empty Val.empty xs ss hg hl he hx hr
  -- the body under its arguments bound at `ks` (`Sound.args`), whatever the caller's `η`, `ρ`
  case call ks _ _ b ih | callCv ks _ _ _ b _ ih _ =>
    refine ⟨fun η ρ hg hl _ => ?_, fun η ρ xs ss hg hl _ hx hr => ?_⟩ <;> simp only [Tm.gap, Tm.argGap] at hg <;>
      simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den, Tm.argGen, Tm.argDen]
    · exact code_of ((ih (by omega)).1 _ _ hg hl (Sound.args ks [] [] (fun _ h => nomatch h) trivial))
    · exact code_of ((ih (by omega)).1 _ _ hg hl (Sound.args ks xs ss hx hr))
  all_goals refine ⟨fun η ρ hg hl hs => ?_, fun η ρ xs ss hg => by simp [Tm.argGap] at hg⟩
  all_goals simp only [Tm.gap, Bool.or_eq_false_iff, Bool.true_eq_false] at hg <;>
    simp only [Tm.LamLaws, Tm.LamLawsAt] at hl <;> simp only [Tm.gen, Tm.den]
  case val R => exact GenK.val_sound (R, true)
  case uni U => exact GenK.uni_sound (U, true)
  case zero => exact GenK.zero_sound
  case id => exact GenK.id_sound
  case top V ih => exact GenK.top_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case outl => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
  case outr => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.outr_holds h
  case comp R S ihR ihS =>
    exact GenK.comp_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf S η hg.2 hs.2))
  case conv R ih => exact GenK.conv_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case meet R S ihR ihS =>
    exact GenK.meet_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf R η hg.1 hs.2)) (code_wf (gen_wf S η hg.2 hs.2))
  case join R S ihR ihS => exact GenK.join_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
  case diff R S ihR ihS => exact GenK.diff_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
  case dom R ih => exact GenK.dom_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case ran R ih => exact GenK.ran_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case rdiv R S U V ihR ihS ihU ihV =>
    exact GenK.rdiv_sound (code_of ((ihR (by omega)).1 η ρ hg.1.1.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.1.1.2 hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hg.1.2 hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hg.2 hl.2.2.2 hs))
  case ldiv R S U V ihR ihS ihU ihV =>
    exact GenK.ldiv_sound (code_of ((ihR (by omega)).1 η ρ hg.1.1.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.1.1.2 hl.2.1 hs))
      (code_of ((ihU (by omega)).1 η ρ hg.1.2 hl.2.2.1 hs)) (code_of ((ihV (by omega)).1 η ρ hg.2 hl.2.2.2 hs))
      (code_wf (gen_wf S η hg.1.1.2 hs.2))
  case pair R S ihR ihS => exact GenK.pair_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
  case prod R S ihR ihS => exact GenK.prod_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
  case fold R S ihR ihS =>
    exact GenK.fold_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf S η hg.2 hs.2))
  case foldr R S ihR ihS =>
    exact GenK.foldr_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs))
      (code_wf (gen_wf S η hg.2 hs.2))
  case foldI R S ihR ihS =>
    exact GenK.foldI_sound (code_of ((ihR (by omega)).1 η ρ hg.1 hl.1 hs)) (code_wf (gen_wf R η hg.1 hs.2))
      (code_of ((ihS (by omega)).1 η ρ hg.2 hl.2 hs)) (code_wf (gen_wf S η hg.2 hs.2))
  case lam R ih => exact GenK.lam_sound (code_of ((ih (by omega)).1 η ρ hg hl.2 hs)) hl.1
  case E R ih =>
    exact GenK.lam_sound (GenK.comp_sound (GenK.ofVals_row_sound fun _ _ _ h => Tab.mem_holds h)
      (code_of ((ih (by omega)).1 η ρ hg hl.2 hs)) (code_wf (gen_wf R η hg hs.2))) hl.1
  case nil => exact GenK.ofVals_row_sound fun _ _ _ h => Tab.nil_holds h
  case own R ih => exact code_of ((ih (by omega)).1 η ρ hg hl hs)
  case succ U ih => exact GenK.succ_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case arith U ih => exact GenK.arith_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case leq U ih => exact GenK.cmp_sound (fun _ _ _ h => Tab.leq_holds h) (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case lt U ih => exact GenK.cmp_sound (fun _ _ _ h => Tab.lt_holds h) (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case flat R ih => exact GenK.flat_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case var k => exact hs.1 k _ _
  case est Q ih => exact GenK.est_sound (code_of ((ih (by omega)).1 η ρ hg hl hs))
  case atPos k => exact GenK.atPos_sound k
  case nu k S b ihS ihb =>
    exact GenK.nu_sound (code_of ((ihS (by omega)).1 η ρ hg.1 hl.2.1 hs))
      (fun X => code_of ((ihb (by omega)).1 _ _ hg.2 hl.2.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  case mu k w m b ih =>
    exact GenK.mu_sound (fun X => code_of ((ih (by omega)).1 _ _ hg hl.2 (hs.bind k (hconst X) (by trivial)))) fun _ _ h => Tm.den_mono hl.1 h
  case hylo A' B' k w b ih =>
    have hc := Tm.lamLawsAt_kids k A' b hl.2
    have hsz := Tm.size_kids k A' b
    revert hg hc hsz
    cases hk : b.kids k A' with
    | none => simp
    | some c =>
      intro hg hc hsz
      simp only [Option.isNone_some, Option.getD_some, and_true] at hg hc hsz ⊢
      exact GenK.hylo_sound ((H c (by omega)).1 η ρ hg.2 hc hs |> code_of) (code_wf (gen_wf c η hg.2 hs.2))
        (fun Y => code_of ((ih (by omega)).1 _ _ hg.1 hl.2 (hs.bind k (hconst Y) (by trivial))))
        (fun Y => code_wf (gen_wf b _ hg.1 (hs.bind k (hconst Y) (by trivial)).2))
        (fun _ _ h => Tm.den_mono hl.1 h) (fun X Y a h => Tm.den_local k ρ X Y b c hk a h)

/-- **`Tm.gen` is sound off the gap**: the code of a term with no `Tm.gap` node represents its meaning in every
    context, given `LamLaw` at each `Λ`, and an environment `η` that represents `ρ`. -/
theorem Tm.gen_sound {A B : Obj} (t : Tm A B) :
    ∀ (η : Code) (ρ : Val), t.gap = false → t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ) :=
  (Tm.gen_sound_spine t).1

end Rel.Lang
