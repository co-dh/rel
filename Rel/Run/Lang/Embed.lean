module

public meta import Rel.Run.Lang.Grammar
public meta import Rel.Run.Lang.TmGen
public meta import Rel.Run.Table
public meta import Lean

public meta section

/-! The command `rel_program n where`: it reads the grammar (`Grammar`) into the AST and defines `n : Program`;
    `Expand.emit` defines what it reads. -/

namespace Rel.Lang.Embed

open Lean Parser Elab Elab.Command Parser.Command
open Rel.Lang
open Rel.Lang.Expand (programOf resolverAt reread)
open Rel.Lang.Parse (P)
/-- The parameters `ps` of the definition or theorem `w`, each a name no builtin takes, each once. -/
def params (s : Syntax) (w : String) (ps : Array Syntax) : C (List Param) := do
  let ps ← ps.toList.mapM fun q => do
    let n ← wordOf q[0]
    if (Parse.builtin n).isSome then failAt q s!"`{n}` is a builtin; choose another name"
    pure (⟨n, ← q[1].getOptional?.mapM typeOf⟩ : Param)
  let _ ← ps.foldlM (fun (seen : List String) q => do
    if seen.contains q.name then failAt s s!"`{q.name}` is already a parameter of `{w}`"
    pure (q.name :: seen)) []
  pure ps

/-- A definition: `w` its name, `key` it or its infix key `_w_`. -/
def defn (s : Syntax) (w key : String) (ps : Array Syntax) (ty body test wh : Syntax) : C Decl := do
  let p ← posOf s
  Parse.fresh p w (← get).taken
  let ps ← params s w ps
  if key != w && ps.length != 2 then
    failAt s s!"the infix operator `{w}` takes two parameters, `{key}(R, S)`, found {ps.length}"
  let ty ← ty.getOptional?.mapM typeOf
  let outer := (← get).known
  let ovars := ((ty.toList ++ ps.filterMap (·.ty)).flatMap fun (a, b) => a.vars ++ b.vars).eraseDups
  modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known, ovars }
  -- the `where` items first: each in scope in the items after it and in the body (§c)
  let σ ← (if wh.getNumArgs == 0 then #[] else wh[1].getSepArgs).foldlM (init := []) fun σ i => do
    let q ← posOf i
    let n ← wordOf i[0]
    Parse.fresh q n ((key, Parse.at_ p) :: (← get).taken)
    if ps.any (·.name == n) then failAt i s!"`{n}` is already a parameter of `{w}`"
    if σ.any (·.1 == n) then failAt i s!"`{n}` is already an item of this `where`"
    let σ := σ ++ [(n, q, ← expr i[2])]
    modify fun st => { st with known := (n, 0) :: st.known }
    pure σ
  -- each item a binder around the items after it and the body, computed once (`Expr.whr`)
  let wh (e : Expr) : Expr := σ.foldr (fun (n, q, i) b => .whr q n i b) e
  let e := wh (← expr body)
  let b ← if test.getNumArgs == 0 then pure (Body.rel e) else do pure (Body.test e (wh (← expr test[1])))
  if let (.test .., some t) := (b, ty) then
    failAt s s!"the test `{w}` has no type of its own: drop ': {OExp.arrow t}' (§e)"
  modify fun st => { st with known := outer, ovars := [] }
  pure (.defn p key ps b ty)

/-- The lemma `theorem n … by lemma` names, refused beside a `calc` or `on`: a Lean proof states the
    whole theorem, which has neither (an `if` hypothesis is a premise of its statement). -/
def proofOf (s : Syntax) (n : String) : C (Option Lean.Name) := do
  if s[10].getNumArgs == 0 then return none
  let l := s[10][1].getId
  let bad := [(s[9].getNumArgs != 0, "a `calc`"), (s[3].getNumArgs != 0, "`on`")].filter (·.1)
  if let some (_, what) := bad.head? then
    failAt s[10] s!"theorem `{n}` has `by {l}` and {what}: a Lean proof is written for a theorem with none"
  pure (some l)

/-- `theorem n(ps) on A if hs : e = f := calc … by lemma` (split from `stmt`, whose elaboration it would push past the
    heartbeat limit). -/
def theoremDecl (s : Syntax) (p : Pos) : C Decl := do
  let opt (o : Syntax) := if o.getNumArgs == 0 then #[] else o[1].getSepArgs
  let n ← wordOf s[1]
  Parse.fresh p n (← get).taken
  let ps ← params s n (opt s[2])
  let proof ← proofOf s n
  if s[3].getNumArgs != 0 && !ps.isEmpty then
    failAt s[3] s!"`on` evaluates a theorem with no parameters; `{n}` has {ps.length}"
  let outer := (← get).known
  let ovars := Expand.paramVars ps
  modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known, ovars }
  let on ← if s[3].getNumArgs == 0 then pure none else some <$> expr s[3][1]
  let hyps ← (opt s[4]).toList.mapM fun h => do
    let a ← expr h[0]
    if h[1].getNumArgs == 0 then pure (a, none) else pure (a, some (atomIn h[1][0] == "=", ← expr h[1][1]))
  let e ← expr s[6]; let f ← expr s[8]; let eq := atomIn s[7] == "="
  -- a reason is the program's theorem or definition, else the registry's one the resolver gives
  let steps ← (if s[9].getNumArgs == 0 then #[] else s[9][3].getArgs).toList.mapM fun l => do
    let t := l[0]; let u := l[1]
    unless t.getKind == ``cReason do failAt t "expected a reason line `[⊑] := n`"
    unless u.getKind == ``cTerm do failAt u "expected a term after the reason line"
    let q ← posOf u; let x ← expr u[0]; let r ← posOf t[3]
    -- a qualified reason, `laws.estMap`, is read as a term reads `m.x`; a bare one is one word
    let m ← match t[3][0] with
      | .ident _ _ c _ => if c.isAtomic then wordOf t[3] else onText t[3] (tokText t[3][0]) Parse.name
      | _ => wordOf t[3]
    let st ← get
    -- a name not the program's is the registry's, through the resolver (§2.3), whose refusal (ambiguous) is the error
    let own := st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) || st.thms.contains m
    let ex ← if own || ps.any (·.name == m) then pure none else match st.res m with
      | .ext e => pure (some e)
      | .bad _ msg => failAt t[3] msg
      | .none => pure none
    if let some e := ex then modify fun st => { st with used := e.const :: st.used }
    let isDef := (st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) && !ps.any (·.name == m)) ||
      ex.any (fun e => !e.obj && !e.thm)
    let isThm := st.thms.contains m || ex.any (·.thm)
    let args ← if t[4].getNumArgs == 0 then pure [] else t[4][1].getSepArgs.toList.mapM expr
    if t[2].getNumArgs != 0 && !args.isEmpty then failAt t[4] s!"`≜ {m}` unfolds a definition: it takes no arguments"
    let why ← if t[2].getNumArgs == 0 then
        if isThm then pure (Why.thm r m (if st.thms.contains m then none else ex.map (·.const)) args)
        else failAt t[3] (if isDef then s!"`{m}` is a definition; write `≜ {m}`" else s!"unknown theorem '{m}'")
      else if isDef then pure (Why.unfold r m)
        else failAt t[3] (if isThm then s!"`{m}` is a theorem, not a definition"
          else s!"unknown definition '{m}'")
    -- a link with no operator is `=`
    let isEq := atomIn t[0] != "⊑"
    if eq && !isEq then failAt t s!"`{n}` states `=`: a step `⊑` proves only `⊑`"
    pure (q, isEq, x, why)
  -- the chain starts at the left side and ends at the right one, compared as the parser reads both
  let first := s[9][2]
  if s[9].getNumArgs != 0 then
    unless first.getKind == ``cTerm do failAt first "expected the chain's first term"
    let a ← expr first[0]
    if a.render 0 true != e.render 0 true then
      failAt first s!"the chain starts at `{a.show}`, the statement's left side is `{e.show}`"
  if let some (q, _, x, _) := steps.getLast? then
    if x.render 0 true != f.render 0 true then
      throw ⟨q, s!"the chain of `{n}` ends at {x.show}, not at its right side {f.show}"⟩
  modify fun st => { st with known := outer, ovars := [] }
  pure (.«theorem» p n ps e f eq on hyps steps proof)

def stmt (s : Syntax) : C Decl := do
  let p ← posOf s
  let objName : C String := do
    let n ← wordOf s[1]
    if let some r := (← get).taken.lookup n then failAt s[1] s!"`{n}` is already defined {r}"
    pure n
  let objDecl (d : C ObjDef) : C Decl := do let n ← objName; pure (.obj p n (← d))
  let num (w : Syntax) : C Int := do onText w[0] "" (Parse.num (← wordOf w))
  let opt (o : Syntax) := if o.getNumArgs == 0 then #[] else o[1].getSepArgs
  -- a `check`'s or `print`'s `where`: each item read in the statement's scope, each name once (`walk` checks it is
  -- an input)
  let binds (o : Syntax) : C (List (String × Expr)) := (opt o).foldlM (init := []) fun σ i => do
    let n ← wordOf i[0]
    if σ.any (·.1 == n) then failAt i s!"`{n}` is already an item of this `where`"
    pure (σ ++ [(n, ← expr i[2])])
  let path (t : Syntax) : C String := match t.isStrLit? with
    | some f => pure f
    | none => failAt t "expected the path as a string literal"
  -- `csv` and its optional separator, a one-byte char literal (`,` when none is written)
  let csvSep (o : Syntax) : C (Option UInt8) := if o.getNumArgs == 0 then pure none else
    if o[1].getNumArgs == 0 then pure (some 44) else match o[1][0].isCharLit? with
      | some c => if c.val < 128 then pure (some c.toNat.toUInt8) else failAt o[1] s!"the separator {repr c} is not one byte"
      | none => failAt o[1] "expected the separator as a char literal"
  match s.getKind with
  | ``sElems => objDecl do pure (.elems (← s[4].getSepArgs.toList.mapM wordOf))
  | ``sRange => objDecl do
    let lo ← num s[3]; let hi ← num s[5]
    if hi < lo then failAt s[5] s!"the range {lo}…{hi} is empty: {hi} is below {lo}"
    pure (.range lo hi)
  | ``sAlias => objDecl do pure (.alias (← obj s[3]))
  | ``sNum => objDecl do pure (.num .i64)
  -- the atom by its constructor's name (`atomNames`), refused where no literal column of it is built (`litLayout`)
  | ``sNumAt => objDecl do
    let ok := (atomNames.filter fun (_, t) => (litLayout t).isSome).map (·.1)
    match atomNames.lookup s[3].getId with
    | some t => if (litLayout t).isSome then pure (.num t) else
        failAt s[3] s!"an object of {atomName t} is not declared: no literal of {atomName t} is stored; the atoms are {ok}"
    | none => failAt s[3] s!"unknown atom '{s[3].getId}'; the atoms are {ok}"
  | ``sSchema => objDecl do
    let cs ← s[4].getSepArgs.toList.mapM fun f => do pure (← wordOf f[0], ← obj f[2])
    -- a column twice is refused where it is written, by the check every `Schema` function makes
    if let .error m := Schema.check cs then failAt s[4] m
    pure (.schema cs)
  | ``sSchemaEach => objDecl do
    let c ← wordOf s[4]; let v ← wordOf s[6]; let o ← obj s[8]
    let some ws ← onText s[6] "" (Parse.finOf v)
      | failAt s[6] s!"`{v}` is no finite object of this program: a schema over an object needs its elements"
    let cs := ws.map fun w => (s!"{c}_{w}", o)
    if let .error m := Schema.check cs then failAt s[6] m
    pure (.schema cs)
  -- each word named as a literal of its atom writes it (`wordText`), its code the word itself
  | ``sObjFrom => objDecl do
    let f ← path s[3]; let c ← wordOf s[4]
    let some (t, xs) := (← get).diskVals.lookup (f, c)
      | failAt s[3] s!"the column {c} of {f} was not read before the program (`Embed.diskOf`)"
    pure (.coded t (xs.map (wordText t)) (xs.map (·.toInt64.toInt)))
  | ``sPrint => pure (.print p (← expr s[1]) (← binds s[2]))
  | ``sCheck =>
    let proof := if s[5].getNumArgs == 0 then none else some s[5][1].getId
    pure (.check p (← expr s[1]) (← expr s[3]) (atomIn s[2] == "=") (← binds s[4]) proof)
  | ``sInput => do
    let n ← wordOf s[1]
    Parse.fresh p n (← get).taken
    pure (.input p n (← typeOf s[2]) (← csvSep s[4]) (← path s[5]))
  | ``sDict => do
    let n ← wordOf s[1]
    Parse.fresh p n (← get).taken
    pure (.dict p n (← typeOf s[2]))
  | ``sOutput => do pure (.output p (← wordOf s[1]) (← csvSep s[3]) (← path s[4]))
  | ``sDefn =>
    -- `_on_` is one Lean identifier: its text read as a head, `_n_` the infix `n`
    let (w, key) ← if s[0].getKind == ``wNeg then (do let w ← wordOf s[0]; pure (w, w)) else onText s[0] (tokText s[0][0]) do
      let w ← Parse.word
      if w != "_" then pure (w, w) else do
        let n ← Parse.word
        if (← Parse.peek) != some '_' then Parse.expected s!"'_' closing the infix operator `_{n}_`"
        Parse.adv; pure (n, Parse.infixKey n)
    defn s w key (opt s[1]) s[2] s[4] s[5] s[6]
  | ``sInfix => do let n ← wordOf s[1]; defn s n (Parse.infixKey n) s[4].getSepArgs s[6] s[8] s[9] s[10]
  | ``sTheorem => theoremDecl s p
  | _ => failAt s "expected a declaration"

/-- `schema S from "dir"` (F1): the schema `diskOf` read from `dir`, each column at the unbounded object of its atom,
    named by the atom (`obj f64 : f64`), declared here unless `ds`, the declarations before, declare it so. -/
def schemaFrom (s : Syntax) (ds : List Decl) : C (List Decl) := do
  let p ← posOf s
  let n ← wordOf s[1]
  if let some r := (← get).taken.lookup n then failAt s[1] s!"`{n}` is already defined {r}"
  let some f := s[3].isStrLit? | failAt s[3] "expected the path as a string literal"
  let some (_, cs, ts) := (← get).disk.find? (·.1 == f)
    | failAt s[3] s!"the schema of {f} was not read before the program (`Embed.diskOf`)"
  let objs ← ts.filterMapM fun t => do
    let a := atomName t
    if ds.any fun | .obj _ m (.num u) => m == a && u == t | _ => false then return none
    if let some r := (← get).taken.lookup a then
      failAt s[3] s!"a column of {f} is at the atom {a}, so at the object `obj {a} : {a}`; `{a}` is already defined {r} as another object"
    if (litLayout t).isNone then
      failAt s[3] s!"a column of {f} is at the atom {a}, and no object of {a} is declared: no literal of {a} is stored"
    return some (Decl.obj p a (.num t))
  if let .error m := Schema.check cs then failAt s[3] m
  return objs ++ [.obj p n (.schema cs)]

/-- The program of the statements `ss`, read in the scope `s₀`, each statement in the scope those before it leave
    (`Parse.after`); and the scope it leaves. -/
def program (fm : FileMap) (s₀ : Parse.S) (ss : Array Syntax) : Except Err (Program × Parse.S) :=
  (ss.toList.foldlM (init := []) (fun ds (x : Syntax) => do
    let es ← if x.getKind == ``sSchemaFrom then schemaFrom x ds else do pure [← stmt x]
    modify (Parse.after · es); pure (ds ++ es)) |>.run fm).run s₀

/-- The schemas the statements `ss` read (`schema S from "dir"`, F1), each read here, at elaboration, from its `.d`
    and files (`Table.readSchema`): the program is fixed by the data as it is now, and is elaborated again when the
    data changes. A path that is no literal is left to `schemaFrom`, which refuses it at its position. -/
def diskOf (ss : Array Syntax) (s₀ : Parse.S) : CommandElabM Parse.S := do
  let disk ← ss.toList.filterMapM fun s => do
    let some f := (if s.getKind == ``sSchemaFrom then s[3].isStrLit? else none) | return none
    match ← (Table.readSchema f).toBaseIO with
    | .error e => throwErrorAt s[3] "{e}"
    | .ok S => return some (f, S.map (fun (c, o) => (c, (oexpOf o).1)), (S.flatMap fun c => (oexpOf c.2).2).eraseDups)
  -- `obj V from "dir" c`: the column at the atom its `.d` names, its distinct words in the atom's order
  -- (`Kernel.ascOrd`, as `asc distinct` gives them); an atom with no literal has no element to name (`litLayout`)
  let diskVals ← ss.toList.filterMapM fun s => do
    let some f := (if s.getKind == ``sObjFrom then s[3].isStrLit? else none) | return none
    let c := s[4][0].getId.toString (escape := false)
    match ← (do
      let some (.atom t) ← Table.objOf? f c
        | throw (IO.userError s!"{f}: the column '{c}' is no atom column, and `obj V from` names the elements of one")
      let some ord := if (litLayout t).isSome then Kernel.ascOrd t else none
        | throw (IO.userError s!"obj V from {f} {c}: the column is at the atom {atomName t}, and no object of {atomName t} \
            is declared: no literal of {atomName t} is stored")
      let r ← Table.readVals (.atom t) f c
      let tb : Tab .long (.atom t) ← IO.ofExcept (Table.frame (B := .atom t) r.2.2)
      let ws ← tb.toList.mapM fun (kv : Obj.long.El × (Obj.atom t).El) => do
        let some w := elWord t kv.2 | throw (IO.userError s!"{f}: {c} holds an element of {atomName t} with no stored word")
        pure w
      pure (t, (ws.eraseDups.toArray.qsort (ord · < ord ·)).toList)).toBaseIO with
    | .error e => throwErrorAt s[3] "{e}"
    | .ok r => return some ((f, c), r)
  return { s₀ with disk, diskVals }

def defConst (n : Name) (v : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := n, levelParams := [], type := mkConst ``Program, value := v, hints := .abbrev, safety := .safe }

/-- The constant `c : Decl` of a declaration not built to a constant of its own (not yet elaborated once). -/
def declConst (c : Name) (d : Decl) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := c, levelParams := [], type := mkConst ``Decl, value := toExpr d, hints := .abbrev, safety := .safe }

/-- The scope of a program read here: the current namespace and `open`s. -/
def scopeHere : CommandElabM Parse.S := do
  let (res, ns) := resolverAt (← getEnv) (← getOptions) (Expand.relRegistry.getState (← getEnv)) (← getCurrNamespace) (← getOpenDecls)
  pure { cs := #[], res, ns, finExt := Expand.finOfConst (← getEnv) (← getOptions) }

/-- The programs the constants `used` reach, each after the programs its own names reach, in the order they were
    defined (an import's before the importer's). -/
def homesOf (reg : Expand.Registry) (used : List Name) : List Name :=
  let hs := used.filterMap fun c => (reg.exts[c]?).map (·.2)
  let all := hs.flatMap fun h => ((reg.chains.lookup h).getD []) ++ [h]
  (reg.progs.toList.map (·.1)).filter all.contains

/-- The object instantiation argument of a generic certificate. -/
def substTy : Lean.Expr := mkApp (mkConst ``List [0]) (mkConst ``Rel.Obj)

/-- The types and denotation of a built term at the caller's objects and valuation. -/
def termAt (ρ : Lean.Expr) (σ : Option Lean.Expr) (ph : List QAtomicType) (p : Pos) (side : String)
    (A B : Obj) (t : Tm A B) : TermElabM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let denName := `Rel.Lang.Tm.den
  let t ← ofExcept (Expand.tmE #[] t)
  let (a, b) := (Expand.oE A, Expand.oE B)
  let some σ := σ | return (a, b, mkAppN (mkConst denName) #[ρ, a, b, t])
  let ph := toExpr ph
  let inst := mkApp2 (mkConst ``Rel.Obj.inst) ph σ
  let (a', b') := (mkApp inst a, mkApp inst b)
  -- The instantiated term must exist with `σ` still arbitrary, including at any fixed nodes.
  let value ← Meta.whnf (mkAppN (mkConst ``Tm.instObj) #[ph, σ, a, b, t])
  let .app ok t := value | throwError "rel_program: {p}: cannot instantiate `{side}` at arbitrary objects"
  unless ok.isAppOfArity ``Except.ok 2 do
    throwError "rel_program: {p}: cannot instantiate `{side}` at arbitrary objects"
  pure (a', b', mkAppN (mkConst denName) #[ρ, a', b', t])

/-- `Tm.den ρ` of both sides, using `Tm.instObj` at the theorem's `σ` when it has object variables. -/
def sidesAt (ρ : Lean.Expr) (c : Expand.Chk) (σ : Option Lean.Expr) (ph : List QAtomicType) :
    TermElabM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let (p, l, r, _, _, _, ⟨A, B, R, S⟩) := c
  unless (← getEnv).contains `Rel.Lang.Tm.den do
    throwError "rel_program: a proved check requires importing Rel.Lang.Den"
  let (a, b, r') ← termAt ρ σ ph p l A B R
  let (_, _, s') ← termAt ρ σ ph p r A B S
  pure (a, b, r', s')

/-- The statement of an elaborated certificate, over the object substitution (if generic), the valuation of its
    parameters, and each premise. -/
def goalOf (c : Expand.Chk) (hs : List Expand.Chk := []) (ph : List QAtomicType := []) : TermElabM Lean.Expr := do
  let goal (σ : Option Lean.Expr) := Meta.withLocalDeclD `ρ (mkConst `Rel.Lang.Val) fun ρ => do
    let prop (c : Expand.Chk) : TermElabM Lean.Expr := do
      let (a, b, r, s) ← sidesAt ρ c σ ph
      let (_, _, _, eq, _, _, _) := c
      if eq then Meta.mkEq r s
      else pure (mkAppN (mkConst `Rel.Core.Rel.le [0, 0]) #[mkApp (mkConst ``Rel.Obj.El) a, mkApp (mkConst ``Rel.Obj.El) b, r, s])
    Meta.mkForallFVars #[ρ] (← hs.foldrM (fun h b => do pure (mkForall `h .default (← prop h) b)) (← prop c))
  if ph.isEmpty then goal none else
    Meta.withLocalDeclD `σ substTy fun σ => do Meta.mkForallFVars #[σ] (← goal (some σ))

/-- Use definitional equality first, then expose the denotation equations and evaluate typed variable lookups. -/
def calcMatch (proof ty : Lean.Expr) (subst : Bool) : MetaM (Option Lean.Expr) := do
  let proofTy ← Meta.inferType proof
  if ← Meta.isDefEq proofTy ty then return some proof
  unless subst && proofTy.getAppFn == ty.getAppFn do return none
  let mut rules : Meta.SimpTheorems := {}
  for d in [`Rel.Lang.Tm.den, `Rel.Lang.Tm.argDen, `Rel.Lang.Val.args] do
    rules ← rules.addDeclToUnfold d
  rules ← rules.addConst `Rel.Lang.Val.bind_apply
  rules ← rules.addConst `Rel.Lang.Val.bind_ne
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[rules])
  let discharge : Meta.Simp.Discharge := fun p => Meta.withTransparency .default do
    if let some (_, a, b) := p.eq? then
      -- The caller and the citation can express the same object with different substitutions.
      if ← Meta.isDefEq a b then return some (← Meta.mkEqRefl a)
      return none
    let q ← Meta.mkDecide p
    if (← Meta.whnf q).isConstOf ``Bool.true then some <$> Meta.mkDecideProof p else pure none
  let (a, _) ← Meta.simp proofTy ctx #[] (discharge? := some discharge)
  let (b, _) ← Meta.simp ty ctx #[] (discharge? := some discharge)
  unless ← Meta.isDefEq a.expr b.expr do return none
  let pr ← a.proof?.elim (pure proof) (Meta.mkEqMP · proof)
  return some (← b.proof?.elim (pure pr) (Meta.mkEqMPR · pr))

/-- A certified sibling at the call's valuation, with its object arguments inferred from the premise when needed. -/
def siblingProof (ρ : Lean.Expr) (σs : List Lean.Expr) (premise : Lean.Expr)
    (c : Name) (ph : List QAtomicType) (subst : Bool) : TermElabM (Option Lean.Expr) := do
  let pr := mkConst c
  if ph.isEmpty then return ← calcMatch (mkApp pr ρ) premise subst
  for σ in σs do
    if let some h ← calcMatch (mkApp2 pr σ ρ) premise subst then return some h
  Meta.withNewMCtxDepth do
    let os ← ph.mapM fun _ => Meta.mkFreshExprMVar (mkConst ``Rel.Obj)
    let σ ← Meta.mkListLit (mkConst ``Rel.Obj) os
    let some h ← calcMatch (mkApp2 pr σ ρ) premise subst | return none
    for (o, a) in os.zip ph do
      if let .mvar m ← instantiateMVars o then m.assign (Expand.oE (.atom a))
    let h ← instantiateMVars h
    return if h.hasMVar then none else some h

/-- The theorem `t` of the program `n` with steps `:= why` then `x` (`theorem t : e = f := calc …`) certified as the chain
    of its steps, `n.proof.t`: a `≜ m` step is `rfl` (the expander inlines definitions, so both sides elaborate to one
    `Tm`), a step citing a theorem is that theorem's own `….proof.m`, joined by `Eq.trans`.
    A citation can use the elaborated hypotheses and previously certified theorems. -/
def certifyCalc (n : Name) (thms : Expand.Thms) (p : Pos) (t : String) (eq : Bool)
    (steps : List (Pos × Bool × Expr × Why)) (siblings : List (Name × List QAtomicType)) :
    TermElabM (Option String) := do
  let env ← getEnv
  unless env.contains `Rel.Lang.Tm.den do
    return some s!"{t}: the program does not import Rel.Lang.Den"
  -- the proof constant of a cited theorem: `h.proof.m` for the constant `h.m` the registry gave it, else the program's own
  let cite : Why → Option Name
    | .unfold .. => none
    | .thm _ m c _ => match c with
      | some (.str h m') => some (.str (h ++ `proof) m')
      | _ => some (n ++ `proof ++ Name.mkSimple m)
  let why := fun (w : Why) => match w with | .thm _ m _ _ => m | .unfold _ m => m
  if !eq || steps.any (!·.2.1) then return some s!"{t}: the theorem has `⊑` steps"
  if let some (q, _, _, w) := steps.find? (fun (_, _, _, w) => (cite w).any (!env.contains ·)) then
    return some s!"{t}: step at {q}: no proof constant for {why w}"
  let some cert := thms.1.lookup p |
    return some s!"{t}: {(thms.2.lookup p).getD "its statement or a step does not type as a `check`"}"
  let goal ← goalOf cert.statement cert.premises cert.ph
  let generic := !cert.ph.isEmpty
  -- a step that does not hold is the reason the theorem is listed, never an error of the program
  let value : Except String Lean.Expr ← Meta.forallTelescope goal fun args _ => do
    let σ := if generic then args[0]? else none
    let arity := if generic then 2 else 1
    let some ρ := args[arity - 1]? | throwError "rel_program: theorem {t} has no valuation binder"
    let premises := args.extract arity args.size
    let mut acc : Option Lean.Expr := none
    for (q, _, _, w) in steps do
      let some l := cert.links.find? (·.sides.1 == q) | throwError "rel_program: no elaborated step at {q}"
      let (_, _, a, b) ← sidesAt ρ l.sides σ cert.ph
      let step ← match cite w with
        | none =>
          unless ← Meta.isDefEq a b do
            return .error s!"step at {q}: `≜ {why w}` unfolds a definition, but both sides are not one term: {← Meta.ppExpr a} and {← Meta.ppExpr b}"
          Meta.mkEqRefl a
        | some c =>
          let subst := !l.args.isEmpty
          let mut ρ' := ρ
          for (⟨A, B, x⟩, k) in l.args.zipIdx do
            let (a, b, den) ← termAt ρ σ cert.ph q s!"argument {k + 1} of {why w}" A B x
            ρ' := mkAppN (mkConst `Rel.Lang.Val.bind) #[ρ', toExpr k, a, b, den]
          let σ' ← if subst then do
            let os := l.objects.map fun (o, ph) => match o, σ with
              | some o, some σ => mkApp3 (mkConst ``Rel.Obj.inst) (toExpr cert.ph) σ (Expand.oE o)
              | some o, none => Expand.oE o
              | none, _ => Expand.oE (.atom ph)
            pure (some (← Meta.mkListLit (mkConst ``Rel.Obj) os))
          else pure σ
          let mut pr := mkConst c
          if let .forallE _ dom _ _ := (← Meta.inferType pr) then
            if dom == substTy then
              let some σ := σ' | return .error s!"step at {q}: {c} requires an object substitution"
              pr := mkApp pr σ
          pr := mkApp pr ρ'
          let mut ty ← Meta.inferType pr
          let objectLists := σ.toList ++ σ'.toList
          while true do
            let .forallE _ premise body _ := ty | break
            let h ← premises.toList.findSomeM? fun h => calcMatch h premise subst
            let h ← if h.isSome then pure h else
              siblings.findSomeM? (fun (c, ph) => siblingProof ρ objectLists premise c ph subst)
            let some h := h |
              return .error s!"step at {q}: {c} requires the premise {← Meta.ppExpr premise}, with no matching hypothesis or certified theorem"
            pr := mkApp pr h
            ty := body.instantiate1 h
          let expected ← Meta.mkEq a b
          let some proof ← calcMatch pr expected subst |
            return .error s!"step at {q}: {c} proves {← Meta.ppExpr (← Meta.inferType pr)}, not {← Meta.ppExpr expected}"
          pure proof
      acc ← match acc with | none => pure (some step) | some s => some <$> Meta.mkEqTrans s step
    let some chain := acc | throwError "rel_program: theorem {t} has no steps"
    pure (.ok (← Meta.mkLambdaFVars args chain))
  let value ← match value with | .ok v => pure v | .error e => return some s!"{t}: {e}"
  unless ← Meta.isDefEq (← Meta.inferType value) goal do
    return some s!"{t}: the chain at {p} proves {← Meta.ppExpr (← Meta.inferType value)}, not {← Meta.ppExpr goal}"
  addDecl (.thmDecl { name := n ++ `proof ++ Name.mkSimple t, levelParams := [], type := goal, value })
  pure none


/-- Check each named proof of `prog` (`check e = f by lemma`, `theorem t : e = f by lemma`) against the denotation of
    the typed terms that emission consumes (`checks`, `thms`, matched by position), as the statement `goalOf`:
    `n.proof.check<i>` for the `i`-th proved check, `n.proof.<t>` for the theorem `t`. A `calc` theorem is certified
    by `certifyCalc`; the ones it cannot are the strings of the constant `n.proof.unproved`. -/
def certify (n : Name) (prog : Program) (checks : List Expand.Chk)
    (thms : Expand.Thms) (prelude : List (Name × List QAtomicType)) : TermElabM Unit := do
  let mut index := 0
  let mut unproved : List String := []
  let mut siblings : List (Name × List QAtomicType) := []
  for decl in prog do
    let (p, proof, name) ← match decl with
      | .check p _ _ _ _ (some proof) =>
        index := index + 1
        pure (p, proof, Name.mkSimple s!"check{index - 1}")
      | .«theorem» p t _ _ _ _ _ _ _ (some proof) => pure (p, proof, Name.mkSimple t)
      | .«theorem» p t _ _ _ eq _ _ steps none =>
        if steps.isEmpty then continue
        if let some m ← certifyCalc n thms p t eq steps (siblings ++ prelude) then unproved := unproved ++ [m]
        else if let some cert := thms.1.lookup p then
          siblings := (n ++ `proof ++ Name.mkSimple t, cert.ph) :: siblings
        continue
      | _ => continue
    let cert ← match thms.1.lookup p with
      | some cert => pure cert
      | none =>
        let some c := checks.find? (·.1 == p) | throwError "rel_program: no elaborated check at {p}"
        let (_, _, _, _, source, target, _) := c
        pure ({ sig := { vars := [], params := [], source, target }, statement := c, premises := [], links := [] } :
          Expand.ThmChecks)
    let goal ← goalOf cert.statement cert.premises cert.ph
    let elabProof (ty : Lean.Expr) := Term.withoutErrToSorry do
      let value ← Term.elabTermEnsuringType (mkIdent proof) ty
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasSorry then
        throwError "rel_program: proof of {name} at {p} contains an unresolved goal"
      pure value
    let value ← if cert.ph.isEmpty then elabProof goal else
      -- A lemma can take the object list itself or infer its object arguments at a fixed `σ`.
      match ← observing? (elabProof goal) with
      | some v => pure v
      | none => Meta.forallBoundedTelescope goal (some 1) fun args ty => do
        Meta.mkLambdaFVars args (← elabProof ty)
    let c := n ++ `proof ++ name
    addDecl (.thmDecl { name := c, levelParams := [], type := goal, value })
    if let .«theorem» .. := decl then siblings := (c, cert.ph) :: siblings
  unless unproved.isEmpty do
    let ty := mkApp (mkConst ``List [0]) (mkConst ``String)
    addAndCompile <| .defnDecl
      { name := n ++ `proof ++ `unproved, levelParams := [], type := ty, value := toExpr unproved
        hints := .abbrev, safety := .safe }

/-- The program `n` named by `id`, read in the scope `s` that left `used`, what it reads (`Expand.emit`): each closed
    definition as the Lean definition `n.x`, its prints, its checks; then its definitions and objects registered,
    each a constant (`n.x : Decl`, its declaration, where it is not built once), with its scope and homes; the doc
    comment `stx[0]`, when written, is `n`'s. -/
def define (stx id : Syntax) (prog : Program) (used : List Name) (more : List Name := [])
    (scope : Option (Name × List OpenDecl) := none) : CommandElabM Unit := do
  let n := (← getCurrNamespace) ++ id.getId
  let (ns, os) := scope.getD (← getCurrNamespace, ← getOpenDecls)
  liftTermElabM do
    defConst n (toExpr (α := List Decl) prog)
    addDocString' n mkNullNode (stx[0].getOptional?.map (⟨·⟩))
    Term.addTermInfo' id (mkConst n) (isBinder := true)
  addDeclarationRangesFromSyntax n stx id
  let env ← getEnv
  let opts ← getOptions
  let reg := Expand.relRegistry.getState env
  -- `nil` starts at the `1` in scope (`Env.one`) though no token names it, so its home is read too
  let one := match (resolverAt env opts reg ns os).1 "1" with | .ext e => [e.const] | _ => []
  let homes := (reg.progs.toList.map (·.1)).filter ((more ++ homesOf reg (one ++ used)).contains ·)
  let progs ← homes.mapM fun m => return (m, ← programOf m)
  let resOf (h : Name) : String → Found :=
    if h == n then (resolverAt env opts reg ns os).1 else
    match reg.progs.find? (·.1 == h) with
    | some (_, ns, os) => (resolverAt env opts reg ns os).1
    | none => fun _ => .none
  let calls ← liftTermElabM reg.call?
  match ← liftTermElabM (Expand.read calls progs prog n resOf (thmSigs := (reg.thms.lookup ·))).run with
  | .error e => throwErrorAt stx "{e}"
  | .ok r =>
    let thms := r.2.2.2.1
    let prelude := reg.thms.filterMap fun (c, sig) =>
      match c with
      | .str home t => if home == `Rel.Programs.prelude then some ((home ++ `proof).str t, sig.vars.map (·.2)) else none
      | _ => none
    liftTermElabM (certify n prog r.2.2.1 thms prelude)
    liftTermElabM (Expand.emit n r)
    let objects := prog.filterMap fun | .obj _ o _ => some o | _ => none
    for d in prog do
      if let some (_, e) := Parse.extOf n d then
        unless (← getEnv).contains e.const do
          liftCoreM (declConst e.const d)
        modifyEnv (Expand.relRegistry.addEntry · (.ext e n))
      if let .«theorem» p t .. := d then
        if (← getEnv).contains (n ++ `proof ++ Name.mkSimple t) then
          if let some cert := thms.1.lookup p then
            modifyEnv (Expand.relRegistry.addEntry · (.thm (n.str t) (cert.sig.qualify n objects)))
    modifyEnv (Expand.relRegistry.addEntry · (.prog n ns os))
    modifyEnv (Expand.relRegistry.addEntry · (.chain n homes))

/-- `rel_program n where …`, read in the current namespace and `open`s (module design §2.3): no program is in
    scope that is not `open`ed or written qualified. -/
@[command_elab relProgram] def elabRelProgram : CommandElab := fun stx => do
  match program (← getFileMap) (← diskOf stx[4].getArgs (← scopeHere)) stx[4].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (prog, s) => define stx stx[2] prog s.used

/-- `rel_program n from base upto x where …`: the replacements read in `base`'s scope and objects. -/
@[command_elab relVariant] def elabRelVariant : CommandElab := fun stx => do
  let b ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[4])
  let base ← programOf b
  let reg := Expand.relRegistry.getState (← getEnv)
  let some (_, bns, bos) := reg.progs.find? (·.1 == b) | throwErrorAt stx[4] "`{b}` is no rel_program"
  let (res, ns) := resolverAt (← getEnv) (← getOptions) reg bns bos
  let s := Parse.after { cs := #[], res, ns } (base.filter fun | .obj .. => true | _ => false)
  let named : Decl → Option String := fun | .defn _ x .. => some x | _ => none
  match program (← getFileMap) (← diskOf stx[7].getArgs s) stx[7].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (news, s') => do
    for d in news do
      match named d with
      | some x => unless base.any (named · == some x) do throwErrorAt stx "`{x}` is no definition of `{b}`"
      | none => throwErrorAt stx "a variant only replaces definitions"
    let kept := base.filter fun | .check .. | .«theorem» .. => false | _ => true
    let kept ← if stx[5].getNumArgs == 0 then pure kept else do
      let x ← match (wordOf stx[5][1]).run (← getFileMap) |>.run' s with
        | .ok x => pure x
        | .error e => throwErrorAt stx[5] "{e}"
      match kept.findIdx? (named · == some x) with
      | some k => pure (kept.take (k + 1))
      | none => throwErrorAt stx[5] "`{x}` is no definition of `{b}`"
    define stx stx[2] (kept.map fun d => ((named d).bind fun x => news.find? (named · == some x)).getD d) s'.used
      ((reg.chains.lookup b).getD []) (some (bns, bos))

/-- `decl_line% c`: the line the declaration `c` is named at, so a test writes a position in `c`'s text as `c`'s line
    plus an offset, which holds wherever `c` moves in its file. -/
elab "decl_line% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some r ← findDeclarationRanges? n | throwErrorAt c "`{n}` has no declaration range to read its line from"
  pure (mkNatLit r.selectionRange.pos.line)

end Rel.Lang.Embed
