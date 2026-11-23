import Rel.Lang.TestNative

/-! The native recipes of `inits`, `tails`, `filter(p)` and `takewhile(p)` (`initsB`, `tailsB`, `filterB`, `takewhileB`):
    one program on literal tables, each definition's plan (`outputOf`, run by `Plan.run`) writing the own files
    `Db.ownFile` makes of the Lean value's columns, the check the `rel-native` gate makes on `out/key`, `out/val`. -/

namespace Rel.Lang.TestNativeP

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude in
rel_program natP where
    obj X = {A,B,C}
    obj N = 0…9
    xs : X ⟶ [N] ≜ {(A,3 1 2),(B,[]),(C,5 4)}
    ev : N ⟶ N ≜ {(2,2),(4,4),(5,5)}
    lt : N ⟶ N ≜ {(1,1),(3,3),(5,5),(4,4)}
    ini : X ⟶ [[N]] ≜ xs inits
    tal : X ⟶ [[N]] ≜ xs tails
    fil : X ⟶ [N] ≜ xs filter(ev)
    tkw : X ⟶ [N] ≜ xs takewhile(lt)

/-- The plan of `name`'s output, run, writes the own files of the Lean value `R` (`Tab.conv`-free: key and value as
    they are), column for column; a refusal of the plan or a difference throws. -/
def check {A B : Obj} (name : String) (R : Except String (Tab A B)) : Lean.Meta.MetaM Unit := do
  let p ← match (← outputOf ``natP name ("out/" ++ name)) >>= Bld.plan with
    | .ok p => pure p | .error e => throwError "{name}: {e}"
  let (_, ws) ← match p.run abiOf with | .ok r => pure r | .error e => throwError "{name}: {e}"
  let x ← match R with | .ok x => pure x | .error e => throwError "{name}: {e}"
  let side (s : String) (cs : List (String × SideCol)) := cs.map fun (p, v) => ("out/" ++ name ++ "/" ++ s ++ p, v)
  let want ← match (side "key" (cols _ x.key "") ++ side "val" (cols _ x.val "")).filterMapM
      (fun (p, v) => do pure ((← ownFile p v).map fun f => (p, f))) with | .ok w => pure w | .error e => throwError "{name}: {e}"
  let got := ws.toList.filterMap fun (_, vs) => match vs.toList with
    | .str p :: c :: k :: n :: ps :: _ => (p, ·) <$> Reg.get? (α := Db.OwnFile) (.ctor 0 #[ps] #[c, k, n])
    | _ => none
  let flat (pf : String × Db.OwnFile) :=
    (pf.1, pf.2.code, pf.2.kind, pf.2.count.toNat, pf.2.parts.toList.map (·.toList))
  unless got.length == ws.size && got.map flat == want.map flat do
    throwError "{name}: the plan writes {got.length} of {ws.size} columns, not those of its Lean value\n{(got.zip want).map fun (g, w) => (g.1, w.1, (flat g).2.1 == (flat w).2.1, (flat g).2.2.1 == (flat w).2.2.1, (flat g).2.2.2.1, (flat w).2.2.2.1, (flat g).2.2.2.2 == (flat w).2.2.2.2)}"

#eval show Lean.Meta.MetaM Unit from do
  check "ini" natP.ini; check "tal" natP.tal; check "fil" natP.fil; check "tkw" natP.tkw

end Rel.Lang.TestNativeP
