import Rel.Programs.Prelude
import Rel.Lang.EmitC

/-! Stage 1 of `doc/dataframe-design.zh.typ` (§6): a two-column frame filtered, grouped by its key and summed per
    group, `out ≜ filter(dom(π₂ big)) ≫ Λ(groups(π₁)) ≫ F(𝟙 × (F(π₂) ≫ sum))`.

    - `frameSpec` is the program as the design writes it: `groups(k) = ⟨∋ k, 𝟙⟩ ≫ ⟨π₁, selᴷ(k)⟩` with
      `selᴷ(k) = strₗ ≫ filter(cor(k°)) ≫ F(π₂)`. The language has no `strₗ` (not in `prims`, and the fold that
      carries the key, `foldI`, is a gap), so it is refused.
    - `frame` is the nearest spelling the language has: `sel`, the sub-list of each key, is a left fold whose carrier
      holds the key, seeded once per key of `K` (`⟨⊤(1,K), nil⟩`), and `groups` keeps the keys that occur. -/

namespace Rel.Lang.TestFrame

/-- error: line 23, col 36: unknown name 'str' -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program frameSpec where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(>{(2,∗)})
    sel(k : γ ⟶ K) : K×[γ] ⟶ [γ] ≜ strₗ filter(cor(k°)) F(π₂)
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) Λ(⟨∋π₁, 𝟙⟩⟨π₁, sel(π₁)⟩) F(𝟙 × (F(π₂) sum))

-- `filter` reaches the term as the prelude's fold (`prims` keeps its row only as the run form of that definition)
open Rel.Programs.prelude in
rel_program frame where
    obj K = {A,B,C}
    obj N = 0…40
    x : 1 ⟶ [K×N] ≜ {(∗,(B,5) (A,3) (B,5) (C,1) (A,7) (C,2) (B,1) (A,3))}
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    eqK : (K×[K×N])×(K×N) ⟶ (K×[K×N])×(K×N) ≜ dom(⟨π₁π₁,π₂π₁⟩ dom(π₁ ∩ π₂))
    sel : [K×N] ⟶ K×[K×N] ≜ ⦇[⟨⊤(1,K),nil⟩, (eqK ⟨π₁π₁, ⟨π₁π₂,π₂⟩snoc⟩) ∪ ((𝟙 − eqK)π₁)]⦈
    groups : [K×N] ⟶ K×[K×N] ≜ ⟨∋π₁, sel⟩ dom(⟨π₁,π₂π₁⟩ dom(π₁ ∩ π₂)) π₂
    out : 1 ⟶ [K×N] ≜ x filter(dom(π₂ big)) Λ(groups) F(𝟙 × (F(π₂) sum))
    print 𝟙(1,1) out

-- by hand: `big` keeps (B,5) (A,3) (B,5) (A,7) (A,3); A sums 3+7+3, B 5+5, C has no row; keys ascending. The
-- duplicate rows count twice: a frame is a list, not the set of its rows.
#guard frame.ok && frame.prints == ["𝟙(1, 1) out = {(∗, (A, 13) (B, 10))}"]

open Rel.Lang Tab in
partial def sh : {A B : Obj} → {d : Bool} → Tm A B d → String
  | _, _, _, .val _ => "val" | _, _, _, .comp R S => s!"({sh R} ≫ {sh S})" | _, _, _, .conv R => s!"{sh R}°"
  | _, _, _, .share k R => s!"share{k}[{sh R}]" | _, _, _, .prim r => r.sym | _, _, _, .arg f x => s!"{sh f}<{sh x}>"
  | _, _, _, .lam R => s!"Λ({sh R})" | _, _, _, .dom R => s!"dom({sh R})" | _, _, _, .outl => "π₁" | _, _, _, .outr => "π₂"
  | _, _, _, .id => "𝟙" | _, _, _, .prod R S => s!"({sh R} × {sh S})" | _, _, _, .pair R S => s!"⟨{sh R},{sh S}⟩"
  | _, _, _, .fold e S => s!"fold[{sh e},{sh S}]" | _, _, _, .lt U => s!"lt[{sh U}]" | _, _, _, .leq U => s!"leq[{sh U}]"
  | _, _, _, .meet R S => s!"({sh R} ∩ {sh S})" | _, _, _, .join R S => s!"({sh R} ∪ {sh S})" | _, _, _, .diff R S => s!"({sh R} − {sh S})"
  | _, _, _, .uni _ => "uni" | _, _, _, .call d c _ _ => s!"call{d}:{c}" | _, _, _, .arith k _ => s!"arith{k}" | _, _, _, .top V => s!"⊤[{sh V}]"
  | _, _, _, .E R => s!"E({sh R})" | _, _, _, .ran R => s!"ran({sh R})" | _, _, _, .nil => "nil" | _, _, _, _ => "?"

open Rel.Lang Tab in
#eval show Lean.Meta.MetaM Unit from do
  let r ← (Expand.read (fun _ => none) [(`prelude, Rel.Programs.prelude)] frame).run
  match r with
  | .ok (ds, _) => for (n, ⟨_, _, _, t⟩) in ds do if n == "out" then IO.println s!"{n}: {sh t}"
  | .error e => throwError s!"{repr e}"

open Rel.Lang Tab in
#eval (Plan.cols _ frame.x.rel.val "").map fun (p, v) =>
  (p, (Db.ownFile v).map fun (f : Db.OwnFile) => (f.code, f.kind, f.count, f.parts.map fun (b : ByteArray) => b.data))
open Rel.Lang Tab in
#eval (Plan.cols _ frame.out.rel.val "").map fun (p, v) =>
  (p, (Db.ownFile v).map fun (f : Db.OwnFile) => (f.code, f.kind, f.count, f.parts.map fun (b : ByteArray) => b.data))

end Rel.Lang.TestFrame
