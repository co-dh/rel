module

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Kernel.Need` the Rel kernels reach; `Rel.Kernel.Need` imports it. -/


namespace Rel.Kernel

/-- Model: the fallback value. C: prints `msg ()` to stderr and exits 1; it never returns.
`never_extract`, as core's `panicCore`: without it a call on closed arguments is hoisted into module
initialisation and stops the program at start-up, whichever branch it takes at run time. -/
@[never_extract, extern "qlean_stop"]
def stop {α : Type} (msg : Unit → String) (model : Unit → α) : α := model ()

/-- The one assert: `k` with the proof where `p` holds, `stop` where it does not. -/
@[macro_inline] def need {α : Type} (p : Prop) [Decidable p] (msg : Unit → String) (model : Unit → α)
    (k : p → α) : α :=
  if h : p then k h else stop msg model

/-- A count Lean states in `Nat` — an `Array`'s or `ByteArray`'s size, a `List`'s length — entering
as the `USize` it is under the fits check, so the one `toUSize` on a count is here. -/
@[macro_inline] def needSize {α : Type} (c : Nat) (what : String) (model : Unit → α) (k : USize → α) : α :=
  need (c < USize.size) (fun _ => s!"{what}: {c} does not fit a USize") model fun _ => k c.toUSize

end Rel.Kernel
