import Rel.RepStruct
import Rel.RepCanon
import Rel.RepTabComp
import Rel.Lang.Den

/-! The axioms of the `Rel.Rep*` laws a downstream proof leans on, pinned. `#print axioms` is refused in a `module`, and
`make axioms` covers `Rel.Core` only, so the pins live here, outside the modules they check (PLAN perf9e). -/

namespace Rel

/-- info: 'Rel.Tab.Holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tab.Holds
/-- info: 'Rel.Tab.zero_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.zero_holds
/-- info: 'Rel.Tab.idU_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.idU_holds
/-- info: 'Rel.Tab.top_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.top_holds
/-- info: 'Rel.Tab.top_val_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.top_val_holds
/-- info: 'Rel.Tab.outl_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.outl_holds
/-- info: 'Rel.Tab.outr_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.outr_holds
/-- info: 'Rel.Tab.pair_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.pair_holds
/-- info: 'Rel.Tab.inl_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.inl_holds
/-- info: 'Rel.Tab.inr_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.inr_holds
/-- info: 'Rel.Tab.inlConv_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.inlConv_holds
/-- info: 'Rel.Tab.inrConv_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.inrConv_holds
/-- info: 'Rel.Tab.flat_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.flat_holds
/-- info: 'Rel.Tab.canon_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.canon_holds
/-- info: 'Rel.Tab.ran_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.ran_holds
/-- info: 'Rel.Tab.conv_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.conv_holds
/-- info: 'Rel.Tab.comp_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tab.comp_holds
/-- info: 'Rel.Obj.lt_trichotomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Obj.lt_trichotomy
/-- info: 'Rel.Obj.lt_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Obj.lt_prod
/-- info: 'Rel.Obj.lt_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Obj.lt_cons
/-- info: 'Rel.Lang.Tm.den_pol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lang.Tm.den_pol
/-- info: 'Rel.Core.Rel.mu_fix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Core.Rel.mu_fix

end Rel
