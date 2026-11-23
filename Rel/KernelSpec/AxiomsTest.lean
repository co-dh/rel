import Rel.KernelSpec.Asc
import Rel.KernelSpec.Assign
import Rel.KernelSpec.BinWin
import Rel.KernelSpec.Codes
import Rel.KernelSpec.Distinct
import Rel.KernelSpec.Elementwise
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.EwEnc
import Rel.KernelSpec.Gather
import Rel.KernelSpec.Grade
import Rel.KernelSpec.Group
import Rel.KernelSpec.Scan
import Rel.KernelSpec.Structural
import Rel.KernelSpec.SymFind

/-! The axioms of the `Rel.KernelSpec` lemmas a downstream proof leans on, pinned. `#print axioms` is refused in a
`module`, and `make axioms` covers `Rel.Core` only (the rest may use `Classical`), so the pins live here, outside the
modules they check. -/

/-- info: 'Rel.Verify.asc_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.asc_perm
/-- info: 'Rel.Verify.kasc_pos_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.kasc_pos_first
/-- info: 'Rel.Verify.kasc_pos_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.kasc_pos_key

/-- info: 'Rel.Verify.resAt_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.resAt_field
/-- info: 'Rel.Verify.set_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.set_field
/-- info: 'Rel.Verify.set!_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms Rel.Verify.set!_getElem?

/-- info: 'Rel.Verify.binBytes_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.binBytes_last

/-- info: 'Rel.Verify.groupOf_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.groupOf_iff
/-- info: 'Rel.Verify.lt_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.lt_idWidthOf

/-- info: 'Rel.Verify.elemsW_foldl_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.elemsW_foldl_mod
/-- info: 'Rel.Verify.elemsW_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.elemsW_foldl

/-- info: 'Rel.Verify.cmp_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.cmp_bitAt
/-- info: 'Rel.Verify.packOf_bitAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.packOf_bitAt
/-- info: 'Rel.Verify.Ew.bit_bitAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.Ew.bit_bitAt

/-- info: 'Rel.Verify.idAt_packIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.idAt_packIds

/-- info: 'Rel.Verify.elemsW_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.elemsW_decode_encode
/-- info: 'Rel.Verify.width_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms Rel.Verify.width_bounds
/-- info: 'Rel.Verify.toUSize_toNat_of_le8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.toUSize_toNat_of_le8
/-- info: 'Rel.Verify.eq_of_ite_some' does not depend on any axioms -/
#guard_msgs in #print axioms Rel.Verify.eq_of_ite_some
/-- info: 'Rel.Verify.eq_of_ite_none' does not depend on any axioms -/
#guard_msgs in #print axioms Rel.Verify.eq_of_ite_none
/-- info: 'Rel.Verify.decode_of_encode8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.decode_of_encode8

/-- info: 'Rel.Verify.elemsW_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.elemsW_decode
/-- info: 'Rel.Verify.elemsW_bytesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.elemsW_bytesOf
/-- info: 'Rel.Verify.byteOf_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.byteOf_bit
/-- info: 'Rel.Verify.bitAt_packOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.bitAt_packOf

/-- info: 'Rel.Verify.merge_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.merge_congr
/-- info: 'Rel.Verify.pairwise_lex_mergeSort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.pairwise_lex_mergeSort
/-- info: 'Rel.Verify.range_mergeSort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.range_mergeSort

/-- info: 'Rel.Verify.groupOf_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.groupOf_eq_iff
/-- info: 'Rel.Verify.rows_groupOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.rows_groupOf
/-- info: 'Rel.Verify.groups_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.groups_congr
/-- info: 'Rel.Verify.idsCap_packIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.idsCap_packIds
/-- info: 'Rel.Verify.ids_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.ids_get

/-- info: 'Rel.Kernel.raw_kscan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rel.Kernel.raw_kscan

/-- info: 'Rel.Verify.idAt_packIds_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.idAt_packIds_idWidthOf
