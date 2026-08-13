import SimpleC.SL.Assertion

namespace AssertionTests

open CompCert
open SimpleC.SL.Mem
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Assertion
open scoped SimpleC.SL.SAC

local instance : SacContext := ⟨SL⟩

#check Names
#check DerivedNames
#check PrimitiveRules
#check Context
#check SL
#check SL.model
#check SL.mstore
#check SL.mstore_noninit
#check SL.mstore_mstore_noninit
#check SL.mstore_eqm
#check SL.dup_mstore_noninit

example (state : mem) : SL.is_unit state ↔ mem_empty state := Iff.rfl

example (state : mem) : SL.join state empty_mem state :=
  mem_join_emp2 state

example (p value : Int) : SL.mstore p value (single_byte_mem p value) := by
  exact ⟨value, Byte.eqm_refl value, rfl⟩

example (p value : Int) : SL.mstore p value |-- SL.mstore_noninit p := by
  exact SL.mstore_mstore_noninit p value

example (p value : Int) : SL.mstore p value |-- SL.mstore_noninit p := by
  pre_process
  exact SL.mstore_mstore_noninit p value

example (p value : Int) : SL.mstore p value |-- EX stored, SL.mstore p stored := by
  Exists value
  entailer!

#print axioms SimpleC.SL.Assertion.PrimitiveRules
#print axioms SimpleC.SL.Assertion.mstore_eqm
#print axioms SimpleC.SL.Assertion.dup_mstore_noninit

end AssertionTests
