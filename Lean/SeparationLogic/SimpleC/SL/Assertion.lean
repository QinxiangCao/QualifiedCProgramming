import SimpleC.SL.CommonAssertion

namespace SimpleC.SL.Assertion

open CompCert
open SimpleC.SL.Mem
open SimpleC.SL.CommonAssertion
open Unifysl.LogicGenerator.demo932

def Names : LanguageSig.{0} where
  model := mem
  join := mem_join
  is_unit := mem_empty

def DerivedNames : DerivedNamesSig Names := {}

def PrimitiveRules : PrimitiveRuleSig Names DerivedNames where
  unit_join := by
    intro state
    exact ⟨empty_mem, empty_mem_empty, mem_join_emp2 state⟩
  unit_spec := by
    intro state result unit hunit hjoin
    have hunit' := mem_empty_IS_empty_mem' unit hunit
    subst unit
    exact (mem_join_emp_r state result hjoin).symm
  join_comm := by
    intro left right result hjoin
    exact mem_join_comm hjoin
  join_assoc := by
    intro left middle right leftMiddle result hLeftMiddle hResult
    exact mem_join_assoc2 hLeftMiddle hResult

def Context : Facade.Context.{0, 0} where
  Names := Names
  DerivedNames := DerivedNames
  Rules := PrimitiveRules

def mstore (p : addr) (v : Int) : Context.expr :=
  fun state => exists v', Byte.eqm v v' ∧ state = single_byte_mem p v'

def mstore_noninit (p : addr) : Context.expr :=
  fun state =>
    state = single_Noninit_mem p ∨ exists v, state = single_byte_mem p v

theorem mstore_mstore_noninit
    (p : addr) (v : Int) (state : mem)
    (hstore : mstore p v state) : mstore_noninit p state := by
  rcases hstore with ⟨v', _, rfl⟩
  exact Or.inr ⟨v', rfl⟩

theorem mstore_eqm
    (p : addr) (v v' : Int) (heqm : Byte.eqm v v') :
    Context.derivable1 (mstore p v) (mstore p v') := by
  intro state hstore
  rcases hstore with ⟨stored, hv, hstate⟩
  exact ⟨stored, Byte.eqm_trans _ _ _ (Byte.eqm_sym _ _ heqm) hv, hstate⟩

theorem dup_mstore_noninit (p : addr) :
    Context.derivable1
      (Context.sepcon (mstore_noninit p) (mstore_noninit p))
      (Context.coq_prop False) := by
  intro state hsep
  rcases hsep with ⟨left, right, hjoin, hleft, hright⟩
  have hrightNonempty : right p ≠ Noperm := by
    rcases hright with hright | ⟨rightValue, hright⟩
    · rw [hright]
      simp [single_Noninit_mem, addr_eqb]
    · rw [hright]
      simp [single_byte_mem, addr_eqb]
  rcases hleft with hleft | ⟨leftValue, hleft⟩
  · have hat : left p = Noninit := by
      rw [hleft]
      simp [single_Noninit_mem, addr_eqb]
    exact hrightNonempty (mem_join_Some1 left right state p hjoin hat).1
  · have hat : left p = value leftValue := by
      rw [hleft]
      simp [single_byte_mem, addr_eqb]
    exact hrightNonempty (mem_join_Some3 left right state p leftValue hjoin hat).1

def SL : SeparationLogicSig where
  toContext := Context
  mstore := mstore
  mstore_noninit := mstore_noninit
  mstore_mstore_noninit := mstore_mstore_noninit
  mstore_eqm := mstore_eqm
  dup_mstore_noninit := dup_mstore_noninit

end SimpleC.SL.Assertion
