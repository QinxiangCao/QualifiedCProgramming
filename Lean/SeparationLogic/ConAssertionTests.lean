import SimpleC.SL.ConAssertion

namespace ConAssertionTests

open AUXLib
open CompCert
open SimpleC.SL.Mem
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.ConAssertion
open scoped SimpleC.SL.SAC

#check STS
#check TokenSet
#check STS_state_transition
#check Lstate
#check Lstate_eq_split
#check TokenSet_join
#check valid_transtion
#check valid_Lstate
#check transtion_disjoint_preserved
#check transition_token_preserved
#check STS_state_join
#check state_join
#check valid_state_join
#check rely_closed
#check Closed_transition
#check keep_rely_closed
#check state_empty
#check empty_state
#check empty_state_is_empty
#check STS_def
#check CSL
#check CSL.canonical
#check naive_S
#check STS_naive

#check CSLImpl.Names
#check CSLImpl.DerivedNames
#check CSLImpl.PrimitiveRules
#check CSLImpl.Context
#check CSLImpl.mstore
#check CSLImpl.mstore_noninit
#check CSLImpl.mstore_mstore_noninit
#check CSLImpl.mstore_eqm
#check CSLImpl.dup_mstore_noninit
#check CSLImpl.at_states
#check CSLImpl.has_tokens

def NaiveCSL : CSL STS_naive := CSL.canonical STS_naive

local instance : SacContext := ⟨NaiveCSL.toSeparationLogicSig⟩

example (spec : STS_def) (logic : CSL spec) :
    logic.toSeparationLogicSig = CSLImpl.SeparationLogic spec := rfl

example (spec : STS_def) (logic : CSL spec) :
    logic.at_states = CSLImpl.at_states spec := rfl

example (spec : STS_def) (logic : CSL spec) :
    logic.has_tokens = CSLImpl.has_tokens spec := rfl

example {S : STS} (transition : STS_state_transition S)
    (hpreserved : transition_token_preserved transition)
    (s1 s2 : S.STS_state) (token1 token2 frame : TokenSet S)
    (htransition : transition (s1, token1) (s2, token2)) :
    TokenSet_join token1 (S.InvownedToken s1) frame ↔
      TokenSet_join token2 (S.InvownedToken s2) frame :=
  hpreserved s1 s2 token1 token2 frame htransition

example (state : Lstate naive_S) :
    NaiveCSL.join state (empty_state : Lstate naive_S) state := by
  exact ⟨mem_join_emp2 state.s_mem,
    ⟨Sets_equiv_symm (Sets_union_empty state.s_token),
      Sets_intersect_empty state.s_token⟩,
    Sets_equiv_symm (Sets_intersect_full state.s_STS)⟩

example : NaiveCSL.is_unit (empty_state : Lstate naive_S) :=
  empty_state_is_empty

def byteState (p value : Int) : Lstate naive_S where
  s_mem := single_byte_mem p value
  s_STS := Sets.full
  s_token := Sets.empty

example (p value : Int) : NaiveCSL.mstore p value (byteState p value) := by
  exact ⟨value, Byte.eqm_refl value, rfl, Sets_equiv_refl _, Sets_equiv_refl _⟩

example (p value : Int) : NaiveCSL.mstore p value |-- NaiveCSL.mstore_noninit p := by
  exact NaiveCSL.mstore_mstore_noninit p value

example (p value : Int) : NaiveCSL.mstore p value |-- EX stored, NaiveCSL.mstore p stored := by
  Exists value
  entailer!

example : NaiveCSL.at_states Sets.full (empty_state : Lstate naive_S) := by
  exact ⟨rfl, Sets_equiv_refl _, Sets_equiv_refl _⟩

example : NaiveCSL.has_tokens Sets.empty
    ({ s_mem := empty_mem
       s_STS := Sets.empty
       s_token := Sets.empty } : Lstate naive_S) := by
  exact ⟨rfl, Sets_equiv_refl _, Sets_equiv_refl _⟩

#print axioms SimpleC.SL.ConAssertion.Lstate_eq_split
#print axioms SimpleC.SL.ConAssertion.valid_state_join
#print axioms SimpleC.SL.ConAssertion.keep_rely_closed
#print axioms SimpleC.SL.ConAssertion.CSLImpl.PrimitiveRules
#print axioms SimpleC.SL.ConAssertion.CSLImpl.dup_mstore_noninit

end ConAssertionTests
