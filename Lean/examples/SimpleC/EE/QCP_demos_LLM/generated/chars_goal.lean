import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.chars_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance chars_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def chars_initialize_safety_wit_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Char |-> (m_pre))
  ** (charArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chars_initialize_safety_wit_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre (i + 1) ((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))))
  ** (charArray.undef_seg a_pre (i + 1) n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "m" ) )) # Char |-> (m_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def chars_initialize_entail_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (charArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (charArray.full a_pre (0 : Int) (repeat_Z (m_pre) ((0 : Int))))
  ** (charArray.undef_seg a_pre (0 : Int) n_pre)
) \/
(
forall (m_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((repeat_Z (m_pre) ((0 : Int))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def chars_initialize_entail_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((repeat_Z (m_pre) ((0 : Int))) = (@List.nil Int))

noncomputable def chars_initialize_entail_wit_2 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre (i + 1) ((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))))
  ** (charArray.undef_seg a_pre (i + 1) n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (charArray.full a_pre (i + 1) (repeat_Z (m_pre) ((i + 1))))
  ** (charArray.undef_seg a_pre (i + 1) n_pre)
) \/
(
forall (m_pre : Int) (n_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))) = (repeat_Z (m_pre) ((i + 1)))) ”
  &&  emp
)

noncomputable def chars_initialize_entail_wit_2_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))) = (repeat_Z (m_pre) ((i + 1))))

noncomputable def chars_initialize_return_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
  ** (charArray.undef_seg a_pre i n_pre)
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))
) \/
(
forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))
)

noncomputable def chars_initialize_return_wit_1_split_goal_spatial : Prop :=
  forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))

noncomputable def chars_initialize_partial_solve_wit_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
  ** (charArray.undef_seg a_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(CHAR)))) # Char |->_)
  ** (charArray.undef_seg a_pre (i + 1) n_pre)
  ** (charArray.full a_pre i (repeat_Z (m_pre) (i)))


structure VC_Correct : Type where
  proof_of_chars_initialize_safety_wit_1 : chars_initialize_safety_wit_1
  proof_of_chars_initialize_safety_wit_2 : chars_initialize_safety_wit_2
  proof_of_chars_initialize_partial_solve_wit_1 : chars_initialize_partial_solve_wit_1
  proof_of_chars_initialize_entail_wit_1 : chars_initialize_entail_wit_1
  proof_of_chars_initialize_entail_wit_2 : chars_initialize_entail_wit_2
  proof_of_chars_initialize_return_wit_1 : chars_initialize_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.chars_goal
