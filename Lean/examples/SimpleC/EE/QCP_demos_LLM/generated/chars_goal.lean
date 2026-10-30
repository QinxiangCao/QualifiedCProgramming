import SimpleC.SL.LeanPrinterPrelude


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
open scoped SimpleC.SL.SAC CoqZ

local instance chars_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def chars_initialize_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Char |-> (m_pre))
  ** (charArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def chars_initialize_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
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
forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
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
forall (n_pre : Int) (m_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((repeat_Z (m_pre) ((0 : Int))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def chars_initialize_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (m_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((repeat_Z (m_pre) ((0 : Int))) = (@List.nil Int))

noncomputable def chars_initialize_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
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
forall (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))) = (repeat_Z (m_pre) ((i + 1)))) ”
  &&  emp
)

noncomputable def chars_initialize_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (((repeat_Z (m_pre) (i)) ++ (m_pre :: (@List.nil Int))) = (repeat_Z (m_pre) ((i + 1))))

noncomputable def chars_initialize_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
  ** (charArray.undef_seg a_pre i n_pre)
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))
) \/
(
forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))
)

noncomputable def chars_initialize_return_wit_1_split_goal_spatial : Prop :=
  forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (charArray.full a_pre i (repeat_Z (m_pre) (i)))
|--
  (charArray.full a_pre n_pre (repeat_Z (m_pre) (n_pre)))

noncomputable def chars_initialize_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (m_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
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
