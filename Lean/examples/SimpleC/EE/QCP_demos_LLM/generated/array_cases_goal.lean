import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.array_cases_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance array_cases_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def arr_sum_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # UInt |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (uintArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # UInt |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (uintArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_3 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (uintArray.full a_pre n_pre l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "ret" ) )) # UInt |-> ((unsigned_last_nbits ((ret + (Znth i l (0 : Int)))) (32))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (uintArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (uintArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (uintArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((unsigned_last_nbits ((ret + (Znth i_2 l (0 : Int)))) (32)) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (uintArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((ret + (Znth i_2 l (0 : Int)))) (32)) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  emp
)

noncomputable def arr_sum_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((unsigned_last_nbits ((ret + (Znth i_2 l (0 : Int)))) (32)) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (uintArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (uintArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (uintArray.full a_pre n_pre l)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(UINT)))) # UInt |-> ((Znth i_2 l (0 : Int))))
  ** (uintArray.missing_i a_pre i_2 (0 : Int) n_pre l)

noncomputable def array_copy1_safety_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "dest" ) )) # Ptr |-> (dest_pre))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_full dest_pre n_pre)
  ** (intArray.full src_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_copy1_safety_wit_2 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) (i + 1) ((sublist ((0 : Int)) (i) (l)) ++ ((Znth i l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "dest" ) )) # Ptr |-> (dest_pre))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_copy1_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.undef_full dest_pre n_pre)
  ** (intArray.full src_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg dest_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) (l)))
  ** (intArray.undef_seg dest_pre (0 : Int) n_pre)
  ** (intArray.full src_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) (l)) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def array_copy1_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((sublist ((0 : Int)) ((0 : Int)) (l)) = (@List.nil Int))

noncomputable def array_copy1_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) (i + 1) ((sublist ((0 : Int)) (i) (l)) ++ ((Znth i l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre l)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg dest_pre (0 : Int) (i + 1) (sublist ((0 : Int)) ((i + 1)) (l)))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (i) (l)) ++ ((Znth i l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (l))) ”
  &&  emp
)

noncomputable def array_copy1_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (((sublist ((0 : Int)) (i) (l)) ++ ((Znth i l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (l)))

noncomputable def array_copy1_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
  ** (intArray.undef_seg dest_pre i n_pre)
  ** (intArray.full src_pre n_pre l)
|--
  (intArray.full dest_pre n_pre l)
  ** (intArray.full src_pre n_pre l)
) \/
(
forall (n_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
|--
  (intArray.full dest_pre n_pre l)
)

noncomputable def array_copy1_return_wit_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
|--
  (intArray.full dest_pre n_pre l)

noncomputable def array_copy1_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
  ** (intArray.undef_seg dest_pre i n_pre)
  ** (intArray.full src_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i src_pre i (0 : Int) n_pre l)
  ** (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
  ** (intArray.undef_seg dest_pre i n_pre)

noncomputable def array_copy1_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full src_pre n_pre l)
  ** (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))
  ** (intArray.undef_seg dest_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((dest_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre l)
  ** (intArray.seg dest_pre (0 : Int) i (sublist ((0 : Int)) (i) (l)))

noncomputable def array_concat_safety_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
  ** (intArray.undef_full ret_pre (n_pre + m_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_concat_safety_wit_2 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (i + 1) ((sublist ((0 : Int)) (i) (l1)) ++ ((Znth i l1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full b_pre m_pre l2)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_concat_safety_wit_3 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_concat_safety_wit_4 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ ((n_pre + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + i)) ”

noncomputable def array_concat_safety_wit_5 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) ((n_pre + i) + 1) ((l1 ++ (sublist ((0 : Int)) (i) (l2))) ++ ((Znth i l2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full b_pre m_pre l2)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full a_pre n_pre l1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_concat_entail_wit_1 : Prop :=
  (
forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
  ** (intArray.undef_full ret_pre (n_pre + m_pre))
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg ret_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) (l1)))
  ** (intArray.undef_seg ret_pre (0 : Int) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) (l1)) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def array_concat_entail_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  ((sublist ((0 : Int)) ((0 : Int)) (l1)) = (@List.nil Int))

noncomputable def array_concat_entail_wit_2 : Prop :=
  (
forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (i + 1) ((sublist ((0 : Int)) (i) (l1)) ++ ((Znth i l1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg ret_pre (0 : Int) (i + 1) (sublist ((0 : Int)) ((i + 1)) (l1)))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (i) (l1)) ++ ((Znth i l1 (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (l1))) ”
  &&  emp
)

noncomputable def array_concat_entail_wit_2_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (((sublist ((0 : Int)) (i) (l1)) ++ ((Znth i l1 (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (l1)))

noncomputable def array_concat_entail_wit_3 : Prop :=
  (
forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg ret_pre (0 : Int) (n_pre + (0 : Int)) (l1 ++ (sublist ((0 : Int)) ((0 : Int)) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + (0 : Int)) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
) \/
(
forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
|--
  (intArray.seg ret_pre (0 : Int) (n_pre + (0 : Int)) (l1 ++ (sublist ((0 : Int)) ((0 : Int)) (l2))))
)

noncomputable def array_concat_entail_wit_3_split_goal_spatial : Prop :=
  forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
|--
  (intArray.seg ret_pre (0 : Int) (n_pre + (0 : Int)) (l1 ++ (sublist ((0 : Int)) ((0 : Int)) (l2))))

noncomputable def array_concat_entail_wit_4 : Prop :=
  (
forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) ((n_pre + i) + 1) ((l1 ++ (sublist ((0 : Int)) (i) (l2))) ++ ((Znth i l2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full b_pre m_pre l2)
  ** (intArray.full a_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg ret_pre (0 : Int) (n_pre + (i + 1)) (l1 ++ (sublist ((0 : Int)) ((i + 1)) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + (i + 1)) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
) \/
(
forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) ((n_pre + i) + 1) ((l1 ++ (sublist ((0 : Int)) (i) (l2))) ++ ((Znth i l2 (0 : Int)) :: (@List.nil Int))))
|--
  (intArray.seg ret_pre (0 : Int) (n_pre + (i + 1)) (l1 ++ (sublist ((0 : Int)) ((i + 1)) (l2))))
)

noncomputable def array_concat_entail_wit_4_split_goal_spatial : Prop :=
  forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) ((n_pre + i) + 1) ((l1 ++ (sublist ((0 : Int)) (i) (l2))) ++ ((Znth i l2 (0 : Int)) :: (@List.nil Int))))
|--
  (intArray.seg ret_pre (0 : Int) (n_pre + (i + 1)) (l1 ++ (sublist ((0 : Int)) ((i + 1)) (l2))))

noncomputable def array_concat_return_wit_1 : Prop :=
  (
forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
  ** (intArray.full ret_pre (n_pre + m_pre) (l1 ++ l2))
) \/
(
forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
|--
  (intArray.full ret_pre (n_pre + m_pre) (l1 ++ l2))
)

noncomputable def array_concat_return_wit_1_split_goal_spatial : Prop :=
  forall (m_pre : Int) (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
|--
  (intArray.full ret_pre (n_pre + m_pre) (l1 ++ l2))

noncomputable def array_concat_partial_solve_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l1 (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre l1)
  ** (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full b_pre m_pre l2)

noncomputable def array_concat_partial_solve_wit_2 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full a_pre n_pre l1)
  ** (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full b_pre m_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.seg ret_pre (0 : Int) i (sublist ((0 : Int)) (i) (l1)))
  ** (intArray.full b_pre m_pre l2)

noncomputable def array_concat_partial_solve_wit_3 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre m_pre l2)
|--
  “ (i < m_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l2 (0 : Int))))
  ** (intArray.missing_i b_pre i (0 : Int) m_pre l2)
  ** (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)

noncomputable def array_concat_partial_solve_wit_4 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full b_pre m_pre l2)
  ** (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full a_pre n_pre l1)
|--
  “ (i < m_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((ret_pre + ((n_pre + i) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full b_pre m_pre l2)
  ** (intArray.seg ret_pre (0 : Int) (n_pre + i) (l1 ++ (sublist ((0 : Int)) (i) (l2))))
  ** (intArray.full a_pre n_pre l1)

noncomputable def array_swap_safety_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre n_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_swap_safety_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full b_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) (0 : Int))) (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))))
  ** (intArray.full a_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_swap_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full a_pre n_pre l1)
  ** (intArray.full b_pre n_pre l2)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (intArray.full a_pre n_pre ((sublist ((0 : Int)) ((0 : Int)) (l2)) ++ (sublist ((0 : Int)) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) ((0 : Int)) (l1)) ++ (sublist ((0 : Int)) (n_pre) (l2))))
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ (l1 = ((sublist ((0 : Int)) ((0 : Int)) (l2)) ++ (sublist ((0 : Int)) (n_pre) (l1)))) ” &&
  “ (l2 = ((sublist ((0 : Int)) ((0 : Int)) (l1)) ++ (sublist ((0 : Int)) (n_pre) (l2)))) ”
  &&  emp
)

noncomputable def array_swap_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (l1 = ((sublist ((0 : Int)) ((0 : Int)) (l2)) ++ (sublist ((0 : Int)) (n_pre) (l1))))

noncomputable def array_swap_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (l2 = ((sublist ((0 : Int)) ((0 : Int)) (l1)) ++ (sublist ((0 : Int)) (n_pre) (l2))))

noncomputable def array_swap_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full b_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) (0 : Int))) (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))))
  ** (intArray.full a_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))))
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (intArray.full a_pre n_pre ((sublist ((0 : Int)) ((i + 1)) (l2)) ++ (sublist ((i + 1)) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) ((i + 1)) (l1)) ++ (sublist ((i + 1)) (n_pre) (l2))))
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ ((replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) (0 : Int))) (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))) = ((sublist ((0 : Int)) ((i + 1)) (l1)) ++ (sublist ((i + 1)) (n_pre) (l2)))) ” &&
  “ ((replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))) = ((sublist ((0 : Int)) ((i + 1)) (l2)) ++ (sublist ((i + 1)) (n_pre) (l1)))) ”
  &&  emp
)

noncomputable def array_swap_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) (0 : Int))) (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))) = ((sublist ((0 : Int)) ((i + 1)) (l1)) ++ (sublist ((i + 1)) (n_pre) (l2))))

noncomputable def array_swap_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))) = ((sublist ((0 : Int)) ((i + 1)) (l2)) ++ (sublist ((i + 1)) (n_pre) (l1))))

noncomputable def array_swap_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full a_pre n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
|--
  (intArray.full a_pre n_pre l2)
  ** (intArray.full b_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) = l2) ” &&
  “ (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) = l1) ”
  &&  emp
)

noncomputable def array_swap_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) = l2)

noncomputable def array_swap_return_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) = l1)

noncomputable def array_swap_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full a_pre n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))) (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))

noncomputable def array_swap_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full a_pre n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |-> ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))))
  ** (intArray.missing_i b_pre i (0 : Int) n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
  ** (intArray.full a_pre n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))

noncomputable def array_swap_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
  ** (intArray.full a_pre n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i (0 : Int) n_pre ((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))

noncomputable def array_swap_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))))
  ** (intArray.full b_pre n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l1)) = n_pre) ” &&
  “ ((Zlength (l2)) = n_pre) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i b_pre i (0 : Int) n_pre ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))))
  ** (intArray.full a_pre n_pre (replace_Znth (i) ((Znth i ((sublist ((0 : Int)) (i) (l1)) ++ (sublist (i) (n_pre) (l2))) (0 : Int))) (((sublist ((0 : Int)) (i) (l2)) ++ (sublist (i) (n_pre) (l1))))))

noncomputable def array_vector_sum_safety_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.undef_full ret_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_vector_sum_safety_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg ret_pre (0 : Int) (i + 1) (l3 ++ (((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))) :: (@List.nil Int))))
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_vector_sum_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.undef_full ret_pre n_pre)
|--
  EX l3 : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ”
  &&  (uintArray.seg ret_pre (0 : Int) (0 : Int) l3)
  ** (uintArray.undef_seg ret_pre (0 : Int) n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 (@List.nil Int) (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def array_vector_sum_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 (@List.nil Int) (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))

noncomputable def array_vector_sum_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))

noncomputable def array_vector_sum_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))

noncomputable def array_vector_sum_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def array_vector_sum_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg ret_pre (0 : Int) (i + 1) (l3_2 ++ (((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))) :: (@List.nil Int))))
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
|--
  EX l3 : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = (i + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ”
  &&  (uintArray.seg ret_pre (0 : Int) (i + 1) l3)
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  TT && emp 
|--
  “ ((Zlength ((l3_2 ++ (((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def array_vector_sum_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  ((Zlength ((l3_2 ++ (((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))) :: (@List.nil Int))))) = (i + 1))

noncomputable def array_vector_sum_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_2)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg ret_pre (0 : Int) i_2 l3_2)
  ** (uintArray.undef_seg ret_pre i_2 n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
|--
  EX l3 : (List Int),
  “ ((Zlength (l3)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l3 (0 : Int)) = ((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))))) ”
  &&  (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full ret_pre n_pre l3)
) \/
(
forall (n_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_2)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg ret_pre (0 : Int) i_2 l3_2)
|--
  EX l3 : (List Int),
  “ ((Zlength (l3)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l3 (0 : Int)) = ((Znth i l1 (0 : Int)) + (Znth i l2 (0 : Int))))) ”
  &&  (uintArray.full ret_pre n_pre l3)
)

noncomputable def array_vector_sum_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg ret_pre (0 : Int) i l3)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt |-> ((Znth i l1 (0 : Int))))
  ** (uintArray.missing_i a_pre i (0 : Int) n_pre l1)
  ** (uintArray.seg ret_pre (0 : Int) i l3)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full b_pre n_pre l2)

noncomputable def array_vector_sum_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg ret_pre (0 : Int) i l3)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full b_pre n_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt |-> ((Znth i l2 (0 : Int))))
  ** (uintArray.missing_i b_pre i (0 : Int) n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg ret_pre (0 : Int) i l3)
  ** (uintArray.undef_seg ret_pre i n_pre)

noncomputable def array_vector_sum_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg ret_pre (0 : Int) i l3)
  ** (uintArray.undef_seg ret_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) + (Znth k_3 l2 (0 : Int))))) ”
  &&  (((ret_pre + (i * sizeof(UINT)))) # UInt |->_)
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg ret_pre (0 : Int) i l3)

noncomputable def pointwise_mul_safety_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "c" ) )) # Ptr |-> (c_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.undef_full c_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pointwise_mul_safety_wit_2 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg c_pre (0 : Int) (i + 1) (l3 ++ (((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))) :: (@List.nil Int))))
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "c" ) )) # Ptr |-> (c_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def pointwise_mul_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.undef_full c_pre n_pre)
|--
  EX l3 : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ”
  &&  (uintArray.seg c_pre (0 : Int) (0 : Int) l3)
  ** (uintArray.undef_seg c_pre (0 : Int) n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 (@List.nil Int) (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def pointwise_mul_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 (@List.nil Int) (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))

noncomputable def pointwise_mul_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))

noncomputable def pointwise_mul_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))

noncomputable def pointwise_mul_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l1 (0 : Int))) ∧ ((Znth i l1 (0 : Int)) < 100)))) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l2 (0 : Int))) ∧ ((Znth i_2 l2 (0 : Int)) < 100)))) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def pointwise_mul_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg c_pre (0 : Int) (i + 1) (l3_2 ++ (((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))) :: (@List.nil Int))))
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
|--
  EX l3 : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = (i + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ”
  &&  (uintArray.seg c_pre (0 : Int) (i + 1) l3)
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
) \/
(
forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  TT && emp 
|--
  “ ((Zlength ((l3_2 ++ (((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def pointwise_mul_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  ((Zlength ((l3_2 ++ (((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))) :: (@List.nil Int))))) = (i + 1))

noncomputable def pointwise_mul_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_2)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg c_pre (0 : Int) i_2 l3_2)
  ** (uintArray.undef_seg c_pre i_2 n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
|--
  EX l3 : (List Int),
  “ ((Zlength (l3)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l3 (0 : Int)) = ((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))))) ”
  &&  (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full c_pre n_pre l3)
) \/
(
forall (n_pre : Int) (c_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_2)) -> ((Znth k_3 l3_2 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg c_pre (0 : Int) i_2 l3_2)
|--
  EX l3 : (List Int),
  “ ((Zlength (l3)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l3 (0 : Int)) = ((Znth i l1 (0 : Int)) * (Znth i l2 (0 : Int))))) ”
  &&  (uintArray.full c_pre n_pre l3)
)

noncomputable def pointwise_mul_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.seg c_pre (0 : Int) i l3)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.full b_pre n_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt |-> ((Znth i l1 (0 : Int))))
  ** (uintArray.missing_i a_pre i (0 : Int) n_pre l1)
  ** (uintArray.seg c_pre (0 : Int) i l3)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full b_pre n_pre l2)

noncomputable def pointwise_mul_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg c_pre (0 : Int) i l3)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full b_pre n_pre l2)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt |-> ((Znth i l2 (0 : Int))))
  ** (uintArray.missing_i b_pre i (0 : Int) n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg c_pre (0 : Int) i l3)
  ** (uintArray.undef_seg c_pre i n_pre)

noncomputable def pointwise_mul_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l3 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100)))) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100)))) (PreH9 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int)))))) ,
  (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg c_pre (0 : Int) i l3)
  ** (uintArray.undef_seg c_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((Zlength (l3)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((0 : Int) <= (Znth k l1 (0 : Int))) ∧ ((Znth k l1 (0 : Int)) < 100))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((0 : Int) <= (Znth k_2 l2 (0 : Int))) ∧ ((Znth k_2 l2 (0 : Int)) < 100))) ” &&
  “ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l3 (0 : Int)) = ((Znth k_3 l1 (0 : Int)) * (Znth k_3 l2 (0 : Int))))) ”
  &&  (((c_pre + (i * sizeof(UINT)))) # UInt |->_)
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full b_pre n_pre l2)
  ** (uintArray.full a_pre n_pre l1)
  ** (uintArray.seg c_pre (0 : Int) i l3)

noncomputable def array_max_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  ((( &( "max" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def array_max_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  ((( &( "max" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def array_max_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  ((( &( "max" ) )) # Int |-> ((-1)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_max_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "max" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_max_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "max" ) )) # Int |-> (v))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_max_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ” &&
  “ (((0 : Int) = (0 : Int)) -> ((-1) = (-1))) ” &&
  “ (((0 : Int) < (0 : Int)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (0 : Int))) ∧ ((-1) = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (0 : Int))) -> ((Znth k_3 l (0 : Int)) <= (-1))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ”
  &&  emp
)

noncomputable def array_max_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((0 : Int) <= (Znth i l (0 : Int))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))

noncomputable def array_max_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ” &&
  “ (((i + 1) = (0 : Int)) -> ((Znth i l (0 : Int)) = (-1))) ” &&
  “ (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ ((Znth i l (0 : Int)) = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= (Znth i l (0 : Int)))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  TT && emp 
|--
  “ (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ ((Znth i l (0 : Int)) = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= (Znth i l (0 : Int)))))) ”
  &&  emp
)

noncomputable def array_max_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ ((Znth i l (0 : Int)) = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= (Znth i l (0 : Int))))))

noncomputable def array_max_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ” &&
  “ (((i + 1) = (0 : Int)) -> (v = (-1))) ” &&
  “ (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= v)))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  TT && emp 
|--
  “ (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= v)))) ”
  &&  emp
)

noncomputable def array_max_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (((0 : Int) < (i + 1)) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (i + 1))) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (i + 1))) -> ((Znth k_3 l (0 : Int)) <= v))))

noncomputable def array_max_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (i : Int) (k_2 : Int) (i_3 : Int) (v : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH7 : ((i_3 = (0 : Int)) -> (v = (-1)))) (PreH8 : (((0 : Int) < i_3) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i_3)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_3)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((n_pre = (0 : Int)) -> (v = (-1))) ” &&
  “ (((0 : Int) < n_pre) -> (exists (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) ∧ (v = (Znth i l (0 : Int)))) ∧ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((Znth i_2 l (0 : Int)) <= v)))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (i : Int) (k_2 : Int) (i_3 : Int) (v : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH7 : ((i_3 = (0 : Int)) -> (v = (-1)))) (PreH8 : (((0 : Int) < i_3) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i_3)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_3)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  TT && emp 
|--
  “ (((0 : Int) < n_pre) -> (exists (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) ∧ (v = (Znth i l (0 : Int)))) ∧ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((Znth i_2 l (0 : Int)) <= v)))) ”
  &&  emp
)

noncomputable def array_max_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (i : Int) (k_2 : Int) (i_3 : Int) (v : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH7 : ((i_3 = (0 : Int)) -> (v = (-1)))) (PreH8 : (((0 : Int) < i_3) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i_3)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i_3)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (((0 : Int) < n_pre) -> (exists (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) ∧ (v = (Znth i l (0 : Int)))) ∧ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> ((Znth i_2 l (0 : Int)) <= v))))

noncomputable def array_max_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH7 : ((i = (0 : Int)) -> (v = (-1)))) (PreH8 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ” &&
  “ ((i = (0 : Int)) -> (v = (-1))) ” &&
  “ (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre l)

noncomputable def array_max_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (k_2 : Int) (i : Int) (v : Int) (PreH1 : ((Znth i l (0 : Int)) > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int))))) (PreH8 : ((i = (0 : Int)) -> (v = (-1)))) (PreH9 : (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((Znth i l (0 : Int)) > v) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((0 : Int) <= (Znth k l (0 : Int)))) ” &&
  “ ((i = (0 : Int)) -> (v = (-1))) ” &&
  “ (((0 : Int) < i) -> (exists (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < i)) ∧ (v = (Znth k_2 l (0 : Int)))) ∧ forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < i)) -> ((Znth k_3 l (0 : Int)) <= v)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre l)

noncomputable def memset_safety_wit_1 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** (intArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def memset_safety_wit_2 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l (0 : Int)) = value_pre))) ,
  (intArray.seg a_pre (0 : Int) (i + 1) (l ++ (value_pre :: (@List.nil Int))))
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def memset_entail_wit_1 : Prop :=
  (
forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.undef_full a_pre n_pre)
|--
  EX l : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l)) = (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k l (0 : Int)) = value_pre)) ”
  &&  (intArray.seg a_pre (0 : Int) (0 : Int) l)
  ** (intArray.undef_seg a_pre (0 : Int) n_pre)
) \/
(
forall (value_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = value_pre)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def memset_entail_wit_1_split_goal_1 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k (@List.nil Int) (0 : Int)) = value_pre))

noncomputable def memset_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def memset_entail_wit_2 : Prop :=
  (
forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l_2 (0 : Int)) = value_pre))) ,
  (intArray.seg a_pre (0 : Int) (i + 1) (l_2 ++ (value_pre :: (@List.nil Int))))
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
|--
  EX l : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l)) = (i + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i + 1))) -> ((Znth k l (0 : Int)) = value_pre)) ”
  &&  (intArray.seg a_pre (0 : Int) (i + 1) l)
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
) \/
(
forall (value_pre : Int) (n_pre : Int) (l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l_2 (0 : Int)) = value_pre))) ,
  TT && emp 
|--
  “ ((Zlength ((l_2 ++ (value_pre :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def memset_entail_wit_2_split_goal_1 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l_2 (0 : Int)) = value_pre))) ,
  ((Zlength ((l_2 ++ (value_pre :: (@List.nil Int))))) = (i + 1))

noncomputable def memset_return_wit_1 : Prop :=
  (
forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (l_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l_2 (0 : Int)) = value_pre))) ,
  (intArray.seg a_pre (0 : Int) i_2 l_2)
  ** (intArray.undef_seg a_pre i_2 n_pre)
|--
  EX l : (List Int),
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l (0 : Int)) = value_pre)) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (l_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i_2)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l_2 (0 : Int)) = value_pre))) ,
  (intArray.seg a_pre (0 : Int) i_2 l_2)
|--
  EX l : (List Int),
  “ ((Zlength (l)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l (0 : Int)) = value_pre)) ”
  &&  (intArray.full a_pre n_pre l)
)

noncomputable def memset_partial_solve_wit_1 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l)) = i)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l (0 : Int)) = value_pre))) ,
  (intArray.seg a_pre (0 : Int) i l)
  ** (intArray.undef_seg a_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((Zlength (l)) = i) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l (0 : Int)) = value_pre)) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
  ** (intArray.seg a_pre (0 : Int) i l)

noncomputable def array_to_list_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |->_)
  ** ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_to_list_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |->_)
  ** ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_to_list_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |->_)
  ** ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_to_list_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (n_pre ≠ (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full a_pre n_pre l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |-> (retval))
  ** ((( &( "head" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def array_to_list_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head ≠ (0 : Int))) (PreH7 : (tail ≠ (0 : Int))) (PreH8 : ((0 : Int) < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> ((Znth i l (0 : Int))))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full a_pre n_pre l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Ptr |-> (head))
  ** ((( &( "tail" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_to_list_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (n_pre ≠ (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full a_pre n_pre l)
|--
  EX v : Int,
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ (v = (Znth ((1 - 1)) (l) ((0 : Int)))) ”
  &&  ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg retval retval (sublist ((0 : Int)) ((1 - 1)) (l)))
  ** (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (n_pre ≠ (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((1 - 1)) (l)) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def array_to_list_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (n_pre ≠ (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((sublist ((0 : Int)) ((1 - 1)) (l)) = (@List.nil Int))

noncomputable def array_to_list_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head ≠ (0 : Int))) (PreH7 : (tail ≠ (0 : Int))) (PreH8 : ((0 : Int) < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v_2 = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> ((Znth i l (0 : Int))))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full a_pre n_pre l)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  EX v : Int,
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ (v = (Znth (((i + 1) - 1)) (l) ((0 : Int)))) ”
  &&  ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head retval (sublist ((0 : Int)) (((i + 1) - 1)) (l)))
  ** (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head ≠ (0 : Int))) (PreH9 : (tail ≠ (0 : Int))) (PreH10 : ((0 : Int) < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((Znth i l (0 : Int)) = (Znth (((i + 1) - 1)) (l) ((0 : Int)))) ” &&
  “ ((Znth i l (0 : Int)) = (Znth (((i + 1) - 1)) (l) ((0 : Int)))) ”
  &&  (sllseg head retval (sublist ((0 : Int)) (((i + 1) - 1)) (l)))
)

noncomputable def array_to_list_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head ≠ (0 : Int))) (PreH9 : (tail ≠ (0 : Int))) (PreH10 : ((0 : Int) < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((Znth i l (0 : Int)) = (Znth (((i + 1) - 1)) (l) ((0 : Int)))) ”

noncomputable def array_to_list_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head ≠ (0 : Int))) (PreH9 : (tail ≠ (0 : Int))) (PreH10 : ((0 : Int) < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((Znth i l (0 : Int)) = (Znth (((i + 1) - 1)) (l) ((0 : Int)))) ”

noncomputable def array_to_list_entail_wit_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (l : (List Int)) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (retval_next : Int) (retval : Int) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval ≠ (0 : Int))) (PreH4 : (retval_next = (0 : Int))) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head ≠ (0 : Int))) (PreH9 : (tail ≠ (0 : Int))) (PreH10 : ((0 : Int) < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  (sllseg head retval (sublist ((0 : Int)) (((i + 1) - 1)) (l)))

noncomputable def array_to_list_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
  ** (intArray.full a_pre n_pre l)
|--
  (sll head l)
  ** (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head ≠ (0 : Int))) (PreH7 : (tail ≠ (0 : Int))) (PreH8 : ((0 : Int) < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  EX y : Int, EX l0 : (List Int), EX x : Int,
  “ (head ≠ (0 : Int)) ” &&
  “ (l = (x :: l0)) ”
  &&  (sll y l0)
  ** ((&((head # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((head # "list")  ->ₛ "data")) # Int |-> (x))
)

noncomputable def array_to_list_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (intArray.full a_pre n_pre l)
|--
  (sll (0 : Int) l)
  ** (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (l = (@List.nil Int)) ”
  &&  emp
)

noncomputable def array_to_list_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : (n_pre = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (l = (@List.nil Int))

noncomputable def array_to_list_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (intArray.full a_pre n_pre l)
|--
  “ (n_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def array_to_list_partial_solve_wit_2_pure : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |->_)
  ** ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((Znth (0 : Int) l (0 : Int)) = (Znth (0 : Int) l (0 : Int))) ”

noncomputable def array_to_list_partial_solve_wit_2_aux : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((Znth (0 : Int) l (0 : Int)) = (Znth (0 : Int) l (0 : Int))) ” &&
  “ (n_pre ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full a_pre n_pre l)

noncomputable def array_to_list_partial_solve_wit_2 : Prop := array_to_list_partial_solve_wit_2_pure -> array_to_list_partial_solve_wit_2_aux

noncomputable def array_to_list_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
  ** (intArray.full a_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (tail ≠ (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ (v = (Znth ((i - 1)) (l) ((0 : Int)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre l)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))

noncomputable def array_to_list_partial_solve_wit_4_pure : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "node" ) )) # Ptr |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Ptr |-> (head))
  ** ((( &( "tail" ) )) # Ptr |-> (tail))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((Znth i l (0 : Int)) = (Znth i l (0 : Int))) ”

noncomputable def array_to_list_partial_solve_wit_4_aux : Prop :=
  forall (n_pre : Int) (a_pre : Int) (l : (List Int)) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1)) (l) ((0 : Int))))) ,
  (intArray.full a_pre n_pre l)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))
|--
  “ ((Znth i l (0 : Int)) = (Znth i l (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (tail ≠ (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ (v = (Znth ((i - 1)) (l) ((0 : Int)))) ”
  &&  (intArray.full a_pre n_pre l)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (sllseg head tail (sublist ((0 : Int)) ((i - 1)) (l)))

noncomputable def array_to_list_partial_solve_wit_4 : Prop := array_to_list_partial_solve_wit_4_pure -> array_to_list_partial_solve_wit_4_aux


structure VC_Correct : Type where
  proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1
  proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2
  proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3
  proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1
  proof_of_array_copy1_safety_wit_1 : array_copy1_safety_wit_1
  proof_of_array_copy1_safety_wit_2 : array_copy1_safety_wit_2
  proof_of_array_copy1_partial_solve_wit_1 : array_copy1_partial_solve_wit_1
  proof_of_array_copy1_partial_solve_wit_2 : array_copy1_partial_solve_wit_2
  proof_of_array_concat_safety_wit_1 : array_concat_safety_wit_1
  proof_of_array_concat_safety_wit_2 : array_concat_safety_wit_2
  proof_of_array_concat_safety_wit_3 : array_concat_safety_wit_3
  proof_of_array_concat_safety_wit_4 : array_concat_safety_wit_4
  proof_of_array_concat_safety_wit_5 : array_concat_safety_wit_5
  proof_of_array_concat_partial_solve_wit_1 : array_concat_partial_solve_wit_1
  proof_of_array_concat_partial_solve_wit_2 : array_concat_partial_solve_wit_2
  proof_of_array_concat_partial_solve_wit_3 : array_concat_partial_solve_wit_3
  proof_of_array_concat_partial_solve_wit_4 : array_concat_partial_solve_wit_4
  proof_of_array_swap_safety_wit_1 : array_swap_safety_wit_1
  proof_of_array_swap_safety_wit_2 : array_swap_safety_wit_2
  proof_of_array_swap_partial_solve_wit_1 : array_swap_partial_solve_wit_1
  proof_of_array_swap_partial_solve_wit_2 : array_swap_partial_solve_wit_2
  proof_of_array_swap_partial_solve_wit_3 : array_swap_partial_solve_wit_3
  proof_of_array_swap_partial_solve_wit_4 : array_swap_partial_solve_wit_4
  proof_of_array_vector_sum_safety_wit_1 : array_vector_sum_safety_wit_1
  proof_of_array_vector_sum_safety_wit_2 : array_vector_sum_safety_wit_2
  proof_of_array_vector_sum_partial_solve_wit_1 : array_vector_sum_partial_solve_wit_1
  proof_of_array_vector_sum_partial_solve_wit_2 : array_vector_sum_partial_solve_wit_2
  proof_of_array_vector_sum_partial_solve_wit_3 : array_vector_sum_partial_solve_wit_3
  proof_of_pointwise_mul_safety_wit_1 : pointwise_mul_safety_wit_1
  proof_of_pointwise_mul_safety_wit_2 : pointwise_mul_safety_wit_2
  proof_of_pointwise_mul_partial_solve_wit_1 : pointwise_mul_partial_solve_wit_1
  proof_of_pointwise_mul_partial_solve_wit_2 : pointwise_mul_partial_solve_wit_2
  proof_of_pointwise_mul_partial_solve_wit_3 : pointwise_mul_partial_solve_wit_3
  proof_of_array_max_safety_wit_1 : array_max_safety_wit_1
  proof_of_array_max_safety_wit_2 : array_max_safety_wit_2
  proof_of_array_max_safety_wit_3 : array_max_safety_wit_3
  proof_of_array_max_safety_wit_4 : array_max_safety_wit_4
  proof_of_array_max_safety_wit_5 : array_max_safety_wit_5
  proof_of_array_max_partial_solve_wit_1 : array_max_partial_solve_wit_1
  proof_of_array_max_partial_solve_wit_2 : array_max_partial_solve_wit_2
  proof_of_memset_safety_wit_1 : memset_safety_wit_1
  proof_of_memset_safety_wit_2 : memset_safety_wit_2
  proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1
  proof_of_array_to_list_safety_wit_1 : array_to_list_safety_wit_1
  proof_of_array_to_list_safety_wit_2 : array_to_list_safety_wit_2
  proof_of_array_to_list_safety_wit_3 : array_to_list_safety_wit_3
  proof_of_array_to_list_safety_wit_4 : array_to_list_safety_wit_4
  proof_of_array_to_list_safety_wit_5 : array_to_list_safety_wit_5
  proof_of_array_to_list_partial_solve_wit_1 : array_to_list_partial_solve_wit_1
  proof_of_array_to_list_partial_solve_wit_2_pure : array_to_list_partial_solve_wit_2_pure
  proof_of_array_to_list_partial_solve_wit_2 : array_to_list_partial_solve_wit_2
  proof_of_array_to_list_partial_solve_wit_3 : array_to_list_partial_solve_wit_3
  proof_of_array_to_list_partial_solve_wit_4_pure : array_to_list_partial_solve_wit_4_pure
  proof_of_array_to_list_partial_solve_wit_4 : array_to_list_partial_solve_wit_4
  proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1
  proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2
  proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1
  proof_of_array_copy1_entail_wit_1 : array_copy1_entail_wit_1
  proof_of_array_copy1_entail_wit_2 : array_copy1_entail_wit_2
  proof_of_array_copy1_return_wit_1 : array_copy1_return_wit_1
  proof_of_array_concat_entail_wit_1 : array_concat_entail_wit_1
  proof_of_array_concat_entail_wit_2 : array_concat_entail_wit_2
  proof_of_array_concat_entail_wit_3 : array_concat_entail_wit_3
  proof_of_array_concat_entail_wit_4 : array_concat_entail_wit_4
  proof_of_array_concat_return_wit_1 : array_concat_return_wit_1
  proof_of_array_swap_entail_wit_1 : array_swap_entail_wit_1
  proof_of_array_swap_entail_wit_2 : array_swap_entail_wit_2
  proof_of_array_swap_return_wit_1 : array_swap_return_wit_1
  proof_of_array_vector_sum_entail_wit_1 : array_vector_sum_entail_wit_1
  proof_of_array_vector_sum_entail_wit_2 : array_vector_sum_entail_wit_2
  proof_of_array_vector_sum_return_wit_1 : array_vector_sum_return_wit_1
  proof_of_pointwise_mul_entail_wit_1 : pointwise_mul_entail_wit_1
  proof_of_pointwise_mul_entail_wit_2 : pointwise_mul_entail_wit_2
  proof_of_pointwise_mul_return_wit_1 : pointwise_mul_return_wit_1
  proof_of_array_max_entail_wit_1 : array_max_entail_wit_1
  proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1
  proof_of_array_max_entail_wit_2_2 : array_max_entail_wit_2_2
  proof_of_array_max_return_wit_1 : array_max_return_wit_1
  proof_of_memset_entail_wit_1 : memset_entail_wit_1
  proof_of_memset_entail_wit_2 : memset_entail_wit_2
  proof_of_memset_return_wit_1 : memset_return_wit_1
  proof_of_array_to_list_entail_wit_1 : array_to_list_entail_wit_1
  proof_of_array_to_list_entail_wit_2 : array_to_list_entail_wit_2
  proof_of_array_to_list_return_wit_1 : array_to_list_return_wit_1
  proof_of_array_to_list_return_wit_2 : array_to_list_return_wit_2

end SimpleC.EE.QCP_demos_LLM.generated.array_cases_goal
