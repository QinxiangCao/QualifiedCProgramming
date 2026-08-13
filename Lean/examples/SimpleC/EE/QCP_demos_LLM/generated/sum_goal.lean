import SimpleC.SL.SeparationLogic


set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sum_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sum_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_3 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
)

noncomputable def arr_sum_safety_wit_3_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_safety_wit_3_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”

noncomputable def arr_sum_safety_wit_4 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  emp
)

noncomputable def arr_sum_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l)

noncomputable def arr_sum_do_while_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_do_while_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_do_while_safety_wit_3 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "ret" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
|--
  “ (((0 : Int) + (Znth (0 : Int) l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) + (Znth (0 : Int) l (0 : Int)))) ”

noncomputable def arr_sum_do_while_safety_wit_4 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "ret" ) )) # Int |-> (((0 : Int) + (Znth (0 : Int) l (0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
|--
  “ (((0 : Int) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) + 1)) ”

noncomputable def arr_sum_do_while_safety_wit_5 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_do_while_safety_wit_6 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
)

noncomputable def arr_sum_do_while_safety_wit_6_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_do_while_safety_wit_6_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”

noncomputable def arr_sum_do_while_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  emp
)

noncomputable def arr_sum_do_while_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_do_while_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= ((0 : Int) + 1)) ” &&
  “ (((0 : Int) + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (((0 : Int) + (Znth (0 : Int) l (0 : Int))) = (sum ((sublist ((0 : Int)) (((0 : Int) + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ (((0 : Int) + (Znth (0 : Int) l (0 : Int))) = (sum ((sublist ((0 : Int)) (((0 : Int) + 1)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_do_while_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (((0 : Int) + (Znth (0 : Int) l (0 : Int))) = (sum ((sublist ((0 : Int)) (((0 : Int) + 1)) (l)))))

noncomputable def arr_sum_do_while_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_do_while_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 = n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 = n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_do_while_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 = n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_do_while_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def arr_sum_do_while_partial_solve_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 ≠ n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (i_2 ≠ n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l)

noncomputable def arr_sum_for_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_for_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_for_safety_wit_3 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
)

noncomputable def arr_sum_for_safety_wit_3_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_for_safety_wit_3_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”

noncomputable def arr_sum_for_safety_wit_4 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_for_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_for_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_for_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_for_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  emp
)

noncomputable def arr_sum_for_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_for_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_for_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_for_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l)

noncomputable def arr_sum_which_implies_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_which_implies_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_which_implies_safety_wit_3 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
)

noncomputable def arr_sum_which_implies_safety_wit_3_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_which_implies_safety_wit_3_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”

noncomputable def arr_sum_which_implies_safety_wit_4 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_which_implies_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_which_implies_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_which_implies_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_which_implies_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  emp
)

noncomputable def arr_sum_which_implies_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_which_implies_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_which_implies_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_which_implies_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l)

noncomputable def arr_sum_update_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_update_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_update_safety_wit_3 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l1)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l1 (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l1 (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l1)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l1 (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l1 (0 : Int)))) ”
)

noncomputable def arr_sum_update_safety_wit_3_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l1)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l1 (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_update_safety_wit_3_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l1)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l1 (0 : Int)))) ”

noncomputable def arr_sum_update_safety_wit_4 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l1)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i_2 l1 (0 : Int)))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_update_safety_wit_5 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((0 : Int)) (l1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l1 (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_update_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  EX l1 : (List Int),
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (n_pre = (Zlength (l1))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k l1 (0 : Int)) = (0 : Int))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int)))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (intArray.full a_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l (0 : Int)) = (Znth k_2 l (0 : Int)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k l (0 : Int)) = (0 : Int))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (n_pre = (Zlength (l))) ”
  &&  emp
)

noncomputable def arr_sum_update_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_update_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l (0 : Int)) = (Znth k_2 l (0 : Int))))

noncomputable def arr_sum_update_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (0 : Int))) -> ((Znth k l (0 : Int)) = (0 : Int)))

noncomputable def arr_sum_update_entail_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_update_entail_wit_1_split_goal_5 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (n_pre = (Zlength (l)))

noncomputable def arr_sum_update_entail_wit_1_split_goal_6 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (n_pre = (Zlength (l)))

noncomputable def arr_sum_update_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre (replace_Znth (i_2) ((0 : Int)) (l1_2)))
|--
  EX l1 : (List Int),
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (n_pre = (Zlength (l1))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (i_2 + 1))) -> ((Znth k l1 (0 : Int)) = (0 : Int))) ” &&
  “ forall (k_2 : Int) , ((((i_2 + 1) <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int)))) ” &&
  “ ((ret + (Znth i_2 l1_2 (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l1_2 (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ” &&
  “ (n_pre = (Zlength ((replace_Znth (i_2) ((0 : Int)) (l1_2))))) ”
  &&  emp
)

noncomputable def arr_sum_update_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l1_2 (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_update_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (n_pre = (Zlength ((replace_Znth (i_2) ((0 : Int)) (l1_2)))))

noncomputable def arr_sum_update_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_3 : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_3)) (PreH5 : (i_3 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_3)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_3 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_3) (l)))))) ,
  (intArray.full a_pre n_pre l1_2)
|--
  EX l1 : (List Int),
  “ (ret = (sum (l))) ” &&
  “ (n_pre = (Zlength (l1))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l1 (0 : Int)) = (0 : Int))) ”
  &&  (intArray.full a_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_3 : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_3)) (PreH5 : (i_3 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_3)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_3 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_3) (l)))))) ,
  TT && emp 
|--
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l1_2 (0 : Int)) = (0 : Int))) ” &&
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_update_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_3 : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_3)) (PreH5 : (i_3 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_3)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_3 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_3) (l)))))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i l1_2 (0 : Int)) = (0 : Int)))

noncomputable def arr_sum_update_return_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (ret : Int) (l1_2 : (List Int)) (i_3 : Int) (PreH1 : (i_3 >= n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_3)) (PreH5 : (i_3 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1_2)))) (PreH8 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_3)) -> ((Znth k l1_2 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_3 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1_2 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_3) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_update_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l1)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (n_pre = (Zlength (l1))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1 (0 : Int)) = (0 : Int))) ” &&
  “ forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int)))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l1 (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l1)

noncomputable def arr_sum_update_partial_solve_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (l1 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < n_pre)) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1 (0 : Int)) = (0 : Int)))) (PreH10 : forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int))))) (PreH11 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l1)
|--
  “ (i_2 < n_pre) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 <= n_pre) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (n_pre = (Zlength (l1))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < i_2)) -> ((Znth k l1 (0 : Int)) = (0 : Int))) ” &&
  “ forall (k_2 : Int) , (((i_2 <= k_2) ∧ (k_2 < n_pre)) -> ((Znth k_2 l1 (0 : Int)) = (Znth k_2 l (0 : Int)))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l1)

noncomputable def arr_sum_pointer_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_pointer_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) ,
  ((( &( "ret" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_pointer_safety_wit_3 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i_2 : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 <= n_pre)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH6 : (n_pre = (Zlength (l)))) (PreH7 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH8 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> (ret))
  ** (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_pointer_safety_wit_4 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp ≠ (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp ≠ (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”
)

noncomputable def arr_sum_pointer_safety_wit_4_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp ≠ (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((ret + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def arr_sum_pointer_safety_wit_4_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp ≠ (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> (ret))
|--
  “ ((INT_MIN) <= (ret + (Znth i l (0 : Int)))) ”

noncomputable def arr_sum_pointer_safety_wit_5 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i < n_pre)) (PreH5 : (endp ≠ (a_pre + (i * sizeof(INT))))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "endp" ) )) # Ptr |-> (endp))
  ** ((( &( "ret" ) )) # Int |-> ((ret + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_pointer_entail_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ ((a_pre + (n_pre * sizeof(INT))) = (a_pre + (n_pre * sizeof(INT)))) ” &&
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l))))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_pointer_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (l)))))

noncomputable def arr_sum_pointer_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  (n_pre = (Zlength (l)))

noncomputable def arr_sum_pointer_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_pointer_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i * sizeof(INT)))) sizeof(INT)) ≠ (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (endp ≠ (a_pre + (i * sizeof(INT)))) ” &&
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i * sizeof(INT)))) sizeof(INT)) ≠ (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  TT && emp 
|--
  “ forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100))) ” &&
  “ (endp ≠ (a_pre + (i * sizeof(INT)))) ” &&
  “ (i < n_pre) ”
  &&  emp
)

noncomputable def arr_sum_pointer_entail_wit_2_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i * sizeof(INT)))) sizeof(INT)) ≠ (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((0 : Int) <= (Znth i_2 l (0 : Int))) ∧ ((Znth i_2 l (0 : Int)) < 100)))

noncomputable def arr_sum_pointer_entail_wit_2_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i * sizeof(INT)))) sizeof(INT)) ≠ (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (endp ≠ (a_pre + (i * sizeof(INT))))

noncomputable def arr_sum_pointer_entail_wit_2_split_goal_3 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i * sizeof(INT)))) sizeof(INT)) ≠ (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i) (l)))))) ,
  (i < n_pre)

noncomputable def arr_sum_pointer_entail_wit_3 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i_2 : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp ≠ (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= (i_2 + 1)) ” &&
  “ ((i_2 + 1) <= n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” &&
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i_2 : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp ≠ (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l))))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ”
  &&  emp
)

noncomputable def arr_sum_pointer_entail_wit_3_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i_2 : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp ≠ (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  ((ret + (Znth i_2 l (0 : Int))) = (sum ((sublist ((0 : Int)) ((i_2 + 1)) (l)))))

noncomputable def arr_sum_pointer_entail_wit_3_split_goal_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i_2 : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp ≠ (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < n_pre)) -> (((0 : Int) <= (Znth i_3 l (0 : Int))) ∧ ((Znth i_3 l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))

noncomputable def arr_sum_pointer_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i_2 : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i_2 * sizeof(INT)))) sizeof(INT)) = (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ (ret = (sum (l))) ”
  &&  (intArray.full a_pre n_pre l)
) \/
(
forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i_2 : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i_2 * sizeof(INT)))) sizeof(INT)) = (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
)

noncomputable def arr_sum_pointer_return_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (ret : Int) (endp : Int) (i_2 : Int) (PreH1 : ((Z.quot (endp - (a_pre + (i_2 * sizeof(INT)))) sizeof(INT)) = (0 : Int))) (PreH2 : ((0 : Int) < n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (ret = (sum (l)))

noncomputable def arr_sum_pointer_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (l : (List Int)) (i_2 : Int) (endp : Int) (ret : Int) (PreH1 : ((0 : Int) < n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : ((0 : Int) <= i_2)) (PreH4 : (i_2 < n_pre)) (PreH5 : (endp ≠ (a_pre + (i_2 * sizeof(INT))))) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100)))) (PreH7 : (n_pre = (Zlength (l)))) (PreH8 : (endp = (a_pre + (n_pre * sizeof(INT))))) (PreH9 : (ret = (sum ((sublist ((0 : Int)) (i_2) (l)))))) ,
  (intArray.full a_pre n_pre l)
|--
  “ ((0 : Int) < n_pre) ” &&
  “ (n_pre < 100) ” &&
  “ ((0 : Int) <= i_2) ” &&
  “ (i_2 < n_pre) ” &&
  “ (endp ≠ (a_pre + (i_2 * sizeof(INT)))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((0 : Int) <= (Znth i l (0 : Int))) ∧ ((Znth i l (0 : Int)) < 100))) ” &&
  “ (n_pre = (Zlength (l))) ” &&
  “ (endp = (a_pre + (n_pre * sizeof(INT)))) ” &&
  “ (ret = (sum ((sublist ((0 : Int)) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(INT)))) # Int |-> ((Znth i_2 l (0 : Int))))
  ** (intArray.missing_i a_pre i_2 (0 : Int) n_pre l)


structure VC_Correct : Type where
  proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1
  proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2
  proof_of_arr_sum_safety_wit_4 : arr_sum_safety_wit_4
  proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1
  proof_of_arr_sum_do_while_safety_wit_1 : arr_sum_do_while_safety_wit_1
  proof_of_arr_sum_do_while_safety_wit_2 : arr_sum_do_while_safety_wit_2
  proof_of_arr_sum_do_while_safety_wit_3 : arr_sum_do_while_safety_wit_3
  proof_of_arr_sum_do_while_safety_wit_4 : arr_sum_do_while_safety_wit_4
  proof_of_arr_sum_do_while_safety_wit_5 : arr_sum_do_while_safety_wit_5
  proof_of_arr_sum_do_while_partial_solve_wit_1 : arr_sum_do_while_partial_solve_wit_1
  proof_of_arr_sum_do_while_partial_solve_wit_2 : arr_sum_do_while_partial_solve_wit_2
  proof_of_arr_sum_for_safety_wit_1 : arr_sum_for_safety_wit_1
  proof_of_arr_sum_for_safety_wit_2 : arr_sum_for_safety_wit_2
  proof_of_arr_sum_for_safety_wit_4 : arr_sum_for_safety_wit_4
  proof_of_arr_sum_for_partial_solve_wit_1 : arr_sum_for_partial_solve_wit_1
  proof_of_arr_sum_which_implies_safety_wit_1 : arr_sum_which_implies_safety_wit_1
  proof_of_arr_sum_which_implies_safety_wit_2 : arr_sum_which_implies_safety_wit_2
  proof_of_arr_sum_which_implies_safety_wit_4 : arr_sum_which_implies_safety_wit_4
  proof_of_arr_sum_which_implies_partial_solve_wit_1 : arr_sum_which_implies_partial_solve_wit_1
  proof_of_arr_sum_update_safety_wit_1 : arr_sum_update_safety_wit_1
  proof_of_arr_sum_update_safety_wit_2 : arr_sum_update_safety_wit_2
  proof_of_arr_sum_update_safety_wit_4 : arr_sum_update_safety_wit_4
  proof_of_arr_sum_update_safety_wit_5 : arr_sum_update_safety_wit_5
  proof_of_arr_sum_update_partial_solve_wit_1 : arr_sum_update_partial_solve_wit_1
  proof_of_arr_sum_update_partial_solve_wit_2 : arr_sum_update_partial_solve_wit_2
  proof_of_arr_sum_pointer_safety_wit_1 : arr_sum_pointer_safety_wit_1
  proof_of_arr_sum_pointer_safety_wit_2 : arr_sum_pointer_safety_wit_2
  proof_of_arr_sum_pointer_safety_wit_3 : arr_sum_pointer_safety_wit_3
  proof_of_arr_sum_pointer_safety_wit_5 : arr_sum_pointer_safety_wit_5
  proof_of_arr_sum_pointer_partial_solve_wit_1 : arr_sum_pointer_partial_solve_wit_1
  proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3
  proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1
  proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2
  proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1
  proof_of_arr_sum_do_while_safety_wit_6 : arr_sum_do_while_safety_wit_6
  proof_of_arr_sum_do_while_entail_wit_1 : arr_sum_do_while_entail_wit_1
  proof_of_arr_sum_do_while_entail_wit_2 : arr_sum_do_while_entail_wit_2
  proof_of_arr_sum_do_while_return_wit_1 : arr_sum_do_while_return_wit_1
  proof_of_arr_sum_for_safety_wit_3 : arr_sum_for_safety_wit_3
  proof_of_arr_sum_for_entail_wit_1 : arr_sum_for_entail_wit_1
  proof_of_arr_sum_for_entail_wit_2 : arr_sum_for_entail_wit_2
  proof_of_arr_sum_for_return_wit_1 : arr_sum_for_return_wit_1
  proof_of_arr_sum_which_implies_safety_wit_3 : arr_sum_which_implies_safety_wit_3
  proof_of_arr_sum_which_implies_entail_wit_1 : arr_sum_which_implies_entail_wit_1
  proof_of_arr_sum_which_implies_entail_wit_2 : arr_sum_which_implies_entail_wit_2
  proof_of_arr_sum_which_implies_return_wit_1 : arr_sum_which_implies_return_wit_1
  proof_of_arr_sum_update_safety_wit_3 : arr_sum_update_safety_wit_3
  proof_of_arr_sum_update_entail_wit_1 : arr_sum_update_entail_wit_1
  proof_of_arr_sum_update_entail_wit_2 : arr_sum_update_entail_wit_2
  proof_of_arr_sum_update_return_wit_1 : arr_sum_update_return_wit_1
  proof_of_arr_sum_pointer_safety_wit_4 : arr_sum_pointer_safety_wit_4
  proof_of_arr_sum_pointer_entail_wit_1 : arr_sum_pointer_entail_wit_1
  proof_of_arr_sum_pointer_entail_wit_2 : arr_sum_pointer_entail_wit_2
  proof_of_arr_sum_pointer_entail_wit_3 : arr_sum_pointer_entail_wit_3
  proof_of_arr_sum_pointer_return_wit_1 : arr_sum_pointer_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.sum_goal
