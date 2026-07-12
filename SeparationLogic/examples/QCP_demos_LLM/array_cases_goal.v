Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function arr_sum -----*)

Definition arr_sum_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) ,
  ((( &( "ret" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i) (l)))))) ,
  (UIntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # UInt  |-> (unsigned_last_nbits ((ret + (Znth i l 0) )) (32)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_entail_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (UIntArray.full a_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  (UIntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (l))))) ”
  &&  emp
).

Definition arr_sum_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l 0)) /\ ((Znth i_2 l 0) < 100)))) ,
  (0 = (sum ((sublist (0) (0) (l)))))
.

Definition arr_sum_entail_wit_2 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (UIntArray.full a_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ ((unsigned_last_nbits ((ret + (Znth i_2 l 0) )) (32)) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  (UIntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((ret + (Znth i_2 l 0) )) (32)) = (sum ((sublist (0) ((i_2 + 1 )) (l))))) ”
  &&  emp
).

Definition arr_sum_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  ((unsigned_last_nbits ((ret + (Znth i_2 l 0) )) (32)) = (sum ((sublist (0) ((i_2 + 1 )) (l)))))
.

Definition arr_sum_return_wit_1 := 
(
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (UIntArray.full a_pre n_pre l )
|--
  “ (ret = (sum (l))) ”
  &&  (UIntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  TT && emp 
|--
  “ (ret = (sum (l))) ”
  &&  emp
).

Definition arr_sum_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (ret = (sum (l)))
.

Definition arr_sum_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (ret: Z) (i_2: Z) (PreH1 : (i_2 < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 100)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 <= n_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100)))) (PreH7 : (ret = (sum ((sublist (0) (i_2) (l)))))) ,
  (UIntArray.full a_pre n_pre l )
|--
  “ (i_2 < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l 0)) /\ ((Znth i l 0) < 100))) ” 
  &&  “ (ret = (sum ((sublist (0) (i_2) (l))))) ”
  &&  (((a_pre + (i_2 * sizeof(UINT)))) # UInt  |-> (Znth i_2 l 0))
  **  (UIntArray.missing_i a_pre i_2 0 n_pre l )
.

(*----- Function array_copy1 -----*)

Definition array_copy1_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (IntArray.undef_full dest_pre n_pre )
  **  (IntArray.full src_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_copy1_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_copy1_entail_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.undef_full dest_pre n_pre )
  **  (IntArray.full src_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg dest_pre 0 0 (sublist (0) (0) (l)) )
  **  (IntArray.undef_seg dest_pre 0 n_pre )
  **  (IntArray.full src_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist (0) (0) (l)) = (@nil Z)) ”
  &&  emp
).

Definition array_copy1_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((sublist (0) (0) (l)) = (@nil Z))
.

Definition array_copy1_entail_wit_2 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg dest_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l))) ”
  &&  emp
).

Definition array_copy1_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l)))
.

Definition array_copy1_return_wit_1 := 
(
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
  **  (IntArray.undef_seg dest_pre i n_pre )
  **  (IntArray.full src_pre n_pre l )
|--
  (IntArray.full dest_pre n_pre l )
  **  (IntArray.full src_pre n_pre l )
) \/
(
forall (n_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
|--
  (IntArray.full dest_pre n_pre l )
).

Definition array_copy1_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
|--
  (IntArray.full dest_pre n_pre l )
.

Definition array_copy1_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
  **  (IntArray.undef_seg dest_pre i n_pre )
  **  (IntArray.full src_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i src_pre i 0 n_pre l )
  **  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
  **  (IntArray.undef_seg dest_pre i n_pre )
.

Definition array_copy1_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full src_pre n_pre l )
  **  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
  **  (IntArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((dest_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre l )
  **  (IntArray.seg dest_pre 0 i (sublist (0) (i) (l)) )
.

(*----- Function array_concat -----*)

Definition array_concat_safety_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.undef_full ret_pre (n_pre + m_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_concat_safety_wit_2 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (i + 1 ) (app ((sublist (0) (i) (l1))) ((cons ((Znth i l1 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_concat_safety_wit_3 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_concat_safety_wit_4 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ ((n_pre + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + i )) ”
.

Definition array_concat_safety_wit_5 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 ((n_pre + i ) + 1 ) (app ((app (l1) ((sublist (0) (i) (l2))))) ((cons ((Znth i l2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ret_pre ((n_pre + i ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full b_pre m_pre l2 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_concat_entail_wit_1 := 
(
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.undef_full ret_pre (n_pre + m_pre ) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg ret_pre 0 0 (sublist (0) (0) (l1)) )
  **  (IntArray.undef_seg ret_pre 0 (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  TT && emp 
|--
  “ ((sublist (0) (0) (l1)) = (@nil Z)) ”
  &&  emp
).

Definition array_concat_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((sublist (0) (0) (l1)) = (@nil Z))
.

Definition array_concat_entail_wit_2 := 
(
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (i + 1 ) (app ((sublist (0) (i) (l1))) ((cons ((Znth i l1 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg ret_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l1)) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
) \/
(
forall (m_pre: Z) (n_pre: Z) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (l1))) ((cons ((Znth i l1 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l1))) ”
  &&  emp
).

Definition array_concat_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((app ((sublist (0) (i) (l1))) ((cons ((Znth i l1 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l1)))
.

Definition array_concat_entail_wit_3 := 
(
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg ret_pre 0 (n_pre + 0 ) (app (l1) ((sublist (0) (0) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + 0 ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
|--
  (IntArray.seg ret_pre 0 (n_pre + 0 ) (app (l1) ((sublist (0) (0) (l2)))) )
).

Definition array_concat_entail_wit_3_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
|--
  (IntArray.seg ret_pre 0 (n_pre + 0 ) (app (l1) ((sublist (0) (0) (l2)))) )
.

Definition array_concat_entail_wit_4 := 
(
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 ((n_pre + i ) + 1 ) (app ((app (l1) ((sublist (0) (i) (l2))))) ((cons ((Znth i l2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ret_pre ((n_pre + i ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg ret_pre 0 (n_pre + (i + 1 ) ) (app (l1) ((sublist (0) ((i + 1 )) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + (i + 1 ) ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 ((n_pre + i ) + 1 ) (app ((app (l1) ((sublist (0) (i) (l2))))) ((cons ((Znth i l2 0)) ((@nil Z))))) )
|--
  (IntArray.seg ret_pre 0 (n_pre + (i + 1 ) ) (app (l1) ((sublist (0) ((i + 1 )) (l2)))) )
).

Definition array_concat_entail_wit_4_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 ((n_pre + i ) + 1 ) (app ((app (l1) ((sublist (0) (i) (l2))))) ((cons ((Znth i l2 0)) ((@nil Z))))) )
|--
  (IntArray.seg ret_pre 0 (n_pre + (i + 1 ) ) (app (l1) ((sublist (0) ((i + 1 )) (l2)))) )
.

Definition array_concat_return_wit_1 := 
(
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.full ret_pre (n_pre + m_pre ) (app (l1) (l2)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
|--
  (IntArray.full ret_pre (n_pre + m_pre ) (app (l1) (l2)) )
).

Definition array_concat_return_wit_1_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
|--
  (IntArray.full ret_pre (n_pre + m_pre ) (app (l1) (l2)) )
.

Definition array_concat_partial_solve_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l1 )
  **  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full b_pre m_pre l2 )
.

Definition array_concat_partial_solve_wit_2 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.seg ret_pre 0 i (sublist (0) (i) (l1)) )
  **  (IntArray.full b_pre m_pre l2 )
.

Definition array_concat_partial_solve_wit_3 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre m_pre l2 )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l2 0))
  **  (IntArray.missing_i b_pre i 0 m_pre l2 )
  **  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
.

Definition array_concat_partial_solve_wit_4 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  (IntArray.full a_pre n_pre l1 )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((ret_pre + ((n_pre + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ret_pre ((n_pre + i ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full b_pre m_pre l2 )
  **  (IntArray.seg ret_pre 0 (n_pre + i ) (app (l1) ((sublist (0) (i) (l2)))) )
  **  (IntArray.full a_pre n_pre l1 )
.

(*----- Function array_swap -----*)

Definition array_swap_safety_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_swap_safety_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full b_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) 0)) ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))))) )
  **  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_swap_entail_wit_1 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full a_pre n_pre l1 )
  **  (IntArray.full b_pre n_pre l2 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre (app ((sublist (0) (0) (l2))) ((sublist (0) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (0) (l1))) ((sublist (0) (n_pre) (l2)))) )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ (l1 = (app ((sublist (0) (0) (l2))) ((sublist (0) (n_pre) (l1))))) ” 
  &&  “ (l2 = (app ((sublist (0) (0) (l1))) ((sublist (0) (n_pre) (l2))))) ”
  &&  emp
).

Definition array_swap_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (l1 = (app ((sublist (0) (0) (l2))) ((sublist (0) (n_pre) (l1)))))
.

Definition array_swap_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : ((Zlength (l1)) = n_pre)) (PreH4 : ((Zlength (l2)) = n_pre)) ,
  (l2 = (app ((sublist (0) (0) (l1))) ((sublist (0) (n_pre) (l2)))))
.

Definition array_swap_entail_wit_2 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full b_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) 0)) ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))))) )
  **  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre (app ((sublist (0) ((i + 1 )) (l2))) ((sublist ((i + 1 )) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) ((i + 1 )) (l1))) ((sublist ((i + 1 )) (n_pre) (l2)))) )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ ((replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) 0)) ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))))) = (app ((sublist (0) ((i + 1 )) (l1))) ((sublist ((i + 1 )) (n_pre) (l2))))) ” 
  &&  “ ((replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) = (app ((sublist (0) ((i + 1 )) (l2))) ((sublist ((i + 1 )) (n_pre) (l1))))) ”
  &&  emp
).

Definition array_swap_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) 0)) ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))))) = (app ((sublist (0) ((i + 1 )) (l1))) ((sublist ((i + 1 )) (n_pre) (l2)))))
.

Definition array_swap_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) = (app ((sublist (0) ((i + 1 )) (l2))) ((sublist ((i + 1 )) (n_pre) (l1)))))
.

Definition array_swap_return_wit_1 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full a_pre n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
|--
  (IntArray.full a_pre n_pre l2 )
  **  (IntArray.full b_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) = l2) ” 
  &&  “ ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) = l1) ”
  &&  emp
).

Definition array_swap_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) = l2)
.

Definition array_swap_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  ((app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) = l1)
.

Definition array_swap_partial_solve_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full a_pre n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) 0))
  **  (IntArray.missing_i a_pre i 0 n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
.

Definition array_swap_partial_solve_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full a_pre n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0))
  **  (IntArray.missing_i b_pre i 0 n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
  **  (IntArray.full a_pre n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
.

Definition array_swap_partial_solve_wit_3 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
  **  (IntArray.full a_pre n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre (app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
.

Definition array_swap_partial_solve_wit_4 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l1)) = n_pre)) (PreH7 : ((Zlength (l2)) = n_pre)) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) )
  **  (IntArray.full b_pre n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ ((Zlength (l2)) = n_pre) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i b_pre i 0 n_pre (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) )
  **  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth i (app ((sublist (0) (i) (l1))) ((sublist (i) (n_pre) (l2)))) 0)) ((app ((sublist (0) (i) (l2))) ((sublist (i) (n_pre) (l1)))))) )
.

(*----- Function array_vector_sum -----*)

Definition array_vector_sum_safety_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.undef_full ret_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_vector_sum_safety_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.seg ret_pre 0 (i + 1 ) (app (l3) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_vector_sum_entail_wit_1 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.undef_full ret_pre n_pre )
|--
  EX (l3: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) ))) ”
  &&  (UIntArray.seg ret_pre 0 0 l3 )
  **  (UIntArray.undef_seg ret_pre 0 n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  TT && emp 
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition array_vector_sum_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition array_vector_sum_entail_wit_2 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.seg ret_pre 0 (i + 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
|--
  EX (l3: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) ))) ”
  &&  (UIntArray.seg ret_pre 0 (i + 1 ) l3 )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  TT && emp 
|--
  “ (((Znth 0 (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth 0 l1 0) + (Znth 0 l2 0) )) /\ ((Znth ((i + 1 ) - 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth ((i + 1 ) - 1 ) l1 0) + (Znth ((i + 1 ) - 1 ) l2 0) ))) ” 
  &&  “ ((Zlength ((app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition array_vector_sum_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (((Znth 0 (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth 0 l1 0) + (Znth 0 l2 0) )) /\ ((Znth ((i + 1 ) - 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth ((i + 1 ) - 1 ) l1 0) + (Znth ((i + 1 ) - 1 ) l2 0) )))
.

Definition array_vector_sum_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  ((Zlength ((app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) + (Znth i l2 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition array_vector_sum_return_wit_1 := 
(
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.seg ret_pre 0 i_2 l3_2 )
  **  (UIntArray.undef_seg ret_pre i_2 n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  EX (l3: (@list Z)) ,
  “ ((Zlength (l3)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l3 0) = ((Znth i l1 0) + (Znth i l2 0) ))) ”
  &&  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full ret_pre n_pre l3 )
) \/
(
forall (n_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.seg ret_pre 0 i_2 l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ ((Zlength (l3)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l3 0) = ((Znth i l1 0) + (Znth i l2 0) ))) ”
  &&  (UIntArray.full ret_pre n_pre l3 )
).

Definition array_vector_sum_partial_solve_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.seg ret_pre 0 i l3 )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) ))) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l1 0))
  **  (UIntArray.missing_i a_pre i 0 n_pre l1 )
  **  (UIntArray.seg ret_pre 0 i l3 )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
.

Definition array_vector_sum_partial_solve_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg ret_pre 0 i l3 )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) ))) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l2 0))
  **  (UIntArray.missing_i b_pre i 0 n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg ret_pre 0 i l3 )
  **  (UIntArray.undef_seg ret_pre i n_pre )
.

Definition array_vector_sum_partial_solve_wit_3 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) )))) ,
  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg ret_pre 0 i l3 )
  **  (UIntArray.undef_seg ret_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) + (Znth k_3 l2 0) ))) ”
  &&  (((ret_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg ret_pre 0 i l3 )
.

(*----- Function pointwise_mul -----*)

Definition pointwise_mul_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.undef_full c_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pointwise_mul_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.seg c_pre 0 (i + 1 ) (app (l3) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition pointwise_mul_entail_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.undef_full c_pre n_pre )
|--
  EX (l3: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) ))) ”
  &&  (UIntArray.seg c_pre 0 0 l3 )
  **  (UIntArray.undef_seg c_pre 0 n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  TT && emp 
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition pointwise_mul_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i l1 0)) /\ ((Znth i l1 0) < 100)))) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 l2 0)) /\ ((Znth i_2 l2 0) < 100)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition pointwise_mul_entail_wit_2 := 
(
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.seg c_pre 0 (i + 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
|--
  EX (l3: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) ))) ”
  &&  (UIntArray.seg c_pre 0 (i + 1 ) l3 )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  TT && emp 
|--
  “ (((Znth 0 (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth 0 l1 0) * (Znth 0 l2 0) )) /\ ((Znth ((i + 1 ) - 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth ((i + 1 ) - 1 ) l1 0) * (Znth ((i + 1 ) - 1 ) l2 0) ))) ” 
  &&  “ ((Zlength ((app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition pointwise_mul_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (((Znth 0 (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth 0 l1 0) * (Znth 0 l2 0) )) /\ ((Znth ((i + 1 ) - 1 ) (app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))) 0) = ((Znth ((i + 1 ) - 1 ) l1 0) * (Znth ((i + 1 ) - 1 ) l2 0) )))
.

Definition pointwise_mul_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  ((Zlength ((app (l3_2) ((cons ((unsigned_last_nbits (((Znth i l1 0) * (Znth i l2 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition pointwise_mul_return_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.seg c_pre 0 i_2 l3_2 )
  **  (UIntArray.undef_seg c_pre i_2 n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  EX (l3: (@list Z)) ,
  “ ((Zlength (l3)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l3 0) = ((Znth i l1 0) * (Znth i l2 0) ))) ”
  &&  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full c_pre n_pre l3 )
) \/
(
forall (n_pre: Z) (c_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l3_2 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.seg c_pre 0 i_2 l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ ((Zlength (l3)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l3 0) = ((Znth i l1 0) * (Znth i l2 0) ))) ”
  &&  (UIntArray.full c_pre n_pre l3 )
).

Definition pointwise_mul_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.seg c_pre 0 i l3 )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) ))) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l1 0))
  **  (UIntArray.missing_i a_pre i 0 n_pre l1 )
  **  (UIntArray.seg c_pre 0 i l3 )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
.

Definition pointwise_mul_partial_solve_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg c_pre 0 i l3 )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) ))) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l2 0))
  **  (UIntArray.missing_i b_pre i 0 n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg c_pre 0 i l3 )
  **  (UIntArray.undef_seg c_pre i n_pre )
.

Definition pointwise_mul_partial_solve_wit_3 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (l3: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < 100)) (PreH6 : ((Zlength (l3)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) )))) ,
  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg c_pre 0 i l3 )
  **  (UIntArray.undef_seg c_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ ((Zlength (l3)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l1 0)) /\ ((Znth k l1 0) < 100))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l2 0)) /\ ((Znth k_2 l2 0) < 100))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l3 0) = ((Znth k_3 l1 0) * (Znth k_3 l2 0) ))) ”
  &&  (((c_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full b_pre n_pre l2 )
  **  (UIntArray.full a_pre n_pre l1 )
  **  (UIntArray.seg c_pre 0 i l3 )
.

(*----- Function array_max -----*)

Definition array_max_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (0 <= (Znth i l 0)))) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition array_max_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (0 <= (Znth i l 0)))) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition array_max_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (0 <= (Znth i l 0)))) ,
  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_max_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "max" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_max_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "max" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_max_entail_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (0 <= (Znth i l 0)))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0))) ” 
  &&  “ ((0 = 0) -> ((-1) = (-1))) ” 
  &&  “ ((0 < 0) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) /\ ((-1) = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 l 0) <= (-1))))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_max_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0))) ” 
  &&  “ (((i + 1 ) = 0) -> ((Znth i l 0) = (-1))) ” 
  &&  “ ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth i l 0) = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= (Znth i l 0))))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  TT && emp 
|--
  “ ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth i l 0) = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= (Znth i l 0))))) ”
  &&  emp
).

Definition array_max_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((Znth i l 0) = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= (Znth i l 0)))))
.

Definition array_max_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0))) ” 
  &&  “ (((i + 1 ) = 0) -> (v = (-1))) ” 
  &&  “ ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= v)))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  TT && emp 
|--
  “ ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= v)))) ”
  &&  emp
).

Definition array_max_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  ((0 < (i + 1 )) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l 0) <= v))))
.

Definition array_max_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) (k_2: Z) (i_3: Z) (v: Z) (PreH1 : (i_3 >= n_pre)) (PreH2 : (0 <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH7 : ((i_3 = 0) -> (v = (-1)))) (PreH8 : ((0 < i_3) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i_3)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_3)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ ((n_pre = 0) -> (v = (-1))) ” 
  &&  “ ((0 < n_pre) -> (exists (i: Z) , (((0 <= i) /\ (i < n_pre)) /\ (v = (Znth i l 0))) /\ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) <= v)))) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (k_2: Z) (i_3: Z) (v: Z) (PreH1 : (i_3 >= n_pre)) (PreH2 : (0 <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH7 : ((i_3 = 0) -> (v = (-1)))) (PreH8 : ((0 < i_3) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i_3)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_3)) -> ((Znth k_3 l 0) <= v))))) ,
  TT && emp 
|--
  “ ((0 < n_pre) -> (exists (i: Z) , (((0 <= i) /\ (i < n_pre)) /\ (v = (Znth i l 0))) /\ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) <= v)))) ”
  &&  emp
).

Definition array_max_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (k_2: Z) (i_3: Z) (v: Z) (PreH1 : (i_3 >= n_pre)) (PreH2 : (0 <= i_3)) (PreH3 : (i_3 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH7 : ((i_3 = 0) -> (v = (-1)))) (PreH8 : ((0 < i_3) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i_3)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i_3)) -> ((Znth k_3 l 0) <= v))))) ,
  ((0 < n_pre) -> (exists (i: Z) , (((0 <= i) /\ (i < n_pre)) /\ (v = (Znth i l 0))) /\ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) <= v))))
.

Definition array_max_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH7 : ((i = 0) -> (v = (-1)))) (PreH8 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0))) ” 
  &&  “ ((i = 0) -> (v = (-1))) ” 
  &&  “ ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_max_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (k_2: Z) (i: Z) (v: Z) (PreH1 : ((Znth i l 0) > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0)))) (PreH8 : ((i = 0) -> (v = (-1)))) (PreH9 : ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v))))) ,
  (IntArray.full a_pre n_pre l )
|--
  “ ((Znth i l 0) > v) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (0 <= (Znth k l 0))) ” 
  &&  “ ((i = 0) -> (v = (-1))) ” 
  &&  “ ((0 < i) -> (exists (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) /\ (v = (Znth k_2 l 0))) /\ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l 0) <= v)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

(*----- Function memset -----*)

Definition memset_safety_wit_1 := 
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.undef_full a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memset_safety_wit_2 := 
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l 0) = value_pre))) ,
  (IntArray.seg a_pre 0 (i + 1 ) (app (l) ((cons (value_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memset_entail_wit_1 := 
(
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.undef_full a_pre n_pre )
|--
  EX (l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l 0) = value_pre)) ”
  &&  (IntArray.seg a_pre 0 0 l )
  **  (IntArray.undef_seg a_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition memset_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition memset_entail_wit_2 := 
(
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l_2 0) = value_pre))) ,
  (IntArray.seg a_pre 0 (i + 1 ) (app (l_2) ((cons (value_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
|--
  EX (l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l 0) = value_pre)) ”
  &&  (IntArray.seg a_pre 0 (i + 1 ) l )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
) \/
(
forall (value_pre: Z) (n_pre: Z) (l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l_2 0) = value_pre))) ,
  TT && emp 
|--
  “ (((Znth 0 (app (l_2) ((cons (value_pre) ((@nil Z))))) 0) = value_pre) /\ ((Znth ((i + 1 ) - 1 ) (app (l_2) ((cons (value_pre) ((@nil Z))))) 0) = value_pre)) ” 
  &&  “ ((Zlength ((app (l_2) ((cons (value_pre) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition memset_entail_wit_2_split_goal_1 := 
forall (value_pre: Z) (n_pre: Z) (l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l_2 0) = value_pre))) ,
  (((Znth 0 (app (l_2) ((cons (value_pre) ((@nil Z))))) 0) = value_pre) /\ ((Znth ((i + 1 ) - 1 ) (app (l_2) ((cons (value_pre) ((@nil Z))))) 0) = value_pre))
.

Definition memset_entail_wit_2_split_goal_2 := 
forall (value_pre: Z) (n_pre: Z) (l_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l_2 0) = value_pre))) ,
  ((Zlength ((app (l_2) ((cons (value_pre) ((@nil Z))))))) = (i + 1 ))
.

Definition memset_return_wit_1 := 
(
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (l_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l_2 0) = value_pre))) ,
  (IntArray.seg a_pre 0 i_2 l_2 )
  **  (IntArray.undef_seg a_pre i_2 n_pre )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) = value_pre)) ”
  &&  (IntArray.full a_pre n_pre l )
) \/
(
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (l_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l_2)) = i_2)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l_2 0) = value_pre))) ,
  (IntArray.seg a_pre 0 i_2 l_2 )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) = value_pre)) ”
  &&  (IntArray.full a_pre n_pre l )
).

Definition memset_partial_solve_wit_1 := 
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((Zlength (l)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l 0) = value_pre))) ,
  (IntArray.seg a_pre 0 i l )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l 0) = value_pre)) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (IntArray.seg a_pre 0 i l )
.

(*----- Function array_to_list -----*)

Definition array_to_list_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_to_list_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_to_list_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_to_list_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> (Znth 0 l 0))
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition array_to_list_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head <> 0)) (PreH7 : (tail <> 0)) (PreH8 : (0 < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> (Znth i l 0))
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  ((( &( "tail" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_to_list_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> (Znth 0 l 0))
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (IntArray.full a_pre n_pre l )
|--
  EX (v: Z) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (v = (Znth ((1 - 1 )) (l) (0))) ”
  &&  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg retval retval (sublist (0) ((1 - 1 )) (l)) )
  **  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ ((Znth 0 l 0) = (Znth ((1 - 1 )) (l) (0))) ” 
  &&  “ ((sublist (0) ((1 - 1 )) (l)) = (@nil Z)) ” 
  &&  “ ((Znth 0 l 0) = (Znth ((1 - 1 )) (l) (0))) ”
  &&  emp
).

Definition array_to_list_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((Znth 0 l 0) = (Znth ((1 - 1 )) (l) (0)))
.

Definition array_to_list_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((sublist (0) ((1 - 1 )) (l)) = (@nil Z))
.

Definition array_to_list_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (n_pre <> 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  ((Znth 0 l 0) = (Znth ((1 - 1 )) (l) (0)))
.

Definition array_to_list_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v_2: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head <> 0)) (PreH7 : (tail <> 0)) (PreH8 : (0 < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v_2 = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> (Znth i l 0))
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (IntArray.full a_pre n_pre l )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  EX (v: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (v = (Znth (((i + 1 ) - 1 )) (l) (0))) ”
  &&  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head retval (sublist (0) (((i + 1 ) - 1 )) (l)) )
  **  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (v_2: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head <> 0)) (PreH9 : (tail <> 0)) (PreH10 : (0 < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((Znth i l 0) = (Znth (((i + 1 ) - 1 )) (l) (0))) ” 
  &&  “ ((Znth i l 0) = (Znth (((i + 1 ) - 1 )) (l) (0))) ”
  &&  (sllseg head retval (sublist (0) (((i + 1 ) - 1 )) (l)) )
).

Definition array_to_list_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (v_2: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head <> 0)) (PreH9 : (tail <> 0)) (PreH10 : (0 < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((Znth i l 0) = (Znth (((i + 1 ) - 1 )) (l) (0))) ”
.

Definition array_to_list_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (v_2: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head <> 0)) (PreH9 : (tail <> 0)) (PreH10 : (0 < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((Znth i l 0) = (Znth (((i + 1 ) - 1 )) (l) (0))) ”
.

Definition array_to_list_entail_wit_2_split_goal_spatial := 
forall (n_pre: Z) (l: (@list Z)) (v_2: Z) (tail: Z) (head: Z) (i: Z) (retval_next: Z) (retval: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (head <> 0)) (PreH9 : (tail <> 0)) (PreH10 : (0 < n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (v_2 = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  (sllseg head retval (sublist (0) (((i + 1 ) - 1 )) (l)) )
.

Definition array_to_list_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
  **  (IntArray.full a_pre n_pre l )
|--
  (sll head l )
  **  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head <> 0)) (PreH7 : (tail <> 0)) (PreH8 : (0 < n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (head <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ”
  &&  (sll y l0 )
  **  ((&((head)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((head)  # "list" ->ₛ "data")) # Int  |-> x)
).

Definition array_to_list_return_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (IntArray.full a_pre n_pre l )
|--
  (sll 0 l )
  **  (IntArray.full a_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (l = (@nil Z)) ”
  &&  emp
).

Definition array_to_list_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (l = (@nil Z))
.

Definition array_to_list_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_to_list_partial_solve_wit_2_pure := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((Znth 0 l 0) = (Znth 0 l 0)) ”
.

Definition array_to_list_partial_solve_wit_2_aux := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) ,
  (IntArray.full a_pre n_pre l )
|--
  “ ((Znth 0 l 0) = (Znth 0 l 0)) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_to_list_partial_solve_wit_2 := array_to_list_partial_solve_wit_2_pure -> array_to_list_partial_solve_wit_2_aux.

Definition array_to_list_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
  **  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (tail <> 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (v = (Znth ((i - 1 )) (l) (0))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
.

Definition array_to_list_partial_solve_wit_4_pure := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  (IntArray.full a_pre n_pre l )
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((Znth i l 0) = (Znth i l 0)) ”
.

Definition array_to_list_partial_solve_wit_4_aux := 
forall (n_pre: Z) (a_pre: Z) (l: (@list Z)) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (v = (Znth ((i - 1 )) (l) (0)))) ,
  (IntArray.full a_pre n_pre l )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
|--
  “ ((Znth i l 0) = (Znth i l 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (tail <> 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (v = (Znth ((i - 1 )) (l) (0))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  (sllseg head tail (sublist (0) ((i - 1 )) (l)) )
.

Definition array_to_list_partial_solve_wit_4 := array_to_list_partial_solve_wit_4_pure -> array_to_list_partial_solve_wit_4_aux.

Module Type VC_Correct.

Include sll_Strategy_Correct.

Axiom proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1.
Axiom proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2.
Axiom proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3.
Axiom proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Axiom proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Axiom proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Axiom proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1.
Axiom proof_of_array_copy1_safety_wit_1 : array_copy1_safety_wit_1.
Axiom proof_of_array_copy1_safety_wit_2 : array_copy1_safety_wit_2.
Axiom proof_of_array_copy1_entail_wit_1 : array_copy1_entail_wit_1.
Axiom proof_of_array_copy1_entail_wit_2 : array_copy1_entail_wit_2.
Axiom proof_of_array_copy1_return_wit_1 : array_copy1_return_wit_1.
Axiom proof_of_array_copy1_partial_solve_wit_1 : array_copy1_partial_solve_wit_1.
Axiom proof_of_array_copy1_partial_solve_wit_2 : array_copy1_partial_solve_wit_2.
Axiom proof_of_array_concat_safety_wit_1 : array_concat_safety_wit_1.
Axiom proof_of_array_concat_safety_wit_2 : array_concat_safety_wit_2.
Axiom proof_of_array_concat_safety_wit_3 : array_concat_safety_wit_3.
Axiom proof_of_array_concat_safety_wit_4 : array_concat_safety_wit_4.
Axiom proof_of_array_concat_safety_wit_5 : array_concat_safety_wit_5.
Axiom proof_of_array_concat_entail_wit_1 : array_concat_entail_wit_1.
Axiom proof_of_array_concat_entail_wit_2 : array_concat_entail_wit_2.
Axiom proof_of_array_concat_entail_wit_3 : array_concat_entail_wit_3.
Axiom proof_of_array_concat_entail_wit_4 : array_concat_entail_wit_4.
Axiom proof_of_array_concat_return_wit_1 : array_concat_return_wit_1.
Axiom proof_of_array_concat_partial_solve_wit_1 : array_concat_partial_solve_wit_1.
Axiom proof_of_array_concat_partial_solve_wit_2 : array_concat_partial_solve_wit_2.
Axiom proof_of_array_concat_partial_solve_wit_3 : array_concat_partial_solve_wit_3.
Axiom proof_of_array_concat_partial_solve_wit_4 : array_concat_partial_solve_wit_4.
Axiom proof_of_array_swap_safety_wit_1 : array_swap_safety_wit_1.
Axiom proof_of_array_swap_safety_wit_2 : array_swap_safety_wit_2.
Axiom proof_of_array_swap_entail_wit_1 : array_swap_entail_wit_1.
Axiom proof_of_array_swap_entail_wit_2 : array_swap_entail_wit_2.
Axiom proof_of_array_swap_return_wit_1 : array_swap_return_wit_1.
Axiom proof_of_array_swap_partial_solve_wit_1 : array_swap_partial_solve_wit_1.
Axiom proof_of_array_swap_partial_solve_wit_2 : array_swap_partial_solve_wit_2.
Axiom proof_of_array_swap_partial_solve_wit_3 : array_swap_partial_solve_wit_3.
Axiom proof_of_array_swap_partial_solve_wit_4 : array_swap_partial_solve_wit_4.
Axiom proof_of_array_vector_sum_safety_wit_1 : array_vector_sum_safety_wit_1.
Axiom proof_of_array_vector_sum_safety_wit_2 : array_vector_sum_safety_wit_2.
Axiom proof_of_array_vector_sum_entail_wit_1 : array_vector_sum_entail_wit_1.
Axiom proof_of_array_vector_sum_entail_wit_2 : array_vector_sum_entail_wit_2.
Axiom proof_of_array_vector_sum_return_wit_1 : array_vector_sum_return_wit_1.
Axiom proof_of_array_vector_sum_partial_solve_wit_1 : array_vector_sum_partial_solve_wit_1.
Axiom proof_of_array_vector_sum_partial_solve_wit_2 : array_vector_sum_partial_solve_wit_2.
Axiom proof_of_array_vector_sum_partial_solve_wit_3 : array_vector_sum_partial_solve_wit_3.
Axiom proof_of_pointwise_mul_safety_wit_1 : pointwise_mul_safety_wit_1.
Axiom proof_of_pointwise_mul_safety_wit_2 : pointwise_mul_safety_wit_2.
Axiom proof_of_pointwise_mul_entail_wit_1 : pointwise_mul_entail_wit_1.
Axiom proof_of_pointwise_mul_entail_wit_2 : pointwise_mul_entail_wit_2.
Axiom proof_of_pointwise_mul_return_wit_1 : pointwise_mul_return_wit_1.
Axiom proof_of_pointwise_mul_partial_solve_wit_1 : pointwise_mul_partial_solve_wit_1.
Axiom proof_of_pointwise_mul_partial_solve_wit_2 : pointwise_mul_partial_solve_wit_2.
Axiom proof_of_pointwise_mul_partial_solve_wit_3 : pointwise_mul_partial_solve_wit_3.
Axiom proof_of_array_max_safety_wit_1 : array_max_safety_wit_1.
Axiom proof_of_array_max_safety_wit_2 : array_max_safety_wit_2.
Axiom proof_of_array_max_safety_wit_3 : array_max_safety_wit_3.
Axiom proof_of_array_max_safety_wit_4 : array_max_safety_wit_4.
Axiom proof_of_array_max_safety_wit_5 : array_max_safety_wit_5.
Axiom proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Axiom proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Axiom proof_of_array_max_entail_wit_2_2 : array_max_entail_wit_2_2.
Axiom proof_of_array_max_return_wit_1 : array_max_return_wit_1.
Axiom proof_of_array_max_partial_solve_wit_1 : array_max_partial_solve_wit_1.
Axiom proof_of_array_max_partial_solve_wit_2 : array_max_partial_solve_wit_2.
Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_safety_wit_2 : memset_safety_wit_2.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.
Axiom proof_of_array_to_list_safety_wit_1 : array_to_list_safety_wit_1.
Axiom proof_of_array_to_list_safety_wit_2 : array_to_list_safety_wit_2.
Axiom proof_of_array_to_list_safety_wit_3 : array_to_list_safety_wit_3.
Axiom proof_of_array_to_list_safety_wit_4 : array_to_list_safety_wit_4.
Axiom proof_of_array_to_list_safety_wit_5 : array_to_list_safety_wit_5.
Axiom proof_of_array_to_list_entail_wit_1 : array_to_list_entail_wit_1.
Axiom proof_of_array_to_list_entail_wit_2 : array_to_list_entail_wit_2.
Axiom proof_of_array_to_list_return_wit_1 : array_to_list_return_wit_1.
Axiom proof_of_array_to_list_return_wit_2 : array_to_list_return_wit_2.
Axiom proof_of_array_to_list_partial_solve_wit_1 : array_to_list_partial_solve_wit_1.
Axiom proof_of_array_to_list_partial_solve_wit_2_pure : array_to_list_partial_solve_wit_2_pure.
Axiom proof_of_array_to_list_partial_solve_wit_2 : array_to_list_partial_solve_wit_2.
Axiom proof_of_array_to_list_partial_solve_wit_3 : array_to_list_partial_solve_wit_3.
Axiom proof_of_array_to_list_partial_solve_wit_4_pure : array_to_list_partial_solve_wit_4_pure.
Axiom proof_of_array_to_list_partial_solve_wit_4 : array_to_list_partial_solve_wit_4.

End VC_Correct.
