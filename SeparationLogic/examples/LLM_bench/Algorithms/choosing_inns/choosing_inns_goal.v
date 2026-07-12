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
Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function initCounts -----*)

Definition initCounts_safety_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition initCounts_safety_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i )) (PreH7 : (CountsZeroPrefix good_l i )) ,
  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg seen_pre 0 i seen_l )
  **  (IntArray.undef_seg seen_pre i k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition initCounts_safety_wit_3 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i )) (PreH7 : (CountsZeroPrefix good_l i )) ,
  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition initCounts_safety_wit_4 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (seen_l: (@list Z)) (good_l: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (0 <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountsZeroPrefix seen_l (i + 1 ) )) (PreH6 : (CountsZeroPrefix good_l (i + 1 ) )) ,
  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg seen_pre 0 (i + 1 ) seen_l )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 (i + 1 ) good_l )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition initCounts_entail_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (CountsZeroPrefix seen_l 0 ) ” 
  &&  “ (CountsZeroPrefix good_l 0 ) ”
  &&  (IntArray.seg seen_pre 0 0 seen_l )
  **  (IntArray.undef_seg seen_pre 0 k_pre )
  **  (IntArray.seg good_pre 0 0 good_l )
  **  (IntArray.undef_seg good_pre 0 k_pre )
) \/
(
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (@nil Z) 0 ) ” 
  &&  “ (CountsZeroPrefix (@nil Z) 0 ) ”
  &&  emp
).

Definition initCounts_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (@nil Z) 0 ) ”
.

Definition initCounts_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (@nil Z) 0 ) ”
.

Definition initCounts_entail_wit_2 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (IntArray.seg good_pre 0 (i + 1 ) (app (good_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < k_pre) ” 
  &&  “ (CountsZeroPrefix seen_l (i + 1 ) ) ” 
  &&  “ (CountsZeroPrefix good_l (i + 1 ) ) ”
  &&  (IntArray.seg seen_pre 0 (i + 1 ) seen_l )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 (i + 1 ) good_l )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
) \/
(
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (app (good_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ (CountsZeroPrefix (app (seen_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition initCounts_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (app (good_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ”
.

Definition initCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (app (seen_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ”
.

Definition initCounts_entail_wit_3 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (0 <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountsZeroPrefix seen_l_2 (i + 1 ) )) (PreH6 : (CountsZeroPrefix good_l_2 (i + 1 ) )) ,
  (IntArray.seg seen_pre 0 (i + 1 ) seen_l_2 )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 (i + 1 ) good_l_2 )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (CountsZeroPrefix seen_l (i + 1 ) ) ” 
  &&  “ (CountsZeroPrefix good_l (i + 1 ) ) ”
  &&  (IntArray.seg seen_pre 0 (i + 1 ) seen_l )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 (i + 1 ) good_l )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
.

Definition initCounts_return_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (IntArray.seg seen_pre 0 i seen_l_2 )
  **  (IntArray.undef_seg seen_pre i k_pre )
  **  (IntArray.seg good_pre 0 i good_l_2 )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (CountsZeroFull k_pre seen_l ) ” 
  &&  “ (CountsZeroFull k_pre good_l ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (IntArray.seg seen_pre 0 i seen_l_2 )
  **  (IntArray.seg good_pre 0 i good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (CountsZeroFull k_pre seen_l ) ” 
  &&  “ (CountsZeroFull k_pre good_l ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
).

Definition initCounts_partial_solve_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i )) (PreH7 : (CountsZeroPrefix good_l i )) ,
  (IntArray.seg seen_pre 0 i seen_l )
  **  (IntArray.undef_seg seen_pre i k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CountsZeroPrefix seen_l i ) ” 
  &&  “ (CountsZeroPrefix good_l i ) ”
  &&  (((seen_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 i seen_l )
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
.

Definition initCounts_partial_solve_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l i )) (PreH7 : (CountsZeroPrefix good_l i )) ,
  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CountsZeroPrefix seen_l i ) ” 
  &&  “ (CountsZeroPrefix good_l i ) ”
  &&  (((good_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
.

(*----- Function copyCounts -----*)

Definition copyCounts_safety_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000)))) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_old 0)) /\ ((Znth idx_2 good_old 0) <= 200000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition copyCounts_safety_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < k_pre)) (PreH7 : (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000)))) (PreH9 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000)))) ,
  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition copyCounts_entail_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH6 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_old 0)) /\ ((Znth idx_4 good_old 0) <= 200000)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_old )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur 0 k_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000))) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH6 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_old 0)) /\ ((Znth idx_4 good_old 0) <= 200000)))) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old good_old 0 k_pre ) ”
  &&  emp
).

Definition copyCounts_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH6 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_old 0)) /\ ((Znth idx_4 good_old 0) <= 200000)))) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old good_old 0 k_pre ) ”
.

Definition copyCounts_entail_wit_2 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) (PreH9 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH10 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_cur_2 0)) /\ ((Znth idx_4 good_cur_2 0) <= 200000)))) ,
  (IntArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < k_pre) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000))) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) (PreH9 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH10 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_cur_2 0)) /\ ((Znth idx_4 good_cur_2 0) <= 200000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0)) /\ ((Znth 0 (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0) <= 200000)) /\ ((0 <= (Znth (k_pre - 1 ) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0)) /\ ((Znth (k_pre - 1 ) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0) <= 200000))) ” 
  &&  “ (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ) ”
  &&  emp
).

Definition copyCounts_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) (PreH9 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH10 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_cur_2 0)) /\ ((Znth idx_4 good_cur_2 0) <= 200000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0)) /\ ((Znth 0 (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0) <= 200000)) /\ ((0 <= (Znth (k_pre - 1 ) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0)) /\ ((Znth (k_pre - 1 ) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) 0) <= 200000))) ”
.

Definition copyCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) (PreH9 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH10 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_cur_2 0)) /\ ((Znth idx_4 good_cur_2 0) <= 200000)))) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ) ”
.

Definition copyCounts_entail_wit_3 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : ((Zlength (good_old)) = k_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < k_pre)) (PreH7 : (CopyCountsPrefix seen_l good_old good_cur_2 (i + 1 ) k_pre )) (PreH8 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 200000)))) (PreH9 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_cur_2 0)) /\ ((Znth idx_4 good_cur_2 0) <= 200000)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur_2 )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000))) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
.

Definition copyCounts_return_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) (PreH9 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 seen_l 0)) /\ ((Znth idx_2 seen_l 0) <= 200000)))) (PreH10 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 good_cur 0)) /\ ((Znth idx_3 good_cur 0) <= 200000)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre seen_l )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) (PreH9 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 seen_l 0)) /\ ((Znth idx_2 seen_l 0) <= 200000)))) (PreH10 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 good_cur 0)) /\ ((Znth idx_3 good_cur 0) <= 200000)))) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp
).

Definition copyCounts_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) (PreH9 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 seen_l 0)) /\ ((Znth idx_2 seen_l 0) <= 200000)))) (PreH10 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 good_cur 0)) /\ ((Znth idx_3 good_cur 0) <= 200000)))) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
.

Definition copyCounts_partial_solve_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000)))) (PreH10 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000))) ”
  &&  (((seen_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i seen_l 0))
  **  (IntArray.missing_i seen_pre i 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
.

Definition copyCounts_partial_solve_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((Zlength (seen_l)) = k_pre)) (PreH5 : ((Zlength (good_old)) = k_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= k_pre)) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000)))) (PreH10 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_l 0)) /\ ((Znth idx seen_l 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_cur 0)) /\ ((Znth idx_2 good_cur 0) <= 200000))) ”
  &&  (((good_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i good_pre i 0 k_pre good_cur )
  **  (IntArray.full seen_pre k_pre seen_l )
.

(*----- Function countChoosingInns -----*)

Definition countChoosingInns_safety_wit_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (ans: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH10 : (0 <= ans)) (PreH11 : (ans <= 19999900000)) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH13 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH11 : (CountsZeroFull k_pre seen_l )) (PreH12 : (CountsZeroFull k_pre good_l )) (PreH13 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l good_l )) (PreH14 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH15 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_3 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (answer + (Znth c seen_l 0) )) ”
.

Definition countChoosingInns_safety_wit_4 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c seen_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth c seen_l 0) + 1 )) ”
.

Definition countChoosingInns_safety_wit_5 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c seen_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition countChoosingInns_safety_wit_6 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full good_pre k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (answer + (Znth c good_l 0) )) ”
.

Definition countChoosingInns_safety_wit_7 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c good_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth c seen_l 0) + 1 )) ”
.

Definition countChoosingInns_safety_wit_8 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c good_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition countChoosingInns_safety_wit_9 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : ((Zlength (seen_next)) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH19 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) (PreH20 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH21 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH22 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next 0)) /\ ((Znth idx_3 seen_next 0) <= (i + 1 ))))) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre seen_next )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition countChoosingInns_safety_wit_10 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : (p_pre < cost)) (PreH10 : (cost <= 100)) (PreH11 : ((Zlength (colors_l)) = n_pre)) (PreH12 : ((Zlength (costs_l)) = n_pre)) (PreH13 : ((Zlength (seen_next)) = k_pre)) (PreH14 : ((Zlength (good_l)) = k_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH22 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH23 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l 0) ) seen_l good_l )) (PreH24 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l )) (PreH25 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH26 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH27 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next 0)) /\ ((Znth idx_3 seen_next 0) <= (i + 1 ))))) (PreH28 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= (i + 1 ))))) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition countChoosingInns_entail_wit_1 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (ans_2: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH12 : (0 <= ans_2)) (PreH13 : (ans_2 <= 19999900000)) (PreH14 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH15 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) ,
  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z))  (ans: Z) ,
  “ (0 = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (CountsZeroFull k_pre seen_l ) ” 
  &&  “ (CountsZeroFull k_pre good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (ans_2: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH12 : (0 <= ans_2)) (PreH13 : (ans_2 <= 19999900000)) (PreH14 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH15 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) ,
  TT && emp 
|--
  EX (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (CountsZeroFull k_pre seen_l_2 ) ” 
  &&  “ (CountsZeroFull k_pre good_l_2 ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_2 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH11 : (CountsZeroFull k_pre seen_l_2 )) (PreH12 : (CountsZeroFull k_pre good_l_2 )) (PreH13 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) (PreH14 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH15 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z))  (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= 0))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= 0))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH11 : (CountsZeroFull k_pre seen_l_2 )) (PreH12 : (CountsZeroFull k_pre good_l_2 )) (PreH13 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) (PreH14 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH15 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) ,
  TT && emp 
|--
  EX (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre answer seen_l_2 good_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l_2 0)) /\ ((Znth idx_3 seen_l_2 0) <= 0))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= 0))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_3 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) (PreH16 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH17 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH18 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l_2 0)) /\ ((Znth idx_7 seen_l_2 0) <= i)))) (PreH19 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l_2 0)) /\ ((Znth idx_8 good_l_2 0) <= i)))) ,
  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (ans: Z)  (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ ((Znth i colors_l 0) = (Znth i colors_l 0)) ” 
  &&  “ ((Znth i costs_l 0) = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (Znth i colors_l 0)) ” 
  &&  “ ((Znth i colors_l 0) < k_pre) ” 
  &&  “ (0 <= (Znth i costs_l 0)) ” 
  &&  “ ((Znth i costs_l 0) <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) seen_l 0)) ” 
  &&  “ ((Znth (Znth i colors_l 0) seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) good_l 0)) ” 
  &&  “ ((Znth (Znth i colors_l 0) good_l 0) <= i) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth (Znth i colors_l 0) seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) (PreH16 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH17 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH18 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l_2 0)) /\ ((Znth idx_7 seen_l_2 0) <= i)))) (PreH19 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l_2 0)) /\ ((Znth idx_8 good_l_2 0) <= i)))) ,
  TT && emp 
|--
  EX (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (Znth i colors_l 0)) ” 
  &&  “ ((Znth i colors_l 0) < k_pre) ” 
  &&  “ (0 <= (Znth i costs_l 0)) ” 
  &&  “ ((Znth i costs_l 0) <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) seen_l_2 0)) ” 
  &&  “ ((Znth (Znth i colors_l 0) seen_l_2 0) <= i) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) good_l_2 0)) ” 
  &&  “ ((Znth (Znth i colors_l 0) good_l_2 0) <= i) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) seen_l_2 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l_2 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l_2 0)) /\ ((Znth idx_3 seen_l_2 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= i))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_4 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l_2 0))) (PreH23 : ((Znth c good_l_2 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l_2 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) (PreH29 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH30 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH31 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l 0)) /\ ((Znth idx_7 seen_l 0) <= i)))) (PreH32 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l_2 0)) /\ ((Znth idx_8 good_l_2 0) <= i)))) ,
  (IntArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (ans: Z)  (seen_l_2: (@list Z))  (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c seen_l 0) )) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2))) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l 0) ) - (Znth c seen_l_2 0) ) seen_l_2 good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next 0)) /\ ((Znth idx_3 seen_next 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l_2 0))) (PreH23 : ((Znth c good_l_2 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l_2 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) (PreH29 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH30 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH31 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l 0)) /\ ((Znth idx_7 seen_l 0) <= i)))) (PreH32 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l_2 0)) /\ ((Znth idx_8 good_l_2 0) <= i)))) ,
  TT && emp 
|--
  EX (ans: Z)  (seen_l_2: (@list Z)) ,
  “ ((replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2))) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c seen_l 0) )) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l 0) ) - (Znth c seen_l_2 0) ) seen_l_2 good_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) 0)) /\ ((Znth idx_3 (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= i))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_5 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 seen_next_2 0)) /\ ((Znth idx_4 seen_next_2 0) <= 200000)))) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : (0 <= cost)) (PreH11 : (cost <= p_pre)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : ((Zlength (seen_next_2)) = k_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH22 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH23 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH24 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH25 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH26 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_next_2 0)) /\ ((Znth idx_7 seen_next_2 0) <= (i + 1 ))))) (PreH27 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l 0)) /\ ((Znth idx_8 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_next_2 )
  **  (IntArray.full good_pre k_pre seen_next_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (ans: Z)  (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next 0)) /\ ((Znth idx_3 seen_next 0) <= (i + 1 )))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre seen_next )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 seen_next_2 0)) /\ ((Znth idx_4 seen_next_2 0) <= 200000)))) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : (0 <= cost)) (PreH11 : (cost <= p_pre)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : ((Zlength (seen_next_2)) = k_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH22 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH23 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH24 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH25 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH26 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_next_2 0)) /\ ((Znth idx_7 seen_next_2 0) <= (i + 1 ))))) (PreH27 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l 0)) /\ ((Znth idx_8 good_l 0) <= i)))) ,
  TT && emp 
|--
  EX (ans: Z) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength (seen_next_2)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next_2 seen_next_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next_2 0)) /\ ((Znth idx_3 seen_next_2 0) <= (i + 1 )))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_6 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l_2 0))) (PreH21 : ((Znth c seen_l_2 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l_2 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) (PreH29 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH30 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH31 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l_2 0)) /\ ((Znth idx_7 seen_l_2 0) <= i)))) (PreH32 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l 0)) /\ ((Znth idx_8 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (ans: Z)  (seen_l: (@list Z))  (good_l_2: (@list Z))  (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ (p_pre < cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ ((Zlength (good_l_2)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c good_l 0) )) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l 0) ) - (Znth c good_l_2 0) ) seen_l good_l_2 ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre (answer + (Znth c good_l 0) ) seen_next good_l_2 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_next 0)) /\ ((Znth idx_3 seen_next 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= (i + 1 )))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l_2 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l_2 0))) (PreH21 : ((Znth c seen_l_2 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l_2 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) (PreH29 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH30 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH31 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_l_2 0)) /\ ((Znth idx_7 seen_l_2 0) <= i)))) (PreH32 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l 0)) /\ ((Znth idx_8 good_l 0) <= i)))) ,
  TT && emp 
|--
  EX (ans: Z)  (seen_l: (@list Z)) ,
  “ ((replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ (p_pre < cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) = k_pre) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c good_l 0) )) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l 0) ) - (Znth c good_l 0) ) seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre (answer + (Znth c good_l 0) ) (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) 0)) /\ ((Znth idx_3 (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= (i + 1 )))) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_7_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : ((Zlength (seen_next)) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH19 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) (PreH20 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH21 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH22 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_next 0)) /\ ((Znth idx_7 seen_next 0) <= (i + 1 ))))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre seen_next )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z))  (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= (i + 1 )))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_entail_wit_7_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans_2: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : (p_pre < cost)) (PreH10 : (cost <= 100)) (PreH11 : ((Zlength (colors_l)) = n_pre)) (PreH12 : ((Zlength (costs_l)) = n_pre)) (PreH13 : ((Zlength (seen_next)) = k_pre)) (PreH14 : ((Zlength (good_l_2)) = k_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) (PreH22 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans_2 )) (PreH23 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l_2 0) ) seen_l_2 good_l_2 )) (PreH24 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l_2 )) (PreH25 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> ((0 <= (Znth idx_5 colors_l 0)) /\ ((Znth idx_5 colors_l 0) < k_pre)))) (PreH26 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < n_pre)) -> ((0 <= (Znth idx_6 costs_l 0)) /\ ((Znth idx_6 costs_l 0) <= 100)))) (PreH27 : forall (idx_7: Z) , (((0 <= idx_7) /\ (idx_7 < k_pre)) -> ((0 <= (Znth idx_7 seen_next 0)) /\ ((Znth idx_7 seen_next 0) <= (i + 1 ))))) (PreH28 : forall (idx_8: Z) , (((0 <= idx_8) /\ (idx_8 < k_pre)) -> ((0 <= (Znth idx_8 good_l_2 0)) /\ ((Znth idx_8 good_l_2 0) <= (i + 1 ))))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z))  (ans: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= (i + 1 )))) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_entail_wit_8 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) (PreH16 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH18 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l_2 0)) /\ ((Znth idx_3 seen_l_2 0) <= i)))) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) (PreH16 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH18 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l_2 0)) /\ ((Znth idx_3 seen_l_2 0) <= i)))) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= i)))) ,
  TT && emp 
|--
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_8_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (ans: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) (PreH16 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH18 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l_2 0)) /\ ((Znth idx_3 seen_l_2 0) <= i)))) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l_2 0)) /\ ((Znth idx_4 good_l_2 0) <= i)))) ,
  TT && emp 
|--
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
.

Definition countChoosingInns_return_wit_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 19999900000)) (PreH11 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_1_pure := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (ans: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH10 : (0 <= ans)) (PreH11 : (ans <= 19999900000)) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH13 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) ,
  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ”
.

Definition countChoosingInns_partial_solve_wit_1_aux := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (ans: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH10 : (0 <= ans)) (PreH11 : (ans <= 19999900000)) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH13 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 19999900000) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ”
  &&  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_1 := countChoosingInns_partial_solve_wit_1_pure -> countChoosingInns_partial_solve_wit_1_aux.

Definition countChoosingInns_partial_solve_wit_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH16 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH18 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((colors_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i colors_l 0))
  **  (IntArray.missing_i colors_pre i 0 n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_3 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 19999900000)) (PreH14 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH16 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH18 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((costs_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i costs_l 0))
  **  (IntArray.missing_i costs_pre i 0 n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_4 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((seen_pre + (c * sizeof(INT) ) )) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_5 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((seen_pre + (c * sizeof(INT) ) )) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_6 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((seen_pre + (c * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_7_pure := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= p_pre)) (PreH11 : ((Zlength (colors_l)) = n_pre)) (PreH12 : ((Zlength (costs_l)) = n_pre)) (PreH13 : ((Zlength (seen_next)) = k_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= c)) (PreH17 : (c < k_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH21 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH22 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH23 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH24 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) (PreH25 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < k_pre)) -> ((0 <= (Znth idx_5 seen_next 0)) /\ ((Znth idx_5 seen_next 0) <= (i + 1 ))))) (PreH26 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < k_pre)) -> ((0 <= (Znth idx_6 good_l 0)) /\ ((Znth idx_6 good_l 0) <= i)))) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_next 0)) /\ ((Znth idx seen_next 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_l 0)) /\ ((Znth idx_2 good_l 0) <= 200000))) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ”
) \/
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (p_pre <= INT_MAX)) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (cost >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (c >= INT_MIN)) (PreH10 : (p_pre >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (c = (Znth i colors_l 0))) (PreH14 : (cost = (Znth i costs_l 0))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 50)) (PreH19 : (0 <= p_pre)) (PreH20 : (p_pre <= 100)) (PreH21 : (0 <= cost)) (PreH22 : (cost <= p_pre)) (PreH23 : ((Zlength (colors_l)) = n_pre)) (PreH24 : ((Zlength (costs_l)) = n_pre)) (PreH25 : ((Zlength (seen_next)) = k_pre)) (PreH26 : (0 <= i)) (PreH27 : (i < n_pre)) (PreH28 : (0 <= c)) (PreH29 : (c < k_pre)) (PreH30 : (0 <= answer)) (PreH31 : (answer <= 19999900000)) (PreH32 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH33 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH34 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH35 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH36 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) (PreH37 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < k_pre)) -> ((0 <= (Znth idx_5 seen_next 0)) /\ ((Znth idx_5 seen_next 0) <= (i + 1 ))))) (PreH38 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < k_pre)) -> ((0 <= (Znth idx_6 good_l 0)) /\ ((Znth idx_6 good_l 0) <= i)))) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ ((Zlength (good_l)) = k_pre) ”
).

Definition countChoosingInns_partial_solve_wit_7_pure_split_goal_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (c <= INT_MAX)) (PreH4 : (p_pre <= INT_MAX)) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (cost >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (c >= INT_MIN)) (PreH10 : (p_pre >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (c = (Znth i colors_l 0))) (PreH14 : (cost = (Znth i costs_l 0))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 50)) (PreH19 : (0 <= p_pre)) (PreH20 : (p_pre <= 100)) (PreH21 : (0 <= cost)) (PreH22 : (cost <= p_pre)) (PreH23 : ((Zlength (colors_l)) = n_pre)) (PreH24 : ((Zlength (costs_l)) = n_pre)) (PreH25 : ((Zlength (seen_next)) = k_pre)) (PreH26 : (0 <= i)) (PreH27 : (i < n_pre)) (PreH28 : (0 <= c)) (PreH29 : (c < k_pre)) (PreH30 : (0 <= answer)) (PreH31 : (answer <= 19999900000)) (PreH32 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH33 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH34 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH35 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH36 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) (PreH37 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < k_pre)) -> ((0 <= (Znth idx_5 seen_next 0)) /\ ((Znth idx_5 seen_next 0) <= (i + 1 ))))) (PreH38 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < k_pre)) -> ((0 <= (Znth idx_6 good_l 0)) /\ ((Znth idx_6 good_l 0) <= i)))) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ ((Zlength (good_l)) = k_pre) ”
.

Definition countChoosingInns_partial_solve_wit_7_aux := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= p_pre)) (PreH11 : ((Zlength (colors_l)) = n_pre)) (PreH12 : ((Zlength (costs_l)) = n_pre)) (PreH13 : ((Zlength (seen_next)) = k_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= c)) (PreH17 : (c < k_pre)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH21 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH22 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH23 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre)))) (PreH24 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100)))) (PreH25 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < k_pre)) -> ((0 <= (Znth idx_5 seen_next 0)) /\ ((Znth idx_5 seen_next 0) <= (i + 1 ))))) (PreH26 : forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < k_pre)) -> ((0 <= (Znth idx_6 good_l 0)) /\ ((Znth idx_6 good_l 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < k_pre)) -> ((0 <= (Znth idx seen_next 0)) /\ ((Znth idx seen_next 0) <= 200000))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < k_pre)) -> ((0 <= (Znth idx_2 good_l 0)) /\ ((Znth idx_2 good_l 0) <= 200000))) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> ((0 <= (Znth idx_3 colors_l 0)) /\ ((Znth idx_3 colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> ((0 <= (Znth idx_4 costs_l 0)) /\ ((Znth idx_4 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < k_pre)) -> ((0 <= (Znth idx_5 seen_next 0)) /\ ((Znth idx_5 seen_next 0) <= (i + 1 )))) ” 
  &&  “ forall (idx_6: Z) , (((0 <= idx_6) /\ (idx_6 < k_pre)) -> ((0 <= (Znth idx_6 good_l 0)) /\ ((Znth idx_6 good_l 0) <= i))) ”
  &&  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_7 := countChoosingInns_partial_solve_wit_7_pure -> countChoosingInns_partial_solve_wit_7_aux.

Definition countChoosingInns_partial_solve_wit_8 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((good_pre + (c * sizeof(INT) ) )) # Int  |-> (Znth c good_l 0))
  **  (IntArray.missing_i good_pre c 0 k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
.

Definition countChoosingInns_partial_solve_wit_9 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((seen_pre + (c * sizeof(INT) ) )) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_10 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (ans: Z) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= cost)) (PreH17 : (cost <= 100)) (PreH18 : (0 <= answer)) (PreH19 : (answer <= 19999900000)) (PreH20 : (0 <= (Znth c seen_l 0))) (PreH21 : ((Znth c seen_l 0) <= i)) (PreH22 : (0 <= (Znth c good_l 0))) (PreH23 : ((Znth c good_l 0) <= i)) (PreH24 : ((answer + (Znth c seen_l 0) ) <= 9223372036854775807)) (PreH25 : ((answer + (Znth c good_l 0) ) <= 9223372036854775807)) (PreH26 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH27 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans )) (PreH28 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) (PreH29 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre)))) (PreH30 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100)))) (PreH31 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i)))) (PreH32 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i)))) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (Znth c seen_l 0)) ” 
  &&  “ ((Znth c seen_l 0) <= i) ” 
  &&  “ (0 <= (Znth c good_l 0)) ” 
  &&  “ ((Znth c good_l 0) <= i) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 9223372036854775807) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 9223372036854775807) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre ans ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((0 <= (Znth idx colors_l 0)) /\ ((Znth idx colors_l 0) < k_pre))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> ((0 <= (Znth idx_2 costs_l 0)) /\ ((Znth idx_2 costs_l 0) <= 100))) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < k_pre)) -> ((0 <= (Znth idx_3 seen_l 0)) /\ ((Znth idx_3 seen_l 0) <= i))) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < k_pre)) -> ((0 <= (Znth idx_4 good_l 0)) /\ ((Znth idx_4 good_l 0) <= i))) ”
  &&  (((seen_pre + (c * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_initCounts_safety_wit_1 : initCounts_safety_wit_1.
Axiom proof_of_initCounts_safety_wit_2 : initCounts_safety_wit_2.
Axiom proof_of_initCounts_safety_wit_3 : initCounts_safety_wit_3.
Axiom proof_of_initCounts_safety_wit_4 : initCounts_safety_wit_4.
Axiom proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Axiom proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Axiom proof_of_initCounts_entail_wit_3 : initCounts_entail_wit_3.
Axiom proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Axiom proof_of_initCounts_partial_solve_wit_1 : initCounts_partial_solve_wit_1.
Axiom proof_of_initCounts_partial_solve_wit_2 : initCounts_partial_solve_wit_2.
Axiom proof_of_copyCounts_safety_wit_1 : copyCounts_safety_wit_1.
Axiom proof_of_copyCounts_safety_wit_2 : copyCounts_safety_wit_2.
Axiom proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Axiom proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Axiom proof_of_copyCounts_entail_wit_3 : copyCounts_entail_wit_3.
Axiom proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Axiom proof_of_copyCounts_partial_solve_wit_1 : copyCounts_partial_solve_wit_1.
Axiom proof_of_copyCounts_partial_solve_wit_2 : copyCounts_partial_solve_wit_2.
Axiom proof_of_countChoosingInns_safety_wit_1 : countChoosingInns_safety_wit_1.
Axiom proof_of_countChoosingInns_safety_wit_2 : countChoosingInns_safety_wit_2.
Axiom proof_of_countChoosingInns_safety_wit_3 : countChoosingInns_safety_wit_3.
Axiom proof_of_countChoosingInns_safety_wit_4 : countChoosingInns_safety_wit_4.
Axiom proof_of_countChoosingInns_safety_wit_5 : countChoosingInns_safety_wit_5.
Axiom proof_of_countChoosingInns_safety_wit_6 : countChoosingInns_safety_wit_6.
Axiom proof_of_countChoosingInns_safety_wit_7 : countChoosingInns_safety_wit_7.
Axiom proof_of_countChoosingInns_safety_wit_8 : countChoosingInns_safety_wit_8.
Axiom proof_of_countChoosingInns_safety_wit_9 : countChoosingInns_safety_wit_9.
Axiom proof_of_countChoosingInns_safety_wit_10 : countChoosingInns_safety_wit_10.
Axiom proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Axiom proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Axiom proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Axiom proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Axiom proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Axiom proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Axiom proof_of_countChoosingInns_entail_wit_7_1 : countChoosingInns_entail_wit_7_1.
Axiom proof_of_countChoosingInns_entail_wit_7_2 : countChoosingInns_entail_wit_7_2.
Axiom proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Axiom proof_of_countChoosingInns_return_wit_1 : countChoosingInns_return_wit_1.
Axiom proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure.
Axiom proof_of_countChoosingInns_partial_solve_wit_1 : countChoosingInns_partial_solve_wit_1.
Axiom proof_of_countChoosingInns_partial_solve_wit_2 : countChoosingInns_partial_solve_wit_2.
Axiom proof_of_countChoosingInns_partial_solve_wit_3 : countChoosingInns_partial_solve_wit_3.
Axiom proof_of_countChoosingInns_partial_solve_wit_4 : countChoosingInns_partial_solve_wit_4.
Axiom proof_of_countChoosingInns_partial_solve_wit_5 : countChoosingInns_partial_solve_wit_5.
Axiom proof_of_countChoosingInns_partial_solve_wit_6 : countChoosingInns_partial_solve_wit_6.
Axiom proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure.
Axiom proof_of_countChoosingInns_partial_solve_wit_7 : countChoosingInns_partial_solve_wit_7.
Axiom proof_of_countChoosingInns_partial_solve_wit_8 : countChoosingInns_partial_solve_wit_8.
Axiom proof_of_countChoosingInns_partial_solve_wit_9 : countChoosingInns_partial_solve_wit_9.
Axiom proof_of_countChoosingInns_partial_solve_wit_10 : countChoosingInns_partial_solve_wit_10.

End VC_Correct.
