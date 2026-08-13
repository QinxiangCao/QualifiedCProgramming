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

(*----- Function initCounts -----*)

Definition initCounts_safety_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
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
  (CountsZeroPrefix (@nil Z) 0 )
.

Definition initCounts_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (CountsZeroPrefix (@nil Z) 0 )
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
  (CountsZeroPrefix (app (good_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) )
.

Definition initCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (CountsZeroPrefix (app (seen_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) )
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
  &&  (((seen_pre + (i * sizeof(INT)))) # Int  |->_)
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
  &&  (((good_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
.

(*----- Function copyCounts -----*)

Definition copyCounts_safety_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition copyCounts_safety_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (0 <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountArraySafe seen_l k_pre 200000 )) (PreH6 : (CountArraySafe good_old k_pre 200000 )) (PreH7 : (CountArraySafe good_cur k_pre 200000 )) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre )) ,
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
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_old )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (CountArraySafe seen_l k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_old k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_cur k_pre 200000 ) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur 0 k_pre ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old good_old 0 k_pre ) ”
  &&  emp
).

Definition copyCounts_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  (CopyCountsPrefix seen_l good_old good_old 0 k_pre )
.

Definition copyCounts_entail_wit_2 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (IntArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < k_pre) ” 
  &&  “ (CountArraySafe seen_l k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_old k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_cur k_pre 200000 ) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ) ” 
  &&  “ (CountArraySafe (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) k_pre 200000 ) ”
  &&  emp
).

Definition copyCounts_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre )
.

Definition copyCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (CountArraySafe (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) k_pre 200000 )
.

Definition copyCounts_entail_wit_3 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (0 <= i)) (PreH4 : (i < k_pre)) (PreH5 : (CountArraySafe seen_l k_pre 200000 )) (PreH6 : (CountArraySafe good_old k_pre 200000 )) (PreH7 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH8 : (CopyCountsPrefix seen_l good_old good_cur_2 (i + 1 ) k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur_2 )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (CountArraySafe seen_l k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_old k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_cur k_pre 200000 ) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur (i + 1 ) k_pre ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
.

Definition copyCounts_return_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (CountArraySafe seen_l k_pre 200000 ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre seen_l )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp
).

Definition copyCounts_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  (good_cur = seen_l)
.

Definition copyCounts_partial_solve_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CountArraySafe seen_l k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_old k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_cur k_pre 200000 ) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre ) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int  |-> (Znth i seen_l 0))
  **  (IntArray.missing_i seen_pre i 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
.

Definition copyCounts_partial_solve_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (CountArraySafe seen_l k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_old k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_cur k_pre 200000 ) ” 
  &&  “ (CopyCountsPrefix seen_l good_old good_cur i k_pre ) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i good_pre i 0 k_pre good_cur )
  **  (IntArray.full seen_pre k_pre seen_l )
.

(*----- Function countChoosingInns -----*)

Definition countChoosingInns_safety_wit_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l )) (PreH4 : (CountsZeroFull k_pre good_l )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l good_l )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (Znth c seen_l 0) )) ”
.

Definition countChoosingInns_safety_wit_4 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (Znth c good_l 0) )) ”
.

Definition countChoosingInns_safety_wit_7 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < k_pre)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= 19999900000)) (PreH10 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next seen_next )) (PreH11 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (p_pre < cost)) (PreH5 : (cost <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < k_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l 0) ) seen_l good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l )) ,
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
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (CountsZeroFull k_pre seen_l ) ” 
  &&  “ (CountsZeroFull k_pre good_l ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_1_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )
.

Definition countChoosingInns_entail_wit_1_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )
.

Definition countChoosingInns_entail_wit_2 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l_2 )) (PreH4 : (CountsZeroFull k_pre good_l_2 )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z)) ,
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l_2 )) (PreH4 : (CountsZeroFull k_pre good_l_2 )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_2_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l_2 )) (PreH4 : (CountsZeroFull k_pre good_l_2 )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) ,
  (0 <= n_pre)
.

Definition countChoosingInns_entail_wit_3 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ ((Znth i colors_l 0) = (Znth i colors_l 0)) ” 
  &&  “ ((Znth i costs_l 0) = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth (Znth i colors_l 0) seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth (Znth i colors_l 0) seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  TT && emp 
|--
  “ (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l_2 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) seen_l_2 0) ) <= INT64_MAX) ” 
  &&  “ ((Znth (Znth i colors_l 0) good_l_2 0) <= i) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) good_l_2 0)) ” 
  &&  “ ((Znth (Znth i colors_l 0) seen_l_2 0) <= i) ” 
  &&  “ (0 <= (Znth (Znth i colors_l 0) seen_l_2 0)) ” 
  &&  “ ((Znth i costs_l 0) <= 100) ” 
  &&  “ (0 <= (Znth i costs_l 0)) ” 
  &&  “ ((Znth i colors_l 0) < k_pre) ” 
  &&  “ (0 <= (Znth i colors_l 0)) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_3_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 ) <= INT_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) good_l_2 0) ) <= INT64_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_3 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) seen_l_2 0) ) <= INT64_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_4 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) good_l_2 0) <= i)
.

Definition countChoosingInns_entail_wit_3_split_goal_5 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) good_l_2 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_6 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) seen_l_2 0) <= i)
.

Definition countChoosingInns_entail_wit_3_split_goal_7 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) seen_l_2 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_8 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i costs_l 0) <= 100)
.

Definition countChoosingInns_entail_wit_3_split_goal_9 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i costs_l 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_10 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i colors_l 0) < k_pre)
.

Definition countChoosingInns_entail_wit_3_split_goal_11 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i colors_l 0))
.

Definition countChoosingInns_entail_wit_4 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l_2 0))) (PreH16 : ((Znth c good_l_2 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l_2 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2 )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) ,
  (IntArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l_2: (@list Z))  (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c seen_l 0) )) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2))) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l 0) ) - (Znth c seen_l_2 0) ) seen_l_2 good_l ) ” 
  &&  “ (CountArraySafe seen_next k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_l k_pre 200000 ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l_2 0))) (PreH16 : ((Znth c good_l_2 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l_2 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2 )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) ,
  TT && emp 
|--
  EX (seen_l_2: (@list Z)) ,
  “ ((replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) = (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 )) (seen_l_2))) ” 
  &&  “ (0 <= (answer + (Znth (Znth i colors_l 0) seen_l 0) )) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) seen_l 0) ) <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 )) (seen_l_2)) good_l_2 ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth (Znth i colors_l 0) seen_l 0) ) - (Znth (Znth i colors_l 0) seen_l_2 0) ) seen_l_2 good_l_2 ) ” 
  &&  “ (CountArraySafe (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 )) (seen_l_2)) k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_l_2 k_pre 200000 ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_5 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  (IntArray.full seen_pre k_pre seen_next_2 )
  **  (IntArray.full good_pre k_pre seen_next_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next seen_next ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre seen_next )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next_2 seen_next_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 seen_next_2 ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_5_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next_2 seen_next_2 )
.

Definition countChoosingInns_entail_wit_5_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 seen_next_2 )
.

Definition countChoosingInns_entail_wit_6 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l_2 0))) (PreH14 : ((Znth c seen_l_2 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l_2 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) ,
  (IntArray.full seen_pre k_pre (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  EX (good_l_2: (@list Z))  (seen_l: (@list Z))  (seen_next: (@list Z)) ,
  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (p_pre < cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c good_l 0) )) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l_2 ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l 0) ) - (Znth c good_l_2 0) ) seen_l good_l_2 ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre (answer + (Znth c good_l 0) ) seen_next good_l_2 ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l_2 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l_2 0))) (PreH14 : ((Znth c seen_l_2 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l_2 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) ,
  TT && emp 
|--
  EX (seen_l: (@list Z)) ,
  “ ((replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 )) (seen_l_2)) = (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (p_pre < (Znth i costs_l 0)) ” 
  &&  “ (0 <= (answer + (Znth (Znth i colors_l 0) good_l 0) )) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l 0) ) <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre ((answer + (Znth (Znth i colors_l 0) good_l 0) ) - (Znth (Znth i colors_l 0) good_l 0) ) seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre (answer + (Znth (Znth i colors_l 0) good_l 0) ) (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) good_l ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_7_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < k_pre)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= 19999900000)) (PreH10 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next seen_next )) (PreH11 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre seen_next )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z)) ,
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_entail_wit_7_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (p_pre < cost)) (PreH5 : (cost <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < k_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l_2 )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c good_l_2 0) ) seen_l_2 good_l_2 )) (PreH16 : (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l_2 )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (seen_l: (@list Z))  (good_l: (@list Z)) ,
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_entail_wit_8 := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l_2 )
  **  (IntArray.full good_pre k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  TT && emp 
|--
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_8_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer )
.

Definition countChoosingInns_return_wit_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH2 : (0 <= answer)) (PreH3 : (answer <= 19999900000)) (PreH4 : (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer )) ,
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
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (k_pre <= 50) ” 
  &&  “ (1 <= k_pre) ”
) \/
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ”
).

Definition countChoosingInns_partial_solve_wit_1_pure_split_goal_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (1 <= k_pre) ”
.

Definition countChoosingInns_partial_solve_wit_1_pure_split_goal_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (p_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (p_pre >= INT_MIN)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (k_pre <= 50) ”
.

Definition countChoosingInns_partial_solve_wit_1_aux := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
|--
  “ (k_pre <= 50) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ”
  &&  (IntArray.undef_full seen_pre k_pre )
  **  (IntArray.undef_full good_pre k_pre )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_1 := countChoosingInns_partial_solve_wit_1_pure -> countChoosingInns_partial_solve_wit_1_aux.

Definition countChoosingInns_partial_solve_wit_2 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (i < n_pre) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |-> (Znth i colors_l 0))
  **  (IntArray.missing_i colors_pre i 0 n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_3 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (i < n_pre) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((costs_pre + (i * sizeof(INT)))) # Int  |-> (Znth i costs_l 0))
  **  (IntArray.missing_i costs_pre i 0 n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_4 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_5 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_6 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost <= p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full good_pre k_pre good_l )
.

Definition countChoosingInns_partial_solve_wit_7_pure := 
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (0 <= cost)) (PreH5 : (cost <= p_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < k_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH16 : (CountArraySafe seen_next k_pre 200000 )) (PreH17 : (CountArraySafe good_l k_pre 200000 )) ,
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
  &&  “ (CountArraySafe seen_next k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_l k_pre 200000 ) ” 
  &&  “ (k_pre <= 50) ”
) \/
(
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (answer <= INT64_MAX)) (PreH2 : (answer >= INT64_MIN)) (PreH3 : (cost <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (p_pre <= INT_MAX)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (cost >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (p_pre >= INT_MIN)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (c = (Znth i colors_l 0))) (PreH16 : (cost = (Znth i costs_l 0))) (PreH17 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH18 : (0 <= cost)) (PreH19 : (cost <= p_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= c)) (PreH23 : (c < k_pre)) (PreH24 : (0 <= answer)) (PreH25 : (answer <= 19999900000)) (PreH26 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH27 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH28 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l )) (PreH29 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH30 : (CountArraySafe seen_next k_pre 200000 )) (PreH31 : (CountArraySafe good_l k_pre 200000 )) ,
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
  “ (k_pre <= 50) ”
).

Definition countChoosingInns_partial_solve_wit_7_pure_split_goal_1 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (answer <= INT64_MAX)) (PreH2 : (answer >= INT64_MIN)) (PreH3 : (cost <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (c <= INT_MAX)) (PreH6 : (p_pre <= INT_MAX)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (cost >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (c >= INT_MIN)) (PreH12 : (p_pre >= INT_MIN)) (PreH13 : (k_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (c = (Znth i colors_l 0))) (PreH16 : (cost = (Znth i costs_l 0))) (PreH17 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH18 : (0 <= cost)) (PreH19 : (cost <= p_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= c)) (PreH23 : (c < k_pre)) (PreH24 : (0 <= answer)) (PreH25 : (answer <= 19999900000)) (PreH26 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH27 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH28 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l )) (PreH29 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH30 : (CountArraySafe seen_next k_pre 200000 )) (PreH31 : (CountArraySafe good_l k_pre 200000 )) ,
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
  “ (k_pre <= 50) ”
.

Definition countChoosingInns_partial_solve_wit_7_aux := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH4 : (0 <= cost)) (PreH5 : (cost <= p_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < k_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 19999900000)) (PreH12 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH13 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l )) (PreH15 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH16 : (CountArraySafe seen_next k_pre 200000 )) (PreH17 : (CountArraySafe good_l k_pre 200000 )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (1 <= k_pre) ” 
  &&  “ (CountArraySafe seen_next k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_l k_pre 200000 ) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l ) ” 
  &&  “ (CountArraySafe seen_next k_pre 200000 ) ” 
  &&  “ (CountArraySafe good_l k_pre 200000 ) ”
  &&  (IntArray.full seen_pre k_pre seen_next )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_7 := countChoosingInns_partial_solve_wit_7_pure -> countChoosingInns_partial_solve_wit_7_aux.

Definition countChoosingInns_partial_solve_wit_8 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((good_pre + (c * sizeof(INT)))) # Int  |-> (Znth c good_l 0))
  **  (IntArray.missing_i good_pre c 0 k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
.

Definition countChoosingInns_partial_solve_wit_9 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_10 := 
forall (good_pre: Z) (seen_pre: Z) (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < k_pre)) (PreH9 : (0 <= cost)) (PreH10 : (cost <= 100)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (0 <= (Znth c seen_l 0))) (PreH14 : ((Znth c seen_l 0) <= i)) (PreH15 : (0 <= (Znth c good_l 0))) (PreH16 : ((Znth c good_l 0) <= i)) (PreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (cost > p_pre) ” 
  &&  “ (c = (Znth i colors_l 0)) ” 
  &&  “ (cost = (Znth i costs_l 0)) ” 
  &&  “ (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre ) ” 
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
  &&  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l ) ” 
  &&  “ (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((seen_pre + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i seen_pre c 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Module Type VC_Correct.


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
