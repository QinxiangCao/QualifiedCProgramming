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
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (eq (0)) seen_l )) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (eq (0)) good_l )) ,
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
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (eq (0)) seen_l )) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (eq (0)) good_l )) ,
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
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (eq (0)) seen_l )) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (eq (0)) good_l )) ,
  (IntArray.seg good_pre 0 (i + 1 ) (app (good_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
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
  &&  “ ((Zlength (seen_l)) = 0) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = 0) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (IntArray.seg seen_pre 0 0 seen_l )
  **  (IntArray.undef_seg seen_pre 0 k_pre )
  **  (IntArray.seg good_pre 0 0 good_l )
  **  (IntArray.undef_seg good_pre 0 k_pre )
) \/
(
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition initCounts_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (Forall (eq (0)) (@nil Z) )
.

Definition initCounts_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition initCounts_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (Forall (eq (0)) (@nil Z) )
.

Definition initCounts_entail_wit_1_split_goal_4 := 
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition initCounts_entail_wit_2 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  (IntArray.seg good_pre 0 (i + 1 ) (app (good_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ ((Zlength (seen_l)) = (i + 1 )) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = (i + 1 )) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (IntArray.seg seen_pre 0 (i + 1 ) seen_l )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 (i + 1 ) good_l )
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
) \/
(
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (good_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (good_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (Forall (eq (0)) (app (seen_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (seen_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition initCounts_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  (Forall (eq (0)) (app (good_l_2) ((cons (0) ((@nil Z))))) )
.

Definition initCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  ((Zlength ((app (good_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition initCounts_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  (Forall (eq (0)) (app (seen_l_2) ((cons (0) ((@nil Z))))) )
.

Definition initCounts_entail_wit_2_split_goal_4 := 
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  ((Zlength ((app (seen_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition initCounts_return_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  (IntArray.seg seen_pre 0 i seen_l_2 )
  **  (IntArray.undef_seg seen_pre i k_pre )
  **  (IntArray.seg good_pre 0 i good_l_2 )
  **  (IntArray.undef_seg good_pre i k_pre )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
) \/
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (eq (0)) seen_l_2 )) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (eq (0)) good_l_2 )) ,
  (IntArray.seg seen_pre 0 i seen_l_2 )
  **  (IntArray.seg good_pre 0 i good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l )
).

Definition initCounts_partial_solve_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (eq (0)) seen_l )) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (eq (0)) good_l )) ,
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
  &&  “ ((Zlength (seen_l)) = i) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = i) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 i seen_l )
  **  (IntArray.seg good_pre 0 i good_l )
  **  (IntArray.undef_seg good_pre i k_pre )
.

Definition initCounts_partial_solve_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (eq (0)) seen_l )) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (eq (0)) good_l )) ,
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
  &&  “ ((Zlength (seen_l)) = i) ” 
  &&  “ (Forall (eq (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = i) ” 
  &&  “ (Forall (eq (0)) good_l ) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg good_pre (i + 1 ) k_pre )
  **  (IntArray.seg seen_pre 0 (i + 1 ) (app (seen_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg seen_pre (i + 1 ) k_pre )
  **  (IntArray.seg good_pre 0 i good_l )
.

(*----- Function copyCounts -----*)

Definition copyCounts_safety_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall (Z.le (0)) seen_l )) (PreH5 : (Forall (Z.ge (200000)) seen_l )) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall (Z.le (0)) good_old )) (PreH8 : (Forall (Z.ge (200000)) good_old )) ,
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
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l 0)) (good_cur)) )
  **  (IntArray.full seen_pre k_pre seen_l )
  **  ((( &( "seen" ) )) # Ptr  |-> seen_pre)
  **  ((( &( "good" ) )) # Ptr  |-> good_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition copyCounts_entail_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall (Z.le (0)) seen_l )) (PreH5 : (Forall (Z.ge (200000)) seen_l )) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall (Z.le (0)) good_old )) (PreH8 : (Forall (Z.ge (200000)) good_old )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_old )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_l ) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_old ) ” 
  &&  “ (Forall (Z.ge (200000)) good_old ) ” 
  &&  “ ((Zlength (good_cur)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_cur ) ” 
  &&  “ (Forall (Z.ge (200000)) good_cur ) ” 
  &&  “ (InnsCopiedPrefix seen_l good_old good_cur 0 k_pre ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall (Z.le (0)) seen_l )) (PreH5 : (Forall (Z.ge (200000)) seen_l )) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall (Z.le (0)) good_old )) (PreH8 : (Forall (Z.ge (200000)) good_old )) ,
  TT && emp 
|--
  “ (InnsCopiedPrefix seen_l good_old good_old 0 k_pre ) ”
  &&  emp
).

Definition copyCounts_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall (Z.le (0)) seen_l )) (PreH5 : (Forall (Z.ge (200000)) seen_l )) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall (Z.le (0)) good_old )) (PreH8 : (Forall (Z.ge (200000)) good_old )) ,
  (InnsCopiedPrefix seen_l good_old good_old 0 k_pre )
.

Definition copyCounts_entail_wit_2 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (IntArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) )
  **  (IntArray.full seen_pre k_pre seen_l )
|--
  EX (good_cur: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_l ) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_old ) ” 
  &&  “ (Forall (Z.ge (200000)) good_old ) ” 
  &&  “ ((Zlength (good_cur)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_cur ) ” 
  &&  “ (Forall (Z.ge (200000)) good_cur ) ” 
  &&  “ (InnsCopiedPrefix seen_l good_old good_cur (i + 1 ) k_pre ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  TT && emp 
|--
  “ (InnsCopiedPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.ge (200000)) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)))) = k_pre) ”
  &&  emp
).

Definition copyCounts_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (InnsCopiedPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre )
.

Definition copyCounts_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (Forall (Z.ge (200000)) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) )
.

Definition copyCounts_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (Forall (Z.le (0)) (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) )
.

Definition copyCounts_entail_wit_2_split_goal_4 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur_2 )) (PreH14 : (Forall (Z.ge (200000)) good_cur_2 )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre )) ,
  ((Zlength ((replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)))) = k_pre)
.

Definition copyCounts_return_wit_1 := 
(
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre seen_l )
) \/
(
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp
).

Definition copyCounts_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  (good_cur = seen_l)
.

Definition copyCounts_partial_solve_wit_1 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_l ) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_old ) ” 
  &&  “ (Forall (Z.ge (200000)) good_old ) ” 
  &&  “ ((Zlength (good_cur)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_cur ) ” 
  &&  “ (Forall (Z.ge (200000)) good_cur ) ” 
  &&  “ (InnsCopiedPrefix seen_l good_old good_cur i k_pre ) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int  |-> (Znth i seen_l 0))
  **  (IntArray.missing_i seen_pre i 0 k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
.

Definition copyCounts_partial_solve_wit_2 := 
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall (Z.le (0)) seen_l )) (PreH8 : (Forall (Z.ge (200000)) seen_l )) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall (Z.le (0)) good_old )) (PreH11 : (Forall (Z.ge (200000)) good_old )) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall (Z.le (0)) good_cur )) (PreH14 : (Forall (Z.ge (200000)) good_cur )) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre )) ,
  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_cur )
|--
  “ (i < k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_l ) ” 
  &&  “ ((Zlength (good_old)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_old ) ” 
  &&  “ (Forall (Z.ge (200000)) good_old ) ” 
  &&  “ ((Zlength (good_cur)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_cur ) ” 
  &&  “ (Forall (Z.ge (200000)) good_cur ) ” 
  &&  “ (InnsCopiedPrefix seen_l good_old good_cur i k_pre ) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i good_pre i 0 k_pre good_cur )
  **  (IntArray.full seen_pre k_pre seen_l )
.

(*----- Function countChoosingInns -----*)

Definition countChoosingInns_safety_wit_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall (Z.le (0)) colors_l )) (PreH10 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH11 : (Forall (Z.le (0)) costs_l )) (PreH12 : (Forall (Z.ge (100)) costs_l )) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  (IntArray.undef_full ( &( "good" ) ) 50 )
  **  (IntArray.undef_full ( &( "seen" ) ) 50 )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_3 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_4 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (good_l: (@list Z)) (seen_l: (@list Z)) (PreH1 : ((Zlength (seen_l)) = k_pre)) (PreH2 : (Forall (eq (0)) seen_l )) (PreH3 : ((Zlength (good_l)) = k_pre)) (PreH4 : (Forall (eq (0)) good_l )) (PreH5 : (answer = 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : (0 <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall (Z.le (0)) colors_l )) (PreH15 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH16 : (Forall (Z.le (0)) costs_l )) (PreH17 : (Forall (Z.ge (100)) costs_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_l )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_5 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ ((answer + (Znth c seen_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (Znth c seen_l 0) )) ”
.

Definition countChoosingInns_safety_wit_6 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c seen_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth c seen_l 0) + 1 )) ”
.

Definition countChoosingInns_safety_wit_7 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c seen_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition countChoosingInns_safety_wit_8 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next )) (PreH45 : (Forall (Z.ge (200000)) seen_next )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_9 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next )) (PreH45 : (Forall (Z.ge (200000)) seen_next )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition countChoosingInns_safety_wit_10 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ ((answer + (Znth c good_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (Znth c good_l 0) )) ”
.

Definition countChoosingInns_safety_wit_11 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c good_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (((Znth c seen_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth c seen_l 0) + 1 )) ”
.

Definition countChoosingInns_safety_wit_12 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (Znth c good_l 0) ))
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition countChoosingInns_safety_wit_13 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (0 <= (i + 1 ))) (PreH22 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH23 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH24 : ((Zlength (seen_next)) = k_pre)) (PreH25 : (Forall (Z.le (0)) seen_next )) (PreH26 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH27 : ((Zlength (seen_next)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_next )) (PreH29 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH30 : (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre seen_next )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition countChoosingInns_safety_wit_14 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (p_pre < cost)) (PreH16 : (cost <= 100)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c good_l 0) ) seen_l good_l )) (PreH43 : (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition countChoosingInns_entail_wit_1 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall (Z.le (0)) colors_l )) (PreH10 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH11 : (Forall (Z.le (0)) costs_l )) (PreH12 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.undef_full ( &( "good" ) ) 50 )
  **  (IntArray.undef_full ( &( "seen" ) ) 50 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall (Z.le (0)) colors_l )) (PreH10 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH11 : (Forall (Z.le (0)) costs_l )) (PreH12 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.undef_full ( &( "good" ) ) 50 )
  **  (IntArray.undef_full ( &( "seen" ) ) 50 )
|--
  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
).

Definition countChoosingInns_entail_wit_1_split_goal_spatial := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : (0 <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall (Z.le (0)) colors_l )) (PreH10 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH11 : (Forall (Z.le (0)) costs_l )) (PreH12 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.undef_full ( &( "good" ) ) 50 )
  **  (IntArray.undef_full ( &( "seen" ) ) 50 )
|--
  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_entail_wit_2 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : ((Zlength (seen_l_2)) = k_pre)) (PreH2 : (Forall (eq (0)) seen_l_2 )) (PreH3 : ((Zlength (good_l_2)) = k_pre)) (PreH4 : (Forall (eq (0)) good_l_2 )) (PreH5 : (answer = 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : (0 <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall (Z.le (0)) colors_l )) (PreH15 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH16 : (Forall (Z.le (0)) costs_l )) (PreH17 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_l_2 )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (0)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l 0 k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : ((Zlength (seen_l_2)) = k_pre)) (PreH2 : (Forall (eq (0)) seen_l_2 )) (PreH3 : ((Zlength (good_l_2)) = k_pre)) (PreH4 : (Forall (eq (0)) good_l_2 )) (PreH5 : (answer = 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : (0 <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall (Z.le (0)) colors_l )) (PreH15 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH16 : (Forall (Z.le (0)) costs_l )) (PreH17 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_l_2 )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l_2 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (0)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (0)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l 0 k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
).

Definition countChoosingInns_entail_wit_3 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l_2 )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l_2 )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
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
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 ) <= INT_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) good_l_2 0) ) <= INT64_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_3 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) seen_l_2 0) ) <= INT64_MAX)
.

Definition countChoosingInns_entail_wit_3_split_goal_4 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) good_l_2 0) <= i)
.

Definition countChoosingInns_entail_wit_3_split_goal_5 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) good_l_2 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_6 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) seen_l_2 0) <= i)
.

Definition countChoosingInns_entail_wit_3_split_goal_7 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) seen_l_2 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_8 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i costs_l 0) <= 100)
.

Definition countChoosingInns_entail_wit_3_split_goal_9 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i costs_l 0))
.

Definition countChoosingInns_entail_wit_3_split_goal_10 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i colors_l 0) < k_pre)
.

Definition countChoosingInns_entail_wit_3_split_goal_11 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l_2 )) (PreH23 : (Forall (Z.ge (i)) seen_l_2 )) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l_2 )) (PreH26 : (Forall (Z.ge (i)) good_l_2 )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i colors_l 0))
.

Definition countChoosingInns_entail_wit_4 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l_2 0))) (PreH27 : ((Znth c good_l_2 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l_2 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l_2)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l_2 )) (PreH39 : (Forall (Z.ge (i)) good_l_2 )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) ,
  (IntArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l_2 )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  EX (good_l: (@list Z))  (seen_l_2: (@list Z))  (seen_next: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c seen_l 0) )) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l_2)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l_2 ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l_2 ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l 0) ) - (Znth c seen_l_2 0) ) seen_l_2 good_l ) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (200000)) good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l_2 0))) (PreH27 : ((Znth c good_l_2 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l_2 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l_2)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l_2 )) (PreH39 : (Forall (Z.ge (i)) good_l_2 )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) ,
  (IntArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)) )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l_2: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c seen_l 0) )) ” 
  &&  “ ((answer + (Znth c seen_l 0) ) <= 19999900000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l_2)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l_2 ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l_2 ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l 0) ) - (Znth c seen_l_2 0) ) seen_l_2 good_l ) ” 
  &&  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) ) ” 
  &&  “ (Forall (Z.ge (200000)) (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (200000)) good_l ) ”
  &&  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
).

Definition countChoosingInns_entail_wit_5 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next_2)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next_2 )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next_2 )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next_2)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next_2 )) (PreH45 : (Forall (Z.ge (200000)) seen_next_2 )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next_2 )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre seen_next_2 )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  EX (seen_next: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre seen_next )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next_2)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next_2 )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next_2 )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next_2)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next_2 )) (PreH45 : (Forall (Z.ge (200000)) seen_next_2 )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next_2 )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre seen_next_2 )
|--
  EX (seen_next: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next ) ”
  &&  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre seen_next )
).

Definition countChoosingInns_entail_wit_6 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l_2 0))) (PreH25 : ((Znth c seen_l_2 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l_2 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l_2)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l_2 )) (PreH36 : (Forall (Z.ge (i)) seen_l_2 )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)) )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  EX (good_l_2: (@list Z))  (seen_l: (@list Z))  (seen_next: (@list Z)) ,
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (p_pre < cost) ” 
  &&  “ (cost <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (answer + (Znth c good_l 0) )) ” 
  &&  “ ((answer + (Znth c good_l 0) ) <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l_2)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l_2 ) ” 
  &&  “ (Forall (Z.ge (i)) good_l_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ ((Zlength (good_l_2)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l_2 ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l_2 ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l 0) ) - (Znth c good_l_2 0) ) seen_l good_l_2 ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre (answer + (Znth c good_l 0) ) seen_next good_l_2 ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l_2 )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l_2 0))) (PreH25 : ((Znth c seen_l_2 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l_2 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l_2)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l_2 )) (PreH36 : (Forall (Z.ge (i)) seen_l_2 )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) ,
  TT && emp 
|--
  EX (seen_l: (@list Z)) ,
  “ ((replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 )) (seen_l_2)) = (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (p_pre < (Znth i costs_l 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= (answer + (Znth (Znth i colors_l 0) good_l 0) )) ” 
  &&  “ ((answer + (Znth (Znth i colors_l 0) good_l 0) ) <= 19999900000) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((Zlength (seen_l)) = (Zlength (seen_l_2))) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)))) = (Zlength (seen_l_2))) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i (Zlength (seen_l_2)) p_pre ((answer + (Znth (Znth i colors_l 0) good_l 0) ) - (Znth (Znth i colors_l 0) good_l 0) ) seen_l good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) (Zlength (seen_l_2)) p_pre (answer + (Znth (Znth i colors_l 0) good_l 0) ) (replace_Znth ((Znth i colors_l 0)) (((Znth (Znth i colors_l 0) seen_l 0) + 1 )) (seen_l)) good_l ) ”
  &&  emp
).

Definition countChoosingInns_entail_wit_7_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (0 <= c)) (PreH18 : (c < k_pre)) (PreH19 : (0 <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : (0 <= (i + 1 ))) (PreH22 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH23 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH24 : ((Zlength (seen_next)) = k_pre)) (PreH25 : (Forall (Z.le (0)) seen_next )) (PreH26 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH27 : ((Zlength (seen_next)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_next )) (PreH29 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH30 : (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next seen_next )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre seen_next )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_entail_wit_7_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (p_pre < cost)) (PreH16 : (cost <= 100)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l_2 0) + 1 )) (seen_l_2)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l_2)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l_2 )) (PreH29 : (Forall (Z.ge (i)) seen_l_2 )) (PreH30 : ((Zlength (good_l_2)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l_2 )) (PreH32 : (Forall (Z.ge (i)) good_l_2 )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l_2)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l_2 )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l_2 )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c good_l_2 0) ) seen_l_2 good_l_2 )) (PreH43 : (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next good_l_2 )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_next )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l_2 )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l (i + 1 ) k_pre p_pre answer seen_l good_l ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_entail_wit_8 := 
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full ( &( "seen" ) ) 50 )
  **  (IntArray.undef_full ( &( "good" ) ) 50 )
) \/
(
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer ) ”
  &&  (IntArray.undef_full ( &( "seen" ) ) 50 )
  **  (IntArray.undef_full ( &( "good" ) ) 50 )
).

Definition countChoosingInns_entail_wit_8_split_goal_1 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer ) ”
.

Definition countChoosingInns_entail_wit_8_split_goal_spatial := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  (IntArray.undef_full ( &( "seen" ) ) 50 )
  **  (IntArray.undef_full ( &( "good" ) ) 50 )
.

Definition countChoosingInns_return_wit_1 := 
forall (p_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (PreH1 : (InnsPairAnswer colors_l costs_l n_pre p_pre answer )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer ) ”
  &&  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
.

Definition countChoosingInns_partial_solve_wit_1_pure := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ”
.

Definition countChoosingInns_partial_solve_wit_1_aux := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (answer = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ (0 <= p_pre) ” 
  &&  “ (p_pre <= 100) ” 
  &&  “ ((Zlength (colors_l)) = n_pre) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ”
  &&  (IntArray.undef_full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.undef_full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_1 := countChoosingInns_partial_solve_wit_1_pure -> countChoosingInns_partial_solve_wit_1_aux.

Definition countChoosingInns_partial_solve_wit_2 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |-> (Znth i colors_l 0))
  **  (IntArray.missing_i colors_pre i 0 n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_3 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l: (@list Z)) (seen_l: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : (0 <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall (Z.le (0)) colors_l )) (PreH11 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH12 : (Forall (Z.le (0)) costs_l )) (PreH13 : (Forall (Z.ge (100)) costs_l )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall (Z.le (0)) seen_l )) (PreH23 : (Forall (Z.ge (i)) seen_l )) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall (Z.le (0)) good_l )) (PreH26 : (Forall (Z.ge (i)) good_l )) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((costs_pre + (i * sizeof(INT)))) # Int  |-> (Znth i costs_l 0))
  **  (IntArray.missing_i costs_pre i 0 n_pre costs_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_4 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i ( &( "seen" ) ) c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_5 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i ( &( "seen" ) ) c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_6 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) c 0 k_pre seen_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_7_pure := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next )) (PreH45 : (Forall (Z.ge (200000)) seen_next )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "costs" ) )) # Ptr  |-> costs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cost" ) )) # Int  |-> cost)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (200000)) good_l ) ”
.

Definition countChoosingInns_partial_solve_wit_7_aux := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (c = (Znth i colors_l 0))) (PreH2 : (cost = (Znth i costs_l 0))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : (0 <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall (Z.le (0)) colors_l )) (PreH12 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH13 : (Forall (Z.le (0)) costs_l )) (PreH14 : (Forall (Z.ge (100)) costs_l )) (PreH15 : (0 <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (0 <= c)) (PreH20 : (c < k_pre)) (PreH21 : (0 <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall (Z.le (0)) seen_l )) (PreH29 : (Forall (Z.ge (i)) seen_l )) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall (Z.le (0)) good_l )) (PreH32 : (Forall (Z.ge (i)) good_l )) (PreH33 : (0 <= (i + 1 ))) (PreH34 : ((i + 1 ) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall (Z.le (0)) seen_next )) (PreH38 : (Forall (Z.ge ((i + 1 ))) seen_next )) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall (Z.le (0)) good_l )) (PreH41 : (Forall (Z.ge ((i + 1 ))) good_l )) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall (Z.le (0)) seen_next )) (PreH45 : (Forall (Z.ge (200000)) seen_next )) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall (Z.le (0)) good_l )) (PreH48 : (Forall (Z.ge (200000)) good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 50) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (200000)) good_l ) ” 
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
  &&  “ (0 <= cost) ” 
  &&  “ (cost <= p_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 19999900000) ” 
  &&  “ (seen_next = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l ) ” 
  &&  “ ((Zlength (seen_next)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_next ) ” 
  &&  “ (Forall (Z.ge (200000)) seen_next ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (200000)) good_l ) ”
  &&  (IntArray.full (( &( "seen" ) ) + (0 * sizeof(INT))) k_pre seen_next )
  **  (IntArray.full (( &( "good" ) ) + (0 * sizeof(INT))) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_7 := countChoosingInns_partial_solve_wit_7_pure -> countChoosingInns_partial_solve_wit_7_aux.

Definition countChoosingInns_partial_solve_wit_8 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "good" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c good_l 0))
  **  (IntArray.missing_i ( &( "good" ) ) c 0 k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_9 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c seen_l 0))
  **  (IntArray.missing_i ( &( "seen" ) ) c 0 k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Definition countChoosingInns_partial_solve_wit_10 := 
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_pre: Z) (colors_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : (0 <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall (Z.le (0)) colors_l )) (PreH13 : (Forall (Z.ge ((k_pre - 1 ))) colors_l )) (PreH14 : (Forall (Z.le (0)) costs_l )) (PreH15 : (Forall (Z.ge (100)) costs_l )) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= c)) (PreH19 : (c < k_pre)) (PreH20 : (0 <= cost)) (PreH21 : (cost <= 100)) (PreH22 : (0 <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : (0 <= (Znth c seen_l 0))) (PreH25 : ((Znth c seen_l 0) <= i)) (PreH26 : (0 <= (Znth c good_l 0))) (PreH27 : ((Znth c good_l 0) <= i)) (PreH28 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) (PreH29 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) (PreH30 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) (PreH31 : (0 <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall (Z.le (0)) seen_l )) (PreH36 : (Forall (Z.ge (i)) seen_l )) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall (Z.le (0)) good_l )) (PreH39 : (Forall (Z.ge (i)) good_l )) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l )) ,
  (IntArray.full ( &( "seen" ) ) k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
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
  &&  “ (Forall (Z.le (0)) colors_l ) ” 
  &&  “ (Forall (Z.ge ((k_pre - 1 ))) colors_l ) ” 
  &&  “ (Forall (Z.le (0)) costs_l ) ” 
  &&  “ (Forall (Z.ge (100)) costs_l ) ” 
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (colors_l))) ” 
  &&  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” 
  &&  “ ((Zlength (seen_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) seen_l ) ” 
  &&  “ (Forall (Z.ge (i)) seen_l ) ” 
  &&  “ ((Zlength (good_l)) = k_pre) ” 
  &&  “ (Forall (Z.le (0)) good_l ) ” 
  &&  “ (Forall (Z.ge (i)) good_l ) ” 
  &&  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l ) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) c 0 k_pre seen_l )
  **  (IntArray.full ( &( "good" ) ) k_pre good_l )
  **  (IntArray.full colors_pre n_pre colors_l )
  **  (IntArray.full costs_pre n_pre costs_l )
  **  (IntArray.undef_seg ( &( "seen" ) ) k_pre 50 )
  **  (IntArray.undef_seg ( &( "good" ) ) k_pre 50 )
.

Module Type VC_Correct.


Axiom proof_of_initCounts_safety_wit_1 : initCounts_safety_wit_1.
Axiom proof_of_initCounts_safety_wit_2 : initCounts_safety_wit_2.
Axiom proof_of_initCounts_safety_wit_3 : initCounts_safety_wit_3.
Axiom proof_of_initCounts_safety_wit_4 : initCounts_safety_wit_4.
Axiom proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Axiom proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Axiom proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Axiom proof_of_initCounts_partial_solve_wit_1 : initCounts_partial_solve_wit_1.
Axiom proof_of_initCounts_partial_solve_wit_2 : initCounts_partial_solve_wit_2.
Axiom proof_of_copyCounts_safety_wit_1 : copyCounts_safety_wit_1.
Axiom proof_of_copyCounts_safety_wit_2 : copyCounts_safety_wit_2.
Axiom proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Axiom proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
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
Axiom proof_of_countChoosingInns_safety_wit_11 : countChoosingInns_safety_wit_11.
Axiom proof_of_countChoosingInns_safety_wit_12 : countChoosingInns_safety_wit_12.
Axiom proof_of_countChoosingInns_safety_wit_13 : countChoosingInns_safety_wit_13.
Axiom proof_of_countChoosingInns_safety_wit_14 : countChoosingInns_safety_wit_14.
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
