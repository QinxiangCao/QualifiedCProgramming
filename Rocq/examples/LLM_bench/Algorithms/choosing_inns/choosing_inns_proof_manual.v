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
From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Require Import AUXLib.MonotonicList.
From SumLib Require Import ZRange.
(* Proofs reused by the current witnesses, kept with their mathematical
   statements in this manual so they compile without a separate library. *)
Module ReusedProof.
Definition initCounts_entail_wit_1_split_goal_1 :=
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (CountsZeroPrefix (@nil Z) 0 ).

Definition initCounts_entail_wit_1_split_goal_2 :=
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (CountsZeroPrefix (@nil Z) 0 ).

Definition initCounts_entail_wit_1 :=
forall (k_pre: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (@nil Z) 0 ) ” 
  &&  “ (CountsZeroPrefix (@nil Z) 0 ) ”
  &&  emp.

Definition initCounts_entail_wit_2_split_goal_1 :=
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (CountsZeroPrefix (app (good_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ).

Definition initCounts_entail_wit_2_split_goal_2 :=
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (CountsZeroPrefix (app (seen_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ).

Definition initCounts_entail_wit_2 :=
forall (k_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  TT && emp 
|--
  “ (CountsZeroPrefix (app (good_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ (CountsZeroPrefix (app (seen_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp.

Definition initCounts_return_wit_1 :=
forall (k_pre: Z) (good_pre: Z) (seen_pre: Z) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountsZeroPrefix seen_l_2 i )) (PreH7 : (CountsZeroPrefix good_l_2 i )) ,
  (IntArray.seg seen_pre 0 i seen_l_2 )
  **  (IntArray.seg good_pre 0 i good_l_2 )
|--
  EX (good_l: (@list Z))  (seen_l: (@list Z)) ,
  “ (CountsZeroFull k_pre seen_l ) ” 
  &&  “ (CountsZeroFull k_pre good_l ) ”
  &&  (IntArray.full seen_pre k_pre seen_l )
  **  (IntArray.full good_pre k_pre good_l ).

Definition copyCounts_entail_wit_1_split_goal_1 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  (CopyCountsPrefix seen_l good_old good_old 0 k_pre ).

Definition copyCounts_entail_wit_1 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : (CountArraySafe seen_l k_pre 200000 )) (PreH4 : (CountArraySafe good_old k_pre 200000 )) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old good_old 0 k_pre ) ”
  &&  emp.

Definition copyCounts_entail_wit_2_split_goal_1 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ).

Definition copyCounts_entail_wit_2_split_goal_2 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  (CountArraySafe (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) k_pre 200000 ).

Definition copyCounts_entail_wit_2 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur_2: (@list Z)) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) ,
  TT && emp 
|--
  “ (CopyCountsPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) (i + 1 ) k_pre ) ” 
  &&  “ (CountArraySafe (replace_Znth (i) ((Znth i seen_l 0)) (good_cur_2)) k_pre 200000 ) ”
  &&  emp.

Definition copyCounts_return_wit_1_split_goal_1 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  (good_cur = seen_l).

Definition copyCounts_return_wit_1 :=
forall (k_pre: Z) (good_old: (@list Z)) (seen_l: (@list Z)) (good_cur: (@list Z)) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : (0 <= i)) (PreH5 : (i <= k_pre)) (PreH6 : (CountArraySafe seen_l k_pre 200000 )) (PreH7 : (CountArraySafe good_old k_pre 200000 )) (PreH8 : (CountArraySafe good_cur k_pre 200000 )) (PreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp.

Definition countChoosingInns_entail_wit_1_split_goal_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 ).

Definition countChoosingInns_entail_wit_1_split_goal_2 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 ).

Definition countChoosingInns_entail_wit_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (good_l_2: (@list Z)) (seen_l_2: (@list Z)) (PreH1 : (CountsZeroFull k_pre seen_l_2 )) (PreH2 : (CountsZeroFull k_pre good_l_2 )) (PreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 ) ”
  &&  emp.

Definition countChoosingInns_entail_wit_2_split_goal_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l_2 )) (PreH4 : (CountsZeroFull k_pre good_l_2 )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) ,
  (0 <= n_pre).

Definition countChoosingInns_entail_wit_2 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (PreH1 : (answer = 0)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (CountsZeroFull k_pre seen_l_2 )) (PreH4 : (CountsZeroFull k_pre good_l_2 )) (PreH5 : (ChoosingPrefixDataSafe colors_l costs_l 0 k_pre seen_l_2 good_l_2 )) (PreH6 : (ChoosingPrefixState colors_l costs_l 0 k_pre p_pre 0 seen_l_2 good_l_2 )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ”
  &&  emp.

Definition countChoosingInns_entail_wit_3_split_goal_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (((Znth (Znth i colors_l 0) seen_l_2 0) + 1 ) <= INT_MAX).

Definition countChoosingInns_entail_wit_3_split_goal_2 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) good_l_2 0) ) <= INT64_MAX).

Definition countChoosingInns_entail_wit_3_split_goal_3 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((answer + (Znth (Znth i colors_l 0) seen_l_2 0) ) <= INT64_MAX).

Definition countChoosingInns_entail_wit_3_split_goal_4 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) good_l_2 0) <= i).

Definition countChoosingInns_entail_wit_3_split_goal_5 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) good_l_2 0)).

Definition countChoosingInns_entail_wit_3_split_goal_6 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth (Znth i colors_l 0) seen_l_2 0) <= i).

Definition countChoosingInns_entail_wit_3_split_goal_7 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth (Znth i colors_l 0) seen_l_2 0)).

Definition countChoosingInns_entail_wit_3_split_goal_8 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i costs_l 0) <= 100).

Definition countChoosingInns_entail_wit_3_split_goal_9 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i costs_l 0)).

Definition countChoosingInns_entail_wit_3_split_goal_10 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  ((Znth i colors_l 0) < k_pre).

Definition countChoosingInns_entail_wit_3_split_goal_11 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (0 <= (Znth i colors_l 0)).

Definition countChoosingInns_entail_wit_3 :=
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
  &&  emp.

Definition countChoosingInns_entail_wit_4 :=
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
  &&  emp.

Definition countChoosingInns_entail_wit_5_split_goal_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next_2 seen_next_2 ).

Definition countChoosingInns_entail_wit_5_split_goal_2 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 seen_next_2 ).

Definition countChoosingInns_entail_wit_5 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_next_2: (@list Z)) (seen_l: (@list Z)) (good_l: (@list Z)) (c: Z) (i: Z) (cost: Z) (answer: Z) (PreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH2 : (c = (Znth i colors_l 0))) (PreH3 : (cost = (Znth i costs_l 0))) (PreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH5 : (0 <= cost)) (PreH6 : (cost <= p_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < k_pre)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= 19999900000)) (PreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) (PreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) (PreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) (PreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) (PreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) (PreH18 : (CountArraySafe good_l k_pre 200000 )) ,
  TT && emp 
|--
  “ (ChoosingPrefixState colors_l costs_l (i + 1 ) k_pre p_pre answer seen_next_2 seen_next_2 ) ” 
  &&  “ (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 seen_next_2 ) ”
  &&  emp.

Definition countChoosingInns_entail_wit_6 :=
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
  &&  emp.

Definition countChoosingInns_entail_wit_8_split_goal_1 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ).

Definition countChoosingInns_entail_wit_8 :=
forall (p_pre: Z) (k_pre: Z) (n_pre: Z) (costs_l: (@list Z)) (colors_l: (@list Z)) (seen_l_2: (@list Z)) (good_l_2: (@list Z)) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= answer)) (PreH6 : (answer <= 19999900000)) (PreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) (PreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) ,
  TT && emp 
|--
  “ (ChoosingInnsAnswer colors_l costs_l n_pre k_pre p_pre answer ) ”
  &&  emp.

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
  “ (1 <= k_pre) ”.

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
  “ (k_pre <= 50) ”.

Definition countChoosingInns_partial_solve_wit_1_pure :=
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
  &&  “ (k_pre <= 50) ”.

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
  “ (k_pre <= 50) ”.

Definition countChoosingInns_partial_solve_wit_7_pure :=
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
  “ (k_pre <= 50) ”.

Ltac choosing_input_safe_lia H :=
  let Hsafe := fresh "Hsafe" in
  let Hn := fresh "Hn" in
  let Hk := fresh "Hk" in
  let Hp := fresh "Hp" in
  let Hcolors_len := fresh "Hcolors_len" in
  let Hcosts_len := fresh "Hcosts_len" in
  let Hcolors_bound := fresh "Hcolors_bound" in
  let Hcosts_bound := fresh "Hcosts_bound" in
  let Hn_lo := fresh "Hn_lo" in
  let Hn_hi := fresh "Hn_hi" in
  let Hk_lo := fresh "Hk_lo" in
  let Hk_hi := fresh "Hk_hi" in
  let Hp_lo := fresh "Hp_lo" in
  let Hp_hi := fresh "Hp_hi" in
  pose proof H as Hsafe;
  unfold ChoosingInputSafe in Hsafe;
  destruct Hsafe as
    [Hn [Hk [Hp [Hcolors_len [Hcosts_len [Hcolors_bound Hcosts_bound]]]]]];
  destruct Hn as [Hn_lo Hn_hi];
  destruct Hk as [Hk_lo Hk_hi];
  destruct Hp as [Hp_lo Hp_hi];
  lia.

Lemma proof_of_initCounts_entail_wit_1_split_goal_1 : initCounts_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  apply CountsZeroPrefix_nil.
Qed.
Lemma proof_of_initCounts_entail_wit_1_split_goal_2 : initCounts_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  apply CountsZeroPrefix_nil.
Qed.
Lemma proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_initCounts_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_initCounts_entail_wit_1_split_goal_2.
Qed.
Lemma proof_of_initCounts_entail_wit_2_split_goal_1 : initCounts_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CountsZeroPrefix_snoc_zero; eauto; lia.
Qed.
Lemma proof_of_initCounts_entail_wit_2_split_goal_2 : initCounts_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  eapply CountsZeroPrefix_snoc_zero; eauto; lia.
Qed.
Lemma proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_initCounts_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_initCounts_entail_wit_2_split_goal_2.
Qed.
Lemma proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Proof.
  aggressive_pre_process.
  replace i with k_pre in * by lia.
  Exists good_l_2 seen_l_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full seen_pre 0 k_pre seen_l_2).
    replace (seen_pre + 0 * sizeof(INT)) with seen_pre by lia.
    replace (k_pre - 0) with k_pre by lia.
    sep_apply (IntArray.seg_to_full good_pre 0 k_pre good_l_2).
    replace (good_pre + 0 * sizeof(INT)) with good_pre by lia.
    replace (k_pre - 0) with k_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia.
    + apply CountsZeroPrefix_to_full. exact PreH6.
    + apply CountsZeroPrefix_to_full. exact PreH7.
Qed.
Lemma proof_of_copyCounts_entail_wit_1_split_goal_1 : copyCounts_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  apply CopyCountsPrefix_zero.
  - exact (proj1 PreH3).
  - exact (proj1 PreH4).
Qed.
Lemma proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copyCounts_entail_wit_1_split_goal_1.
Qed.
Lemma proof_of_copyCounts_entail_wit_2_split_goal_1 : copyCounts_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CopyCountsPrefix_step_replace; eauto.
  unfold CountArraySafe in PreH8.
  tauto.
Qed.
Lemma proof_of_copyCounts_entail_wit_2_split_goal_2 : copyCounts_entail_wit_2_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold CountArraySafe in *.
  destruct PreH6 as [Hseen_len Hseen_bounds].
  destruct PreH8 as [Hgood_len Hgood_bounds].
  split.
  - rewrite Zlength_replace_Znth. exact Hgood_len.
  - eapply replace_Znth_preserves_bounds with
        (xs := good_cur_2) (i := i) (v := Znth i seen_l 0)
        (k := k_pre) (lo := 0) (hi := 200000); eauto; lia.
Qed.
Lemma proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_copyCounts_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_copyCounts_entail_wit_2_split_goal_2.
Qed.
Lemma proof_of_copyCounts_return_wit_1_split_goal_1 : copyCounts_return_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold CountArraySafe in PreH6, PreH8.
  destruct PreH6 as [Hseen_len _].
  destruct PreH8 as [Hgood_len _].
  eapply CopyCountsPrefix_full_eq; eauto; lia.
Qed.
Lemma proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_copyCounts_return_wit_1_split_goal_1.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_1_split_goal_1 : countChoosingInns_entail_wit_1_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply CountsZeroFull_to_ChoosingPrefixState_zero; eauto.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_1_split_goal_2 : countChoosingInns_entail_wit_1_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH3.
  destruct PreH3 as [_ [_ [_ [Hcolors_len [Hcosts_len _]]]]].
  eapply CountsZeroFull_to_ChoosingPrefixDataSafe_zero; eauto; lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_1_split_goal_2.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_2_split_goal_1 : countChoosingInns_entail_wit_2_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_2_split_goal_1.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_1 : countChoosingInns_entail_wit_3_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  int_auto; lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_2 : countChoosingInns_entail_wit_3_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_3 : countChoosingInns_entail_wit_3_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [Hn [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_4 : countChoosingInns_entail_wit_3_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_5 : countChoosingInns_entail_wit_3_split_goal_5.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [_ [_ Hgood]]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hgood (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_6 : countChoosingInns_entail_wit_3_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_7 : countChoosingInns_entail_wit_3_split_goal_7.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  unfold ChoosingPrefixDataSafe, CountArraySafe in PreH7.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  destruct PreH7 as [_ [_ [[_ Hseen] _]]].
  specialize (Hcolors i ltac:(lia)).
  specialize (Hseen (Znth i colors_l 0) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_8 : countChoosingInns_entail_wit_3_split_goal_8.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [_ Hcosts]]]]]].
  specialize (Hcosts i ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_9 : countChoosingInns_entail_wit_3_split_goal_9.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [_ Hcosts]]]]]].
  specialize (Hcosts i ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_10 : countChoosingInns_entail_wit_3_split_goal_10.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  specialize (Hcolors i ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3_split_goal_11 : countChoosingInns_entail_wit_3_split_goal_11.
Proof.
  aggressive_pre_process.
  unfold ChoosingInputSafe in PreH2.
  destruct PreH2 as [_ [_ [_ [_ [_ [Hcolors _]]]]]].
  specialize (Hcolors i ltac:(lia)).
  lia.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_4.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_5.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_6.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_7.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_8.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_9.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_10.
  - Goal_apply proof_of_countChoosingInns_entail_wit_3_split_goal_11.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Proof.
  aggressive_pre_process.
  assert (Hnext_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      good_l_2).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    all: choosing_input_safe_lia PreH4.
  }
  assert (Hnext_full_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
  {
    eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
    all: choosing_input_safe_lia PreH4.
  }
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c seen_l 0)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      (replace_Znth c (Znth c seen_l 0 + 1) seen_l)).
  {
    eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer) (good := good_l_2) (c := c);
      try exact PreH20; try exact PreH21; try exact PreH2;
      try reflexivity; try lia.
    choosing_input_safe_lia PreH4.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c seen_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (good := replace_Znth c (Znth c seen_l 0 + 1) seen_l)
           (n := n_pre); eauto.
    all: choosing_input_safe_lia PreH4.
  }
  pose proof Hnext_data as Hnext_data_parts.
  unfold ChoosingPrefixDataSafe in Hnext_data_parts.
  destruct Hnext_data_parts as
    [Hnext_limit [_ [Hnext_seen_safe Hnext_good_safe]]].
  assert (Hnext_seen_200 :
    CountArraySafe (replace_Znth c (Znth c seen_l 0 + 1) seen_l)
      k_pre 200000).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_seen_safe |].
    choosing_input_safe_lia PreH4.
  }
  assert (Hnext_good_200 : CountArraySafe good_l_2 k_pre 200000).
  {
    eapply CountArraySafe_weaken_limit; [exact Hnext_good_safe |].
    choosing_input_safe_lia PreH4.
  }
  subst c.
  Exists seen_l.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption;
      try exact Hnext_data; try exact Hnext_state; try lia.
    + replace
        (answer + Znth (Znth i colors_l 0) seen_l 0 -
         Znth (Znth i colors_l 0) seen_l 0)
        with answer by lia.
      exact PreH21.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_5_split_goal_1 : countChoosingInns_entail_wit_5_split_goal_1.
Proof.
  aggressive_pre_process.
  eapply ChoosingPrefixState_step_affordable_after_copy
      with (old_answer := answer - Znth c seen_l 0)
           (seen := seen_l) (good := good_l) (c := c);
    try exact PreH14; try exact PreH16; try exact PreH2;
    try exact PreH13; try lia.
  choosing_input_safe_lia PreH4.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_5_split_goal_2 : countChoosingInns_entail_wit_5_split_goal_2.
Proof.
  aggressive_pre_process.
  subst seen_next_2.
  eapply ChoosingPrefixDataSafe_step_affordable_after_copy; eauto.
  choosing_input_safe_lia PreH4.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_entail_wit_5_split_goal_2.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Proof.
  aggressive_pre_process.
  assert (Hnext_data :
    ChoosingPrefixDataSafe colors_l costs_l (i + 1) k_pre
      (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l).
  {
    eapply ChoosingPrefixDataSafe_step_expensive; eauto.
    choosing_input_safe_lia PreH4.
  }
  assert (Hnext_state :
    ChoosingPrefixState colors_l costs_l (i + 1) k_pre p_pre
      (answer + Znth c good_l 0)
      (replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2) good_l).
  {
    eapply ChoosingPrefixState_step_expensive
      with (old_answer := answer) (c := c);
      try exact PreH20; try exact PreH21; try exact PreH2;
      try reflexivity; try lia.
    choosing_input_safe_lia PreH4.
  }
  assert (Hnext_bound :
    0 <= answer + Znth c good_l 0 <= 19999900000).
  {
    eapply ChoosingPrefixState_answer_bound
      with (seen := replace_Znth c (Znth c seen_l_2 0 + 1) seen_l_2)
           (good := good_l) (n := n_pre); eauto.
    all: choosing_input_safe_lia PreH4.
  }
  subst c.
  Exists seen_l_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption;
      try exact Hnext_data; try exact Hnext_state; try lia.
    replace
      (answer + Znth (Znth i colors_l 0) good_l 0 -
       Znth (Znth i colors_l 0) good_l 0)
      with answer by lia.
    exact PreH21.
Qed.
Lemma proof_of_countChoosingInns_entail_wit_8_split_goal_1 : countChoosingInns_entail_wit_8_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold ChoosingInnsAnswer.
  replace n_pre with i by lia.
  exact (proj1 PreH8).
Qed.
Lemma proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_countChoosingInns_entail_wit_8_split_goal_1.
Qed.
Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1 : countChoosingInns_partial_solve_wit_1_pure_split_goal_1.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH9.
  lia.
Qed.
Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2 : countChoosingInns_partial_solve_wit_1_pure_split_goal_2.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH9.
  lia.
Qed.
Lemma proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_countChoosingInns_partial_solve_wit_1_pure_split_goal_2.
Qed.
Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1 : countChoosingInns_partial_solve_wit_7_pure_split_goal_1.
Proof.
  aggressive_pre_process.
  dump_pre_spatial.
  unfold ChoosingInputSafe in PreH17.
  lia.
Qed.
Lemma proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_countChoosingInns_partial_solve_wit_7_pure_split_goal_1.
Qed.
End ReusedProof.

Lemma inns_interval_library : forall lo hi,
  zrange_between lo hi = Zrange lo (hi + 1).
Proof.
  intros lo hi. unfold zrange_between, Zrange.
  replace (hi + 1 - lo) with (hi - lo + 1) by lia.
  remember (Z.to_nat (hi - lo + 1)) as count.
  clear Heqcount hi. revert lo.
  induction count as [|count IH]; intros lo; simpl; [reflexivity |].
  rewrite Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map.
  rewrite <- IH. apply map_ext. intros x. lia.
Qed.
Lemma inns_range_library : forall n, zrange n = Zrange 0 n.
Proof.
  intros n.
  assert (H : zrange n = zrange_between 0 (n - 1)).
  { unfold zrange, zrange_between. replace (n - 1 - 0 + 1) with n by lia. reflexivity. }
  rewrite H, inns_interval_library. f_equal. lia.
Qed.
Lemma inns_affordable_eq : forall costs p lo hi,
  affordable_betweenb costs p lo hi = InnsAffordable costs p lo hi.
Proof. intros. unfold affordable_betweenb, InnsAffordable. rewrite inns_interval_library. reflexivity. Qed.
Lemma inns_pair_allowed_eq : forall colors costs p pair,
  choosing_pairb colors costs p pair = InnsPairAllowed colors costs p pair.
Proof. intros colors costs p [a b]. unfold choosing_pairb, InnsPairAllowed. rewrite inns_affordable_eq. reflexivity. Qed.
Lemma inns_pairs_eq : forall n, choosing_pairs_up_to n = InnsPairs n.
Proof. intros. unfold choosing_pairs_up_to, InnsPairs. rewrite inns_range_library. apply flat_map_ext. intros r. rewrite inns_range_library. reflexivity. Qed.
Lemma inns_pair_count_eq : forall colors costs p n,
  choosing_pair_count colors costs p n = InnsPairCount colors costs p n.
Proof.
  intros. unfold choosing_pair_count, InnsPairCount. rewrite Zlength_correct, inns_pairs_eq.
  f_equal. f_equal. apply filter_ext_in. intros pair _. apply inns_pair_allowed_eq.
Qed.
Lemma inns_color_count_eq : forall colors limit color,
  color_count colors limit color = InnsColorCount colors limit color.
Proof. intros. unfold color_count, InnsColorCount. rewrite Zlength_correct, inns_range_library. reflexivity. Qed.
Lemma inns_good_count_eq : forall colors costs limit p color,
  good_color_count colors costs limit p color = InnsGoodColorCount colors costs limit p color.
Proof.
  intros. unfold good_color_count, InnsGoodColorCount. rewrite Zlength_correct, inns_range_library.
  f_equal. f_equal. apply filter_ext_in. intros idx _. rewrite inns_affordable_eq. reflexivity.
Qed.
Lemma inns_prefix_iff : forall colors costs limit k p answer seen good,
  ChoosingPrefixState colors costs limit k p answer seen good <->
  InnsPrefixCounts colors costs limit k p answer seen good.
Proof.
  intros. unfold ChoosingPrefixState, InnsPrefixCounts.
  setoid_rewrite inns_pair_count_eq. setoid_rewrite inns_color_count_eq.
  setoid_rewrite inns_good_count_eq. tauto.
Qed.
Lemma inns_answer_iff : forall colors costs n k p answer,
  ChoosingInnsAnswer colors costs n k p answer <-> InnsPairAnswer colors costs n p answer.
Proof. intros. unfold ChoosingInnsAnswer, InnsPairAnswer. rewrite inns_pair_count_eq. tauto. Qed.
Lemma inns_bounds_iff : forall xs lo hi,
  (Forall (Z.le lo) xs /\ Forall (Z.ge hi) xs) <->
  (forall i, 0 <= i < Zlength xs -> lo <= Znth i xs 0 <= hi).
Proof.
  intros xs lo hi. split.
  - intros [Hl Hh] i Hi.
    pose proof (proj1 (Forall_Znth (Z.le lo) 0 xs) Hl i Hi) as H1.
    pose proof (proj1 (Forall_Znth (Z.ge hi) 0 xs) Hh i Hi) as H2.
    apply Z.ge_le in H2. lia.
  - intros H. split.
    + apply (proj2 (Forall_Znth (Z.le lo) 0 xs)). intros i Hi. specialize (H i Hi). lia.
    + apply (proj2 (Forall_Znth (Z.ge hi) 0 xs)). intros i Hi. specialize (H i Hi). apply Z.le_ge. lia.
Qed.
Lemma inns_array_iff : forall xs k limit,
  CountArraySafe xs k limit <->
  Zlength xs = k /\ Forall (Z.le 0) xs /\ Forall (Z.ge limit) xs.
Proof.
  intros xs k limit. unfold CountArraySafe. rewrite inns_bounds_iff.
  split; intros [Hlen H]; (split; [exact Hlen | intros i Hi; apply H; lia]).
Qed.
Lemma inns_zero_prefix_iff : forall xs n,
  CountsZeroPrefix xs n <-> Zlength xs = n /\ Forall (eq 0) xs.
Proof.
  intros xs n. unfold CountsZeroPrefix. rewrite (Forall_Znth (eq 0) 0 xs).
  split; intros [Hlen H]; (split; [exact Hlen | intros i Hi; specialize (H i ltac:(lia)); lia]).
Qed.
Lemma inns_zero_full_iff : forall n xs,
  CountsZeroFull n xs <-> Zlength xs = n /\ Forall (eq 0) xs.
Proof. intros. exact (inns_zero_prefix_iff xs n). Qed.

Lemma inns_input_iff : forall colors costs n k p,
  ChoosingInputSafe colors costs n k p <->
  0 <= n /\ n <= 200000 /\ 1 <= k /\ k <= 50 /\ 0 <= p /\ p <= 100 /\
  Zlength colors = n /\ Zlength costs = n /\
  Forall (Z.le 0) colors /\ Forall (Z.ge (k - 1)) colors /\
  Forall (Z.le 0) costs /\ Forall (Z.ge 100) costs.
Proof.
  intros colors costs n k p. unfold ChoosingInputSafe. split.
  - intros (Hn & Hk & Hp & HC & HB & Hcols & Hcosts).
    assert (Hcolor_forall : Forall (Z.le 0) colors /\ Forall (Z.ge (k - 1)) colors).
    { apply inns_bounds_iff. intros idx Hi. specialize (Hcols idx ltac:(lia)). lia. }
    assert (Hcost_forall : Forall (Z.le 0) costs /\ Forall (Z.ge 100) costs).
    { apply inns_bounds_iff. intros idx Hi. apply Hcosts. lia. }
    intuition lia.
  - intros (Hnl & Hnh & Hkl & Hkh & Hpl & Hph & HC & HB & Hcl & Hch & Hbl & Hbh).
    pose proof (proj1 (inns_bounds_iff colors 0 (k - 1)) (conj Hcl Hch)) as Hcolors.
    pose proof (proj1 (inns_bounds_iff costs 0 100) (conj Hbl Hbh)) as Hcosts.
    assert (Hcolors' : forall idx, 0 <= idx < n -> 0 <= Znth idx colors 0 < k).
    { intros idx Hi. specialize (Hcolors idx ltac:(lia)). lia. }
    assert (Hcosts' : forall idx, 0 <= idx < n -> 0 <= Znth idx costs 0 <= 100).
    { intros idx Hi. apply Hcosts. lia. }
    repeat first [assumption | match goal with |- _ /\ _ => split end]; lia.
Qed.
Lemma inns_Forall2_eq : forall (xs ys : list Z), Forall2 eq xs ys <-> xs = ys.
Proof.
  intros xs ys. split.
  - intros H. induction H; subst; f_equal; assumption.
  - intros H. subst ys. induction xs; constructor; auto.
Qed.
Lemma inns_segments_agree : forall (xs ys : list Z) lo hi other_lo other_hi,
  0 <= lo <= hi /\ hi <= Zlength xs ->
  0 <= other_lo <= other_hi /\ other_hi <= Zlength ys ->
  hi - lo = other_hi - other_lo ->
  (Forall2 eq (sublist lo hi xs) (sublist other_lo other_hi ys) <->
   forall k, 0 <= k < hi - lo ->
     Znth (lo + k) xs 0 = Znth (other_lo + k) ys 0).
Proof.
  intros xs ys lo hi other_lo other_hi Hx Hy Hlength.
  rewrite inns_Forall2_eq, (list_eq_ext _ _ 0).
  rewrite !Zlength_sublist by lia. split.
  - intros [_ H] k Hk. specialize (H k Hk).
    rewrite !Znth_sublist in H by lia.
    replace (k + lo) with (lo + k) in H by lia.
    replace (k + other_lo) with (other_lo + k) in H by lia. exact H.
  - intros H. split; [lia |]. intros k Hk.
    rewrite !Znth_sublist by lia.
    replace (k + lo) with (lo + k) by lia.
    replace (k + other_lo) with (other_lo + k) by lia. apply H. exact Hk.
Qed.

Lemma inns_copy_iff : forall src old dst written k,
  Zlength src = k -> Zlength old = k -> Zlength dst = k ->
  0 <= written <= k ->
  (CopyCountsPrefix src old dst written k <-> InnsCopiedPrefix src old dst written k).
Proof.
  intros src old dst written k Hsrc Hold Hdst Hi.
  unfold CopyCountsPrefix, InnsCopiedPrefix.
  rewrite (inns_segments_agree dst src 0 written 0 written ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (inns_segments_agree dst old written k written k ltac:(lia) ltac:(lia) ltac:(lia)).
  split; intros [Hp Hs]; split.
  - intros j Hj. apply Hp. lia.
  - intros j Hj. apply Hs. lia.
  - intros j Hj. apply Hp. lia.
  - intros j Hj. specialize (Hs (j - written) ltac:(lia)).
    replace (written + (j - written)) with j in Hs by lia. exact Hs.
Qed.
Ltac inns_math :=
  try solve [assumption | reflexivity];
  repeat rewrite inns_prefix_iff in *;
  repeat rewrite inns_answer_iff in *;
  unfold ChoosingPrefixDataSafe in *;
  repeat rewrite inns_input_iff in *;
  repeat rewrite inns_array_iff in *;
  repeat rewrite inns_zero_prefix_iff in *;
  repeat rewrite inns_zero_full_iff in *;
  repeat rewrite inns_copy_iff in * by lia;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  try lia;
  repeat match goal with
  | H : Forall ?P ?xs |- _ => rewrite (Forall_Znth P 0 xs) in H
  | |- Forall ?P ?xs => apply (proj2 (Forall_Znth P 0 xs))
  end;
  try solve [assumption | congruence | intuition lia];
  try solve [intros; match goal with H : forall j : Z, _ -> _ |- _ => apply H; lia end];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end];
  try nia.

Lemma proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1.
Proof.
  unfold initCounts_entail_wit_1; try right; intros.
  assert (LegacyPreH1 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH2 : (k_pre <= 50)) by inns_math.
  pose proof (ReusedProof.proof_of_initCounts_entail_wit_1 k_pre LegacyPreH1 LegacyPreH2) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2.
Proof.
  unfold initCounts_entail_wit_2; try right; intros.
  assert (LegacyPreH1 : (i < k_pre)) by inns_math.
  assert (LegacyPreH2 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH3 : (k_pre <= 50)) by inns_math.
  assert (LegacyPreH4 : (0 <= i)) by inns_math.
  assert (LegacyPreH5 : (i <= k_pre)) by inns_math.
  assert (LegacyPreH6 : (CountsZeroPrefix seen_l_2 i )) by inns_math.
  assert (LegacyPreH7 : (CountsZeroPrefix good_l_2 i )) by inns_math.
  pose proof (ReusedProof.proof_of_initCounts_entail_wit_2 k_pre good_l_2 seen_l_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_initCounts_return_wit_1 : initCounts_return_wit_1.
Proof.
  unfold initCounts_return_wit_1; try right; intros.
  assert (LegacyPreH1 : (i >= k_pre)) by inns_math.
  assert (LegacyPreH2 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH3 : (k_pre <= 50)) by inns_math.
  assert (LegacyPreH4 : (0 <= i)) by inns_math.
  assert (LegacyPreH5 : (i <= k_pre)) by inns_math.
  assert (LegacyPreH6 : (CountsZeroPrefix seen_l_2 i )) by inns_math.
  assert (LegacyPreH7 : (CountsZeroPrefix good_l_2 i )) by inns_math.
  pose proof (ReusedProof.proof_of_initCounts_return_wit_1 k_pre good_pre seen_pre good_l_2 seen_l_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros good_l_reused seen_l_reused.
  Exists good_l_reused seen_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1.
Proof.
  unfold copyCounts_entail_wit_1; try right; intros.
  assert (LegacyPreH1 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH2 : (k_pre <= 50)) by inns_math.
  assert (LegacyPreH3 : (CountArraySafe seen_l k_pre 200000 )) by inns_math.
  assert (LegacyPreH4 : (CountArraySafe good_old k_pre 200000 )) by inns_math.
  pose proof (ReusedProof.proof_of_copyCounts_entail_wit_1 k_pre good_old seen_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2.
Proof.
  unfold copyCounts_entail_wit_2; try right; intros.
  assert (LegacyPreH1 : (i < k_pre)) by inns_math.
  assert (LegacyPreH2 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH3 : (k_pre <= 50)) by inns_math.
  assert (LegacyPreH4 : (0 <= i)) by inns_math.
  assert (LegacyPreH5 : (i <= k_pre)) by inns_math.
  assert (LegacyPreH6 : (CountArraySafe seen_l k_pre 200000 )) by inns_math.
  assert (LegacyPreH7 : (CountArraySafe good_old k_pre 200000 )) by inns_math.
  assert (LegacyPreH8 : (CountArraySafe good_cur_2 k_pre 200000 )) by inns_math.
  assert (LegacyPreH9 : (CopyCountsPrefix seen_l good_old good_cur_2 i k_pre )) by inns_math.
  pose proof (ReusedProof.proof_of_copyCounts_entail_wit_2 k_pre good_old seen_l good_cur_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1.
Proof.
  unfold copyCounts_return_wit_1; try right; intros.
  assert (LegacyPreH1 : (i >= k_pre)) by inns_math.
  assert (LegacyPreH2 : (1 <= k_pre)) by inns_math.
  assert (LegacyPreH3 : (k_pre <= 50)) by inns_math.
  assert (LegacyPreH4 : (0 <= i)) by inns_math.
  assert (LegacyPreH5 : (i <= k_pre)) by inns_math.
  assert (LegacyPreH6 : (CountArraySafe seen_l k_pre 200000 )) by inns_math.
  assert (LegacyPreH7 : (CountArraySafe good_old k_pre 200000 )) by inns_math.
  assert (LegacyPreH8 : (CountArraySafe good_cur k_pre 200000 )) by inns_math.
  assert (LegacyPreH9 : (CopyCountsPrefix seen_l good_old good_cur i k_pre )) by inns_math.
  pose proof (ReusedProof.proof_of_copyCounts_return_wit_1 k_pre good_old seen_l good_cur i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2.
Proof.
  unfold countChoosingInns_entail_wit_2; try right; intros. subst answer.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  assert (LegacyPreH1 : (CountsZeroFull k_pre seen_l_2 )) by inns_math.
  assert (LegacyPreH2 : (CountsZeroFull k_pre good_l_2 )) by inns_math.
  assert (LegacyPreH3 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_1 p_pre k_pre n_pre costs_l colors_l good_l_2 seen_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3) as Hreused.
  rewrite truep_andp_left_equiv in Hreused.
  eapply derivable1_trans.
  { apply sepcon_cancel_res_emp. exact Hreused. }
  Intros.
  Exists good_l_2 seen_l_2.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial;
      first [assumption | lia |
        solve [apply (proj1 (inns_prefix_iff _ _ _ _ _ _ _ _)); assumption] |
        eapply Forall_impl with (P := eq 0);
          [intros x Hx; subst x; lia | eassumption]].
Qed.

Lemma proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3.
Proof.
  unfold countChoosingInns_entail_wit_3; try right; intros.
  assert (LegacyPreH1 : (i < n_pre)) by inns_math.
  assert (LegacyPreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  assert (LegacyPreH3 : (0 <= i)) by inns_math.
  assert (LegacyPreH4 : (i <= n_pre)) by inns_math.
  assert (LegacyPreH5 : (0 <= answer)) by inns_math.
  assert (LegacyPreH6 : (answer <= 19999900000)) by inns_math.
  assert (LegacyPreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l_2 )) by inns_math.
  assert (LegacyPreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2 )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_3 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l_2 answer i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4.
Proof.
  unfold countChoosingInns_entail_wit_4; try right; intros.
  assert (LegacyPreH1 : (cost <= p_pre)) by inns_math.
  assert (LegacyPreH2 : (c = (Znth i colors_l 0))) by inns_math.
  assert (LegacyPreH3 : (cost = (Znth i costs_l 0))) by inns_math.
  assert (LegacyPreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  assert (LegacyPreH5 : (0 <= i)) by inns_math.
  assert (LegacyPreH6 : (i < n_pre)) by inns_math.
  assert (LegacyPreH7 : (0 <= c)) by inns_math.
  assert (LegacyPreH8 : (c < k_pre)) by inns_math.
  assert (LegacyPreH9 : (0 <= cost)) by inns_math.
  assert (LegacyPreH10 : (cost <= 100)) by inns_math.
  assert (LegacyPreH11 : (0 <= answer)) by inns_math.
  assert (LegacyPreH12 : (answer <= 19999900000)) by inns_math.
  assert (LegacyPreH13 : (0 <= (Znth c seen_l 0))) by inns_math.
  assert (LegacyPreH14 : ((Znth c seen_l 0) <= i)) by inns_math.
  assert (LegacyPreH15 : (0 <= (Znth c good_l_2 0))) by inns_math.
  assert (LegacyPreH16 : ((Znth c good_l_2 0) <= i)) by inns_math.
  assert (LegacyPreH17 : ((answer + (Znth c seen_l 0) ) <= INT64_MAX)) by inns_math.
  assert (LegacyPreH18 : ((answer + (Znth c good_l_2 0) ) <= INT64_MAX)) by inns_math.
  assert (LegacyPreH19 : (((Znth c seen_l 0) + 1 ) <= INT_MAX)) by inns_math.
  assert (LegacyPreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l_2 )) by inns_math.
  assert (LegacyPreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l_2 )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_4 p_pre k_pre n_pre costs_l colors_l seen_l good_l_2 c i cost answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21) as Hreused.
  rewrite truep_andp_left_equiv in Hreused.
  eapply derivable1_trans.
  { apply sepcon_cancel_res_emp. exact Hreused. }
  Intros seen_l_2_reused.
  Exists good_l_2 seen_l_2_reused.
  try subst c.
  try match goal with H : replace_Znth _ _ _ = replace_Znth _ _ _ |- _ => rewrite H end.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity; try assumption; try congruence.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5.
Proof.
  unfold countChoosingInns_entail_wit_5; try right; intros.
  assert (LegacyPreH1 : (CountArraySafe seen_next_2 k_pre 200000 )) by inns_math.
  assert (LegacyPreH2 : (c = (Znth i colors_l 0))) by inns_math.
  assert (LegacyPreH3 : (cost = (Znth i costs_l 0))) by inns_math.
  assert (LegacyPreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  assert (LegacyPreH5 : (0 <= cost)) by inns_math.
  assert (LegacyPreH6 : (cost <= p_pre)) by inns_math.
  assert (LegacyPreH7 : (0 <= i)) by inns_math.
  assert (LegacyPreH8 : (i < n_pre)) by inns_math.
  assert (LegacyPreH9 : (0 <= c)) by inns_math.
  assert (LegacyPreH10 : (c < k_pre)) by inns_math.
  assert (LegacyPreH11 : (0 <= answer)) by inns_math.
  assert (LegacyPreH12 : (answer <= 19999900000)) by inns_math.
  assert (LegacyPreH13 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l 0) + 1 )) (seen_l)))) by inns_math.
  assert (LegacyPreH14 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) by inns_math.
  assert (LegacyPreH15 : (ChoosingPrefixDataSafe colors_l costs_l (i + 1 ) k_pre seen_next_2 good_l )) by inns_math.
  assert (LegacyPreH16 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l 0) ) seen_l good_l )) by inns_math.
  assert (LegacyPreH17 : (CountArraySafe seen_next_2 k_pre 200000 )) by inns_math.
  assert (LegacyPreH18 : (CountArraySafe good_l k_pre 200000 )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_5 p_pre k_pre n_pre costs_l colors_l seen_next_2 seen_l good_l c i cost answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18) as Hreused.
  rewrite truep_andp_left_equiv in Hreused.
  eapply derivable1_trans.
  { apply sepcon_cancel_res_emp. exact Hreused. }
  Intros.
  Exists seen_next_2.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6.
Proof.
  unfold countChoosingInns_entail_wit_6; try right; intros.
  assert (LegacyPreH1 : (cost > p_pre)) by inns_math.
  assert (LegacyPreH2 : (c = (Znth i colors_l 0))) by inns_math.
  assert (LegacyPreH3 : (cost = (Znth i costs_l 0))) by inns_math.
  assert (LegacyPreH4 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  assert (LegacyPreH5 : (0 <= i)) by inns_math.
  assert (LegacyPreH6 : (i < n_pre)) by inns_math.
  assert (LegacyPreH7 : (0 <= c)) by inns_math.
  assert (LegacyPreH8 : (c < k_pre)) by inns_math.
  assert (LegacyPreH9 : (0 <= cost)) by inns_math.
  assert (LegacyPreH10 : (cost <= 100)) by inns_math.
  assert (LegacyPreH11 : (0 <= answer)) by inns_math.
  assert (LegacyPreH12 : (answer <= 19999900000)) by inns_math.
  assert (LegacyPreH13 : (0 <= (Znth c seen_l_2 0))) by inns_math.
  assert (LegacyPreH14 : ((Znth c seen_l_2 0) <= i)) by inns_math.
  assert (LegacyPreH15 : (0 <= (Znth c good_l 0))) by inns_math.
  assert (LegacyPreH16 : ((Znth c good_l 0) <= i)) by inns_math.
  assert (LegacyPreH17 : ((answer + (Znth c seen_l_2 0) ) <= INT64_MAX)) by inns_math.
  assert (LegacyPreH18 : ((answer + (Znth c good_l 0) ) <= INT64_MAX)) by inns_math.
  assert (LegacyPreH19 : (((Znth c seen_l_2 0) + 1 ) <= INT_MAX)) by inns_math.
  assert (LegacyPreH20 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l_2 good_l )) by inns_math.
  assert (LegacyPreH21 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l_2 good_l )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_6 p_pre k_pre n_pre costs_l colors_l seen_l_2 good_l c i cost answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros seen_l_reused.
  Exists seen_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8.
Proof.
  unfold countChoosingInns_entail_wit_8; try right; intros.
  assert (LegacyPreH1 : (i >= n_pre)) by inns_math.
  assert (LegacyPreH2 : (ChoosingInputSafe colors_l costs_l n_pre k_pre p_pre )) by inns_math.
  assert (LegacyPreH3 : (0 <= i)) by inns_math.
  assert (LegacyPreH4 : (i <= n_pre)) by inns_math.
  assert (LegacyPreH5 : (0 <= answer)) by inns_math.
  assert (LegacyPreH6 : (answer <= 19999900000)) by inns_math.
  assert (LegacyPreH7 : (ChoosingPrefixDataSafe colors_l costs_l i k_pre seen_l good_l )) by inns_math.
  assert (LegacyPreH8 : (ChoosingPrefixState colors_l costs_l i k_pre p_pre answer seen_l good_l )) by inns_math.
  pose proof (ReusedProof.proof_of_countChoosingInns_entail_wit_8 p_pre k_pre n_pre costs_l colors_l seen_l good_l answer i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as Hreused.
  rewrite truep_andp_left_equiv in Hreused.
  eapply derivable1_trans.
  { apply sepcon_cancel_res_emp. exact Hreused. }
  Intros.
  sep_apply (IntArray.full_to_undef_full (&("seen")) k_pre seen_l).
  sep_apply (IntArray.full_to_undef_full (&("good")) k_pre good_l).
  sep_apply (IntArray.undef_full_to_undef_seg (&("seen")) k_pre).
  sep_apply (IntArray.undef_full_to_undef_seg (&("good")) k_pre).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("seen")) 0 k_pre 50); try lia.
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("good")) 0 k_pre 50); try lia.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; inns_math.
Qed.

Lemma proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1.
Proof.
  unfold countChoosingInns_entail_wit_1. left. intros.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("seen")) k_pre 50); try lia.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("good")) k_pre 50); try lia.
  sep_apply (IntArray.undef_seg_to_undef_full (&("seen")) 0 k_pre).
  sep_apply (IntArray.undef_seg_to_undef_full (&("good")) 0 k_pre).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  entailer!.
Qed.
