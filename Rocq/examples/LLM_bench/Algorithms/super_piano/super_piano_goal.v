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
Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function build_prefix -----*)

Definition build_prefix_safety_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps )) (PreH5 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps )) (PreH5 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_3 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref)) = 1)) (PreH5 : ((Znth 0 pref 0) = 0)) (PreH6 : (PrefixArrayPrefix l pref 0 )) (PreH7 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_prefix_safety_wit_4 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_prefix_safety_wit_5 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_prefix_safety_wit_6 := 
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) pref 0) + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) pref 0) + (Znth i l 0) )) ”
) \/
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) pref 0) + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i - 0 ) pref 0) + (Znth i l 0) )) ”
).

Definition build_prefix_safety_wit_6_split_goal_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) pref 0) + (Znth i l 0) ) <= INT_MAX) ”
.

Definition build_prefix_safety_wit_6_split_goal_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ ((INT_MIN) <= ((Znth (i - 0 ) pref 0) + (Znth i l 0) )) ”
.

Definition build_prefix_safety_wit_7 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pref) ((cons (((Znth (i - 0 ) pref 0) + (Znth i l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_prefix_entail_wit_1 := 
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps )) (PreH5 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps 0)) /\ ((Znth idx_2 ps 0) <= INT_MAX)))) (PreH6 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) ,
  (((pre_pre + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (pref)) = 1) ” 
  &&  “ ((Znth 0 pref 0) = 0) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
) \/
(
forall (pre_pre: Z) (n_pre: Z) (l: (@list Z)) (ps: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (PrefixSums l ps )) (PreH7 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps 0)) /\ ((Znth idx_2 ps 0) <= INT_MAX)))) (PreH8 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) ,
  (((pre_pre + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (pref)) = 1) ” 
  &&  “ ((Znth 0 pref 0) = 0) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.seg pre_pre 0 1 pref )
).

Definition build_prefix_entail_wit_2 := 
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref_2)) = 1)) (PreH5 : ((Znth 0 pref_2 0) = 0)) (PreH6 : (PrefixArrayPrefix l pref_2 0 )) (PreH7 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 1 pref_2 )
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (0 + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (0 + 1 ) (n_pre + 1 ) )
) \/
(
forall (pre_pre: Z) (n_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((Zlength (pref_2)) = 1)) (PreH5 : ((Znth 0 pref_2 0) = 0)) (PreH6 : (PrefixArrayPrefix l pref_2 0 )) (PreH7 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.seg pre_pre 0 1 pref_2 )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref 0 ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.seg pre_pre 0 (0 + 1 ) pref )
).

Definition build_prefix_entail_wit_3 := 
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pref_2) ((cons (((Znth (i - 0 ) pref_2 0) + (Znth i l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (pref: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref (i + 1 ) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 ((i + 1 ) + 1 ) pref )
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  TT && emp 
|--
  “ (PrefixArrayPrefix l (app (pref_2) ((cons (((Znth (i - 0 ) pref_2 0) + (Znth i l 0) )) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition build_prefix_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (pref_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref_2 i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (PrefixArrayPrefix l (app (pref_2) ((cons (((Znth (i - 0 ) pref_2 0) + (Znth i l 0) )) ((@nil Z))))) (i + 1 ) )
.

Definition build_prefix_return_wit_1 := 
(
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  EX (ps: (@list Z)) ,
  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full pre_pre (n_pre + 1 ) ps )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx pref 0)) /\ ((Znth idx pref 0) <= INT_MAX))) ” 
  &&  “ (PrefixSums l pref ) ”
  &&  emp
).

Definition build_prefix_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx pref 0)) /\ ((Znth idx pref 0) <= INT_MAX)))
.

Definition build_prefix_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (PrefixSums l pref )
.

Definition build_prefix_partial_solve_wit_1 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (PrefixSums l ps )) (PreH5 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full pre_pre (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (((pre_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg pre_pre 1 (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_prefix_partial_solve_wit_2 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((pre_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) pref 0))
  **  (IntArray.missing_i pre_pre i 0 (i + 1 ) pref )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_partial_solve_wit_3 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
.

Definition build_prefix_partial_solve_wit_4 := 
forall (pre_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pref: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (PrefixArrayPrefix l pref i )) (PreH8 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
  **  (IntArray.undef_seg pre_pre (i + 1 ) (n_pre + 1 ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (PrefixArrayPrefix l pref i ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.seg pre_pre 0 (i + 1 ) pref )
.

(*----- Function superPiano -----*)

Definition superPiano_safety_wit_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps )) (PreH10 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH12 : ((INT64_MIN) <= ans)) (PreH13 : (ans <= INT64_MAX)) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (((n_pre + k_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre + k_pre ) + 1 )) ”
.

Definition superPiano_safety_wit_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps )) (PreH10 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH12 : ((INT64_MIN) <= ans)) (PreH13 : (ans <= INT64_MAX)) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ ((n_pre + k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + k_pre )) ”
.

Definition superPiano_safety_wit_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps )) (PreH10 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH12 : ((INT64_MIN) <= ans)) (PreH13 : (ans <= INT64_MAX)) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_5 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_6 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (heap_cap: Z) (hsize: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps )) (PreH13 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH15 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH16 : ((Zlength (slots)) = heap_cap)) (PreH17 : (NodeArrays slots vals starts los his bests )) (PreH18 : (NodeHeapState slots hsize )) (PreH19 : (InitialFrontierState ps n_pre L_pre R_pre (sublist (0) (hsize) (slots)) )) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_7 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (heap_cap: Z) (hsize: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : (total = 0)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps )) (PreH14 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests )) (PreH19 : (NodeHeapState slots hsize )) (PreH20 : (FrontierState ps n_pre L_pre R_pre (@nil Z) 0 0 (sublist (0) (hsize) (slots)) )) (PreH21 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_8 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize - 1 )) ”
.

Definition superPiano_safety_wit_9 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_10 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((total + value ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + value )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((total + value ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + value )) ”
).

Definition superPiano_safety_wit_10_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((total + value ) <= INT64_MAX) ”
.

Definition superPiano_safety_wit_10_split_goal_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((INT64_MIN) <= (total + value )) ”
.

Definition superPiano_safety_wit_11 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "has_left" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_12 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "left_best" ) )) # Int  |->_)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_13 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_14 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "has_right" ) )) # Int  |->_)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_15 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_best" ) )) # Int  |->_)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_16 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps )) (PreH20 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition superPiano_safety_wit_17 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l query_ps )) (PreH20 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_18 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH4 : (FrontierPopTop pop_slots hsize slots_out )) (PreH5 : (value = (heap_top_value (pop_slots)))) (PreH6 : (start = (heap_top_start (pop_slots)))) (PreH7 : (lo = (heap_top_lo (pop_slots)))) (PreH8 : (hi = (heap_top_hi (pop_slots)))) (PreH9 : (best = (heap_top_best (pop_slots)))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100000)) (PreH12 : (1 <= L_pre)) (PreH13 : (L_pre <= R_pre)) (PreH14 : (R_pre <= n_pre)) (PreH15 : (1 <= k_pre)) (PreH16 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH17 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l query_ps )) (PreH20 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH21 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH22 : ((Zlength (pop_slots)) = heap_cap)) (PreH23 : (NodeArrays pop_slots vals starts los his bests )) (PreH24 : (0 <= t)) (PreH25 : (t < k_pre)) (PreH26 : (0 < hsize)) (PreH27 : (hsize <= heap_cap)) (PreH28 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH29 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH30 : (NodeHeapState pop_slots hsize )) (PreH31 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH32 : (1 <= start)) (PreH33 : (start <= n_pre)) (PreH34 : (0 <= (start - 1 ))) (PreH35 : ((start - 1 ) < (n_pre + 1 ))) (PreH36 : (((start + L_pre ) - 1 ) <= lo)) (PreH37 : (0 <= lo)) (PreH38 : (lo <= best)) (PreH39 : (best <= hi)) (PreH40 : (hi <= n_pre)) (PreH41 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_19 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_20 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_21 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_22 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_23 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
).

Definition superPiano_safety_wit_23_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ”
.

Definition superPiano_safety_wit_23_split_goal_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
.

Definition superPiano_safety_wit_24 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_25 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_26 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_27 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo > (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_28 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_29 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_30 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo > (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_31 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_32 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_33 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_34 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_35 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_36 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition superPiano_safety_wit_37 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_38 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_39 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval_2 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1 ))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval_2 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1 ))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
).

Definition superPiano_safety_wit_39_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval_2 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1 ))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ”
.

Definition superPiano_safety_wit_39_split_goal_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval_2 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < (n_pre + 1 ))) (PreH11 : (lo <= retval_2)) (PreH12 : (retval_2 <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
.

Definition superPiano_safety_wit_40 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_41 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_42 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
).

Definition superPiano_safety_wit_42_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) <= INT_MAX) ”
.

Definition superPiano_safety_wit_42_split_goal_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((INT_MIN) <= ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) ”
.

Definition superPiano_safety_wit_43 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((start - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start - 1 )) ”
.

Definition superPiano_safety_wit_44 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_45 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "right_best" ) )) # Int  |-> retval_2)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_46 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "right_best" ) )) # Int  |-> retval)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_47 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_48 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_49 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 0)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (hi <= best)) (PreH40 : (right_best = 0)) (PreH41 : (right_value = 0)) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition superPiano_safety_wit_50 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 0)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (hi <= best)) (PreH40 : (right_best = 0)) (PreH41 : (right_value = 0)) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_51 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps )) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH27 : (NodeHeapState push_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= (best - 1 ))) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1 ) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH38 : (0 <= left_best)) (PreH39 : (left_best < (n_pre + 1 ))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1 ))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH43 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH44 : (0 <= right_best)) (PreH45 : (right_best < (n_pre + 1 ))) (PreH46 : ((best + 1 ) <= right_best)) (PreH47 : (right_best <= hi)) (PreH48 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH50 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_52 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps )) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH27 : (NodeHeapState push_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= (best - 1 ))) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1 ) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH38 : (0 <= left_best)) (PreH39 : (left_best < (n_pre + 1 ))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1 ))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH43 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH44 : (0 <= right_best)) (PreH45 : (right_best < (n_pre + 1 ))) (PreH46 : ((best + 1 ) <= right_best)) (PreH47 : (right_best <= hi)) (PreH48 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH50 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_53 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps )) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH27 : (NodeHeapState push_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= (best - 1 ))) (PreH34 : (best <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1 ) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH38 : (0 <= left_best)) (PreH39 : (left_best < (n_pre + 1 ))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1 ))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH43 : (hi <= best)) (PreH44 : (right_best = 0)) (PreH45 : (right_value = 0)) (PreH46 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH47 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_54 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l push_ps )) (PreH15 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (push_slots)) = heap_cap)) (PreH18 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH27 : (NodeHeapState push_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= (best - 1 ))) (PreH34 : (best <= hi)) (PreH35 : (hi <= n_pre)) (PreH36 : ((best - 1 ) <= n_pre)) (PreH37 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH38 : (0 <= left_best)) (PreH39 : (left_best < (n_pre + 1 ))) (PreH40 : (lo <= left_best)) (PreH41 : (left_best <= (best - 1 ))) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH43 : (hi <= best)) (PreH44 : (right_best = 0)) (PreH45 : (right_value = 0)) (PreH46 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH47 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_55 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left = 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_56 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left = 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_57 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH52 : (has_right = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_58 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests )) (PreH15 : (has_left = 0)) (PreH16 : (has_right = 0)) (PreH17 : (left_best = 0)) (PreH18 : (left_value = 0)) (PreH19 : (right_best = 0)) (PreH20 : (right_value = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots)) )) (PreH27 : (NodeHeapState slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH35 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH36 : (has_right <> 0)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ False ”
.

Definition superPiano_safety_wit_59 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH49 : (has_right <> 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_60 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH52 : (has_right <> 0)) (PreH53 : (has_left = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ False ”
.

Definition superPiano_safety_wit_61 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH23 : (NodeHeapState right_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (0 <= (best + 1 ))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH34 : (0 <= right_best)) (PreH35 : (right_best < (n_pre + 1 ))) (PreH36 : ((best + 1 ) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH39 : (0 <= lo)) (PreH40 : (lo <= (best - 1 ))) (PreH41 : ((best - 1 ) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH43 : (0 <= left_best)) (PreH44 : (left_best < (n_pre + 1 ))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1 ))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_62 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH23 : (NodeHeapState right_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (0 <= (best + 1 ))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH34 : (0 <= right_best)) (PreH35 : (right_best < (n_pre + 1 ))) (PreH36 : ((best + 1 ) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH39 : (0 <= lo)) (PreH40 : (lo <= (best - 1 ))) (PreH41 : ((best - 1 ) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH43 : (0 <= left_best)) (PreH44 : (left_best < (n_pre + 1 ))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1 ))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_63 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 0)) (PreH16 : (left_best = 0)) (PreH17 : (left_value = 0)) (PreH18 : (has_right = 1)) (PreH19 : (0 <= t)) (PreH20 : (t < k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH25 : (NodeHeapState right_slots hsize )) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : (0 <= (start - 1 ))) (PreH29 : ((start - 1 ) < (n_pre + 1 ))) (PreH30 : (0 <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1 ) <= hi)) (PreH33 : (0 <= (best + 1 ))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH36 : (0 <= right_best)) (PreH37 : (right_best < (n_pre + 1 ))) (PreH38 : ((best + 1 ) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ ((best + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + 1 )) ”
.

Definition superPiano_safety_wit_64 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 0)) (PreH16 : (left_best = 0)) (PreH17 : (left_value = 0)) (PreH18 : (has_right = 1)) (PreH19 : (0 <= t)) (PreH20 : (t < k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH25 : (NodeHeapState right_slots hsize )) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : (0 <= (start - 1 ))) (PreH29 : ((start - 1 ) < (n_pre + 1 ))) (PreH30 : (0 <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1 ) <= hi)) (PreH33 : (0 <= (best + 1 ))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH36 : (0 <= right_best)) (PreH37 : (right_best < (n_pre + 1 ))) (PreH38 : ((best + 1 ) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_65 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH27 : (NodeHeapState right_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (0 <= (best + 1 ))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH38 : (0 <= right_best)) (PreH39 : (right_best < (n_pre + 1 ))) (PreH40 : ((best + 1 ) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH43 : (0 <= lo)) (PreH44 : (lo <= (best - 1 ))) (PreH45 : ((best - 1 ) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH47 : (0 <= left_best)) (PreH48 : (left_best < (n_pre + 1 ))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1 ))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH53 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_66 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH27 : (NodeHeapState right_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (0 <= (best + 1 ))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH38 : (0 <= right_best)) (PreH39 : (right_best < (n_pre + 1 ))) (PreH40 : ((best + 1 ) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH43 : (0 <= lo)) (PreH44 : (lo <= (best - 1 ))) (PreH45 : ((best - 1 ) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH47 : (0 <= left_best)) (PreH48 : (left_best < (n_pre + 1 ))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1 ))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH53 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_67 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 0)) (PreH20 : (left_best = 0)) (PreH21 : (left_value = 0)) (PreH22 : (has_right = 1)) (PreH23 : (0 <= t)) (PreH24 : (t < k_pre)) (PreH25 : (0 <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH29 : (NodeHeapState right_slots hsize )) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : (0 <= (start - 1 ))) (PreH33 : ((start - 1 ) < (n_pre + 1 ))) (PreH34 : (0 <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1 ) <= hi)) (PreH37 : (0 <= (best + 1 ))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ ((hsize + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hsize + 1 )) ”
.

Definition superPiano_safety_wit_68 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 0)) (PreH20 : (left_best = 0)) (PreH21 : (left_value = 0)) (PreH22 : (has_right = 1)) (PreH23 : (0 <= t)) (PreH24 : (t < k_pre)) (PreH25 : (0 <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH29 : (NodeHeapState right_slots hsize )) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : (0 <= (start - 1 ))) (PreH33 : ((start - 1 ) < (n_pre + 1 ))) (PreH34 : (0 <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1 ) <= hi)) (PreH37 : (0 <= (best + 1 ))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition superPiano_safety_wit_69 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (right_best: Z) (left_value: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (hi: Z) (lo: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests )) (PreH15 : (0 <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : (0 <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : (0 <= left_best)) (PreH20 : (left_best < (n_pre + 1 ))) (PreH21 : (0 <= right_best)) (PreH22 : (right_best < (n_pre + 1 ))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : (0 <= t)) (PreH28 : (t < k_pre)) (PreH29 : (0 <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH32 : (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) (hsize) (slots)) )) (PreH33 : (NodeHeapState slots hsize )) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : (0 <= (start - 1 ))) (PreH38 : ((start - 1 ) < (n_pre + 1 ))) (PreH39 : (((start + L_pre ) - 1 ) <= lo)) (PreH40 : (0 <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition superPiano_entail_wit_1 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (ps_3: (@list Z)) (PreH1 : (PrefixSums l ps_3 )) (PreH2 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_3 0)) /\ ((Znth idx_3 ps_3 0) <= INT_MAX)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= L_pre)) (PreH6 : (L_pre <= R_pre)) (PreH7 : (R_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2 )) (PreH12 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_4 ps_2 0)) /\ ((Znth idx_4 ps_2 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH14 : ((INT64_MIN) <= ans_2)) (PreH15 : (ans_2 <= INT64_MAX)) (PreH16 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> (((-1000) <= (Znth idx_5 l 0)) /\ ((Znth idx_5 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_3 )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  EX (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (ps_3: (@list Z)) (PreH1 : (PrefixSums l ps_3 )) (PreH2 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_3 0)) /\ ((Znth idx_3 ps_3 0) <= INT_MAX)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= L_pre)) (PreH6 : (L_pre <= R_pre)) (PreH7 : (R_pre <= n_pre)) (PreH8 : (1 <= k_pre)) (PreH9 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2 )) (PreH12 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_4 ps_2 0)) /\ ((Znth idx_4 ps_2 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH14 : ((INT64_MIN) <= ans_2)) (PreH15 : (ans_2 <= INT64_MAX)) (PreH16 : forall (idx_5: Z) , (((0 <= idx_5) /\ (idx_5 < n_pre)) -> (((-1000) <= (Znth idx_5 l 0)) /\ ((Znth idx_5 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (ans: Z)  (st_slots: (@list Z)) ,
  “ ((Zlength (st_slots)) = (((Zlength (l)) + 1 ) * ST_LEVELS )) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_3 (Zlength (l)) L_pre R_pre k_pre ans ) ”
  &&  emp
).

Definition superPiano_entail_wit_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (st_out: (@list Z)) (PreH1 : (SparseArgmaxBuilt ps_2 st_out (n_pre + 1 ) )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2 )) (PreH12 : ((Zlength (st_slots_2)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH13 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH14 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH15 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  EX (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
.

Definition superPiano_entail_wit_3 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (heap_cap: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (PreH1 : (retval = ((n_pre - L_pre ) + 1 ))) (PreH2 : ((Zlength (slots_2)) = heap_cap)) (PreH3 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH4 : (NodeHeapState slots_2 retval )) (PreH5 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (retval) (slots_2)) )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps_2 )) (PreH16 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH17 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH18 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (retval = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((retval + k_pre ) < heap_cap) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots retval ) ” 
  &&  “ (InitialFrontierState ps n_pre L_pre R_pre (sublist (0) (retval) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (heap_cap: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (retval: Z) (PreH1 : (retval = ((n_pre - L_pre ) + 1 ))) (PreH2 : ((Zlength (slots_2)) = heap_cap)) (PreH3 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH4 : (NodeHeapState slots_2 retval )) (PreH5 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (retval) (slots_2)) )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps_2 )) (PreH16 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH17 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH18 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH19 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (((((Zlength (l)) - L_pre ) + 1 ) + k_pre ) < (Zlength (slots_2))) ” 
  &&  “ ((Zlength (slots)) = (Zlength (slots_2))) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots (((Zlength (l)) - L_pre ) + 1 ) ) ” 
  &&  “ (InitialFrontierState ps_2 (Zlength (l)) L_pre R_pre (sublist (0) ((((Zlength (l)) - L_pre ) + 1 )) (slots)) ) ”
  &&  emp
).

Definition superPiano_entail_wit_4 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps_2 )) (PreH13 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH15 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH16 : ((Zlength (slots_2)) = heap_cap)) (PreH17 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH18 : (NodeHeapState slots_2 hsize )) (PreH19 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (hsize) (slots_2)) )) (PreH20 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (hsize = ((n_pre - L_pre ) + 1 )) ” 
  &&  “ ((hsize + k_pre ) < heap_cap) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (@nil Z) 0 0 (sublist (0) (hsize) (slots)) ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : (PrefixSums l ps_2 )) (PreH13 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH14 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH15 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH16 : ((Zlength (slots_2)) = heap_cap)) (PreH17 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH18 : (NodeHeapState slots_2 hsize )) (PreH19 : (InitialFrontierState ps_2 n_pre L_pre R_pre (sublist (0) (hsize) (slots_2)) )) (PreH20 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (NodeHeapState slots (((Zlength (l)) - L_pre ) + 1 ) ) ” 
  &&  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre (@nil Z) 0 0 (sublist (0) ((((Zlength (l)) - L_pre ) + 1 )) (slots)) ) ”
  &&  emp
).

Definition superPiano_entail_wit_5 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : (total = 0)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps_2 )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps_2 0)) /\ ((Znth idx_2 ps_2 0) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (slots_2)) = heap_cap)) (PreH18 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH19 : (NodeHeapState slots_2 hsize )) (PreH20 : (FrontierState ps_2 n_pre L_pre R_pre (@nil Z) 0 0 (sublist (0) (hsize) (slots_2)) )) (PreH21 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - 0 ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen 0 total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((0 < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (heap_cap: Z) (hsize: Z) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : (hsize = ((n_pre - L_pre ) + 1 ))) (PreH10 : ((hsize + k_pre ) < heap_cap)) (PreH11 : (total = 0)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (PrefixSums l ps_2 )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_2 ps_2 0)) /\ ((Znth idx_2 ps_2 0) <= INT_MAX)))) (PreH15 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (slots_2)) = heap_cap)) (PreH18 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH19 : (NodeHeapState slots_2 hsize )) (PreH20 : (FrontierState ps_2 n_pre L_pre R_pre (@nil Z) 0 0 (sublist (0) (hsize) (slots_2)) )) (PreH21 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= (((Zlength (l)) - L_pre ) + 1 )) ” 
  &&  “ ((((Zlength (l)) - L_pre ) + 1 ) <= (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (((((Zlength (l)) - L_pre ) + 1 ) + (k_pre - 0 ) ) < (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen 0 0 (sublist (0) ((((Zlength (l)) - L_pre ) + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (((Zlength (l)) - L_pre ) + 1 ) ) ” 
  &&  “ ((0 < k_pre) -> (0 < (((Zlength (l)) - L_pre ) + 1 ))) ”
  &&  emp
).

Definition superPiano_entail_wit_6 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans_2: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (heap_top_best (slots_2)))) (PreH2 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH3 : (NodeHeapState slots_2 hsize )) (PreH4 : (retval_4 = (heap_top_hi (slots_2)))) (PreH5 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH6 : (NodeHeapState slots_2 hsize )) (PreH7 : (retval_3 = (heap_top_lo (slots_2)))) (PreH8 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH9 : (NodeHeapState slots_2 hsize )) (PreH10 : (retval_2 = (heap_top_start (slots_2)))) (PreH11 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH12 : (NodeHeapState slots_2 hsize )) (PreH13 : (retval = (heap_top_value (slots_2)))) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (NodeHeapState slots_2 hsize )) (PreH16 : (t < k_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l ps_2 )) (PreH27 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH29 : ((Zlength (slots_2)) = heap_cap)) (PreH30 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH31 : (0 <= t)) (PreH32 : (t <= k_pre)) (PreH33 : (0 <= hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) )) (PreH37 : (NodeHeapState slots_2 hsize )) (PreH38 : ((t < k_pre) -> (0 < hsize))) (PreH39 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (retval_5 = (heap_top_best (slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5 ) ” 
  &&  “ (1 <= retval_2) ” 
  &&  “ (retval_2 <= n_pre) ” 
  &&  “ (0 <= (retval_2 - 1 )) ” 
  &&  “ ((retval_2 - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((retval_2 + L_pre ) - 1 ) <= retval_3) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= retval_5) ” 
  &&  “ (retval_5 <= retval_4) ” 
  &&  “ (retval_4 <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans_2: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (heap_top_best (slots_2)))) (PreH2 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH3 : (NodeHeapState slots_2 hsize )) (PreH4 : (retval_4 = (heap_top_hi (slots_2)))) (PreH5 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH6 : (NodeHeapState slots_2 hsize )) (PreH7 : (retval_3 = (heap_top_lo (slots_2)))) (PreH8 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH9 : (NodeHeapState slots_2 hsize )) (PreH10 : (retval_2 = (heap_top_start (slots_2)))) (PreH11 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH12 : (NodeHeapState slots_2 hsize )) (PreH13 : (retval = (heap_top_value (slots_2)))) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (NodeHeapState slots_2 hsize )) (PreH16 : (t < k_pre)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l ps_2 )) (PreH27 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH29 : ((Zlength (slots_2)) = heap_cap)) (PreH30 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH31 : (0 <= t)) (PreH32 : (t <= k_pre)) (PreH33 : (0 <= hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (slots_2)) )) (PreH37 : (NodeHeapState slots_2 hsize )) (PreH38 : ((t < k_pre) -> (0 < hsize))) (PreH39 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((heap_top_value (slots_2)) = (heap_top_value (slots))) ” 
  &&  “ ((heap_top_start (slots_2)) = (heap_top_start (slots))) ” 
  &&  “ ((heap_top_lo (slots_2)) = (heap_top_lo (slots))) ” 
  &&  “ ((heap_top_hi (slots_2)) = (heap_top_hi (slots))) ” 
  &&  “ ((heap_top_best (slots_2)) = (heap_top_best (slots))) ” 
  &&  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps_2 (Zlength (l)) L_pre R_pre (heap_top_value (slots_2)) (heap_top_start (slots_2)) (heap_top_lo (slots_2)) (heap_top_hi (slots_2)) (heap_top_best (slots_2)) ) ” 
  &&  “ (1 <= (heap_top_start (slots_2))) ” 
  &&  “ ((heap_top_start (slots_2)) <= (Zlength (l))) ” 
  &&  “ (0 <= ((heap_top_start (slots_2)) - 1 )) ” 
  &&  “ (((heap_top_start (slots_2)) - 1 ) < ((Zlength (l)) + 1 )) ” 
  &&  “ ((((heap_top_start (slots_2)) + L_pre ) - 1 ) <= (heap_top_lo (slots_2))) ” 
  &&  “ (0 <= (heap_top_lo (slots_2))) ” 
  &&  “ ((heap_top_lo (slots_2)) <= (heap_top_best (slots_2))) ” 
  &&  “ ((heap_top_best (slots_2)) <= (heap_top_hi (slots_2))) ” 
  &&  “ ((heap_top_hi (slots_2)) <= (Zlength (l))) ”
  &&  emp
).

Definition superPiano_entail_wit_7 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) (start) (lo) ((best - 1 )) (retval))) ((cons ((mkNode (((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) )) (start) ((best + 1 )) (hi) (retval_2))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) start lo (best - 1 ) retval ) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval_2 query_ps 0) - (Znth (start - 1 ) query_ps 0) ) start (best + 1 ) hi retval_2 ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1 ) ) ” 
  &&  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < (Zlength (slots_out))) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots))))) (chosen)) (t + 1 ) (total + (heap_top_value (pop_slots)) ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) )) ((heap_top_start (pop_slots))) ((heap_top_lo (pop_slots))) (((heap_top_best (pop_slots)) - 1 )) (retval))) ((cons ((mkNode (((Znth retval_2 query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) )) ((heap_top_start (pop_slots))) (((heap_top_best (pop_slots)) + 1 )) ((heap_top_hi (pop_slots))) (retval_2))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (((heap_top_best (pop_slots)) - 1 ) <= (Zlength (l))) ” 
  &&  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) ) (heap_top_start (pop_slots)) (heap_top_lo (pop_slots)) ((heap_top_best (pop_slots)) - 1 ) retval ) ” 
  &&  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval_2 query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) ) (heap_top_start (pop_slots)) ((heap_top_best (pop_slots)) + 1 ) (heap_top_hi (pop_slots)) retval_2 ) ”
  &&  emp
).

Definition superPiano_entail_wit_8 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) > hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) (start) (lo) ((best - 1 )) (retval))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) start lo (best - 1 ) retval ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) > hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1 ) ) ” 
  &&  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < (Zlength (slots_out))) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots))))) (chosen)) (t + 1 ) (total + (heap_top_value (pop_slots)) ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) )) ((heap_top_start (pop_slots))) ((heap_top_lo (pop_slots))) (((heap_top_best (pop_slots)) - 1 )) (retval))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (((heap_top_best (pop_slots)) - 1 ) <= (Zlength (l))) ” 
  &&  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) ) (heap_top_start (pop_slots)) (heap_top_lo (pop_slots)) ((heap_top_best (pop_slots)) - 1 ) retval ) ” 
  &&  “ ((heap_top_hi (pop_slots)) <= (heap_top_best (pop_slots))) ”
  &&  emp
).

Definition superPiano_entail_wit_9 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) > hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ (((hsize - 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) > hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < (Zlength (slots_out))) ” 
  &&  “ (((hsize - 1 ) + (k_pre - (t + 1 ) ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots))))) (chosen)) (t + 1 ) (total + (heap_top_value (pop_slots)) ) (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ ((heap_top_lo (pop_slots)) = (heap_top_best (pop_slots))) ” 
  &&  “ ((heap_top_best (pop_slots)) = (heap_top_hi (pop_slots))) ”
  &&  emp
).

Definition superPiano_entail_wit_10_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals starts los his bests )) (PreH15 : (has_left = 0)) (PreH16 : (has_right = 0)) (PreH17 : (left_best = 0)) (PreH18 : (left_value = 0)) (PreH19 : (right_best = 0)) (PreH20 : (right_value = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots)) )) (PreH27 : (NodeHeapState slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH35 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH36 : (has_right = 0)) ,
  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
.

Definition superPiano_entail_wit_10_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH49 : (has_right = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
.

Definition superPiano_entail_wit_10_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_3: Z) (st_slots_3: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize_3: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out_2)) = heap_cap)) (PreH3 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 )) (PreH4 : (NodeHeapState slots_out_2 (hsize_3 + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize_3 left_value start lo (best - 1 ) left_best slots_out_2 )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_3 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_3 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize_3)) (PreH25 : (hsize_3 < heap_cap)) (PreH26 : (((hsize_3 + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize_3) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize_3 )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) (PreH52 : (has_right = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_3 + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_3 )
|--
  (EX (chosen: (@list Z))  (hsize: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (lo = best) ” 
  &&  “ (best = hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests ))
  ||
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen_2: (@list Z))  (hsize_2: Z)  (ans_2: Z)  (st_slots_2: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize_2 + 1 ) ) ” 
  &&  “ (FrontierPushFields push_slots hsize_2 left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize_2) ” 
  &&  “ (hsize_2 < heap_cap) ” 
  &&  “ (((hsize_2 + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize_2) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize_2 ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ (has_right = 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 + 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 ))
.

Definition superPiano_entail_wit_11_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (ps: (@list Z)) (ans_3: Z) (st_slots_2: (@list Z)) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left_2: Z) (has_right_2: Z) (left_best_2: Z) (left_value_2: Z) (right_best: Z) (right_value_2: Z) (t: Z) (hsize_3: Z) (total_3: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : (SparseArgmaxBuilt ps st_slots_2 (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans_3 )) (PreH13 : ((Zlength (slots)) = heap_cap)) (PreH14 : (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (has_left_2 = 0)) (PreH16 : (has_right_2 = 0)) (PreH17 : (left_best_2 = 0)) (PreH18 : (left_value_2 = 0)) (PreH19 : (right_best = 0)) (PreH20 : (right_value_2 = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize_3)) (PreH24 : (hsize_3 < heap_cap)) (PreH25 : ((hsize_3 + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH26 : (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total_3 (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize_3) (slots)) )) (PreH27 : (NodeHeapState slots hsize_3 )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH35 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) (PreH36 : (has_right_2 <> 0)) ,
  ((( &( "has_left" ) )) # Int  |-> has_left_2)
  **  ((( &( "has_right" ) )) # Int  |-> has_right_2)
  **  ((( &( "left_best" ) )) # Int  |-> left_best_2)
  **  ((( &( "left_value" ) )) # Int  |-> left_value_2)
  **  ((( &( "right_value" ) )) # Int  |-> right_value_2)
  **  ((( &( "hsize" ) )) # Int  |-> hsize_3)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  (EX (push_ps: (@list Z))  (push_slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (push_vals: (@list Z))  (push_starts: (@list Z))  (push_los: (@list Z))  (push_his: (@list Z))  (push_bests: (@list Z))  (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (total: Z)  (left_value: Z)  (left_best: Z)  (right_value: Z)  (hsize: Z)  (has_right: Z)  (has_left: Z)  (ans: Z)  (st_slots: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax push_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (EX (ans_2: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (chosen_2: (@list Z))  (hsize_2: Z)  (total_2: Z)  (vals_out_2: (@list Z))  (starts_out_2: (@list Z))  (los_out_2: (@list Z))  (his_out_2: (@list Z))  (bests_out_2: (@list Z))  (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax query_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total_2 (sublist (0) (hsize_2) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize_2 ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total_2 + value ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_11_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (ans_3: Z) (st_slots_2: (@list Z)) (chosen_3: (@list Z)) (heap_cap: Z) (has_left_2: Z) (has_right_2: Z) (t: Z) (hsize_3: Z) (left_best_2: Z) (best: Z) (lo: Z) (start: Z) (left_value_2: Z) (total_3: Z) (hi: Z) (right_best: Z) (right_value_2: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out_3: (@list Z)) (starts_out_3: (@list Z)) (los_out_3: (@list Z)) (his_out_3: (@list Z)) (bests_out_3: (@list Z)) (slots_out_3: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left_2 <> 0)) (PreH2 : ((Zlength (slots_out_3)) = heap_cap)) (PreH3 : (NodeArrays slots_out_3 vals_out_3 starts_out_3 los_out_3 his_out_3 bests_out_3 )) (PreH4 : (NodeHeapState slots_out_3 (hsize_3 + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize_3 left_value_2 start lo (best - 1 ) left_best_2 slots_out_3 )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_3 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left_2 = 1)) (PreH21 : (has_right_2 = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize_3)) (PreH25 : (hsize_3 < heap_cap)) (PreH26 : (((hsize_3 + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_3)) (t + 1 ) total_3 (cons ((mkNode (left_value_2) (start) (lo) ((best - 1 )) (left_best_2))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize_3) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize_3 )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best_2 )) (PreH39 : (0 <= left_best_2)) (PreH40 : (left_best_2 < (n_pre + 1 ))) (PreH41 : (lo <= left_best_2)) (PreH42 : (left_best_2 <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value_2 start lo (best - 1 ) left_best_2 )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value_2 = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < n_pre)) -> (((-1000) <= (Znth idx_3 l 0)) /\ ((Znth idx_3 l 0) <= 1000)))) (PreH49 : (has_right_2 <> 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out_3 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_3 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_3 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_3 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_3 )
  **  ((( &( "has_left" ) )) # Int  |-> has_left_2)
  **  ((( &( "has_right" ) )) # Int  |-> has_right_2)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_3 + 1 ))
  **  ((( &( "left_best" ) )) # Int  |-> left_best_2)
  **  ((( &( "left_value" ) )) # Int  |-> left_value_2)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  ((( &( "right_value" ) )) # Int  |-> right_value_2)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  (EX (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z)))  (chosen: (@list Z))  (total: Z)  (left_value: Z)  (left_best: Z)  (right_value: Z)  (hsize: Z)  (has_right: Z)  (has_left: Z)  (ans: Z)  (st_slots: (@list Z)) ,
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax push_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots ))
  ||
  (EX (ans_2: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (chosen_2: (@list Z))  (hsize_2: Z)  (total_2: Z)  (vals_out_2: (@list Z))  (starts_out_2: (@list Z))  (los_out_2: (@list Z))  (his_out_2: (@list Z))  (bests_out_2: (@list Z))  (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax query_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total_2 (sublist (0) (hsize_2) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize_2 ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total_2 + value ))
  **  (IntArray.full arr_pre n_pre l ))
.

Definition superPiano_entail_wit_11_3 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) (PreH52 : (has_right <> 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (has_left <> 0) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize + 1 ) ) ” 
  &&  “ (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax push_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ” 
  &&  “ (has_right <> 0) ”
  &&  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_entail_wit_11_4 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize_2: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out_2)) = heap_cap)) (PreH10 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 )) (PreH11 : (NodeHeapState slots_out_2 (hsize_2 - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize_2 slots_out_2 )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize_2)) (PreH35 : (hsize_2 <= heap_cap)) (PreH36 : ((hsize_2 + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize_2) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize_2 )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out_2)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 ) ” 
  &&  “ (NodeHeapState slots_out_2 (hsize_2 - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize_2 slots_out_2 ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize_2) ” 
  &&  “ (hsize_2 <= heap_cap) ” 
  &&  “ ((hsize_2 + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize_2) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize_2 ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 - 1 ))
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_entail_wit_12_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (ans_2: Z) (st_slots: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize_2: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total_2: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out_2: (@list Z)) (starts_out_2: (@list Z)) (los_out_2: (@list Z)) (his_out_2: (@list Z)) (bests_out_2: (@list Z)) (slots_out_2: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out_2)) = heap_cap)) (PreH3 : (NodeArrays slots_out_2 vals_out_2 starts_out_2 los_out_2 his_out_2 bests_out_2 )) (PreH4 : (NodeHeapState slots_out_2 (hsize_2 + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize_2 left_value start lo (best - 1 ) left_best slots_out_2 )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize_2)) (PreH25 : (hsize_2 < heap_cap)) (PreH26 : (((hsize_2 + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total_2 (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize_2) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize_2 )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH52 : (has_right <> 0)) (PreH53 : (has_left = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_out_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_out_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_out_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_out_2 )
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize_2 + 1 ))
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total_2)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  EX (ans: Z)  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (chosen: (@list Z))  (hsize: Z)  (total: Z)  (vals_out: (@list Z))  (starts_out: (@list Z))  (los_out: (@list Z))  (his_out: (@list Z))  (bests_out: (@list Z))  (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (RangeArgmax query_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> ((Znth right_best query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "has_right" ) )) # Int  |-> 1)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_entail_wit_12_2 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_entail_wit_13 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH52 : (has_right <> 0)) (PreH53 : (has_left <> 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 1)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : ((best + 1 ) <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH45 : (0 <= right_best)) (PreH46 : (right_best < (n_pre + 1 ))) (PreH47 : ((best + 1 ) <= right_best)) (PreH48 : (right_best <= hi)) (PreH49 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH50 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH51 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH52 : (has_right <> 0)) (PreH53 : (has_left <> 0)) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierSplitState push_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (lo <= best) ” 
  &&  “ (0 <= (best + 1 )) ”
  &&  emp
).

Definition superPiano_entail_wit_14 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < heap_cap) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) (total + value ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) )) (start) ((best + 1 )) (hi) (retval))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ) start (best + 1 ) hi retval ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen_2 t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (SparseArgmaxBuilt query_ps query_st_slots ((Zlength (l)) + 1 ) ) ” 
  &&  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= (hsize - 1 )) ” 
  &&  “ ((hsize - 1 ) < (Zlength (slots_out))) ” 
  &&  “ ((((hsize - 1 ) + 1 ) + (k_pre - t ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierSplitState query_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) ((heap_top_start (pop_slots))) ((heap_top_best (pop_slots))))) (chosen)) (t + 1 ) (total + (heap_top_value (pop_slots)) ) (cons ((mkNode (((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) )) ((heap_top_start (pop_slots))) (((heap_top_best (pop_slots)) + 1 )) ((heap_top_hi (pop_slots))) (retval))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) ((hsize - 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize - 1 ) ) ” 
  &&  “ (0 <= ((heap_top_best (pop_slots)) + 1 )) ” 
  &&  “ (ValidNodeFields query_ps (Zlength (l)) L_pre R_pre ((Znth retval query_ps 0) - (Znth ((heap_top_start (pop_slots)) - 1 ) query_ps 0) ) (heap_top_start (pop_slots)) ((heap_top_best (pop_slots)) + 1 ) (heap_top_hi (pop_slots)) retval ) ”
  &&  emp
).

Definition superPiano_entail_wit_15_1 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH27 : (NodeHeapState right_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (0 <= (best + 1 ))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH38 : (0 <= right_best)) (PreH39 : (right_best < (n_pre + 1 ))) (PreH40 : ((best + 1 ) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH43 : (0 <= lo)) (PreH44 : (lo <= (best - 1 ))) (PreH45 : ((best - 1 ) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH47 : (0 <= left_best)) (PreH48 : (left_best < (n_pre + 1 ))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1 ))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH53 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 1)) (PreH20 : (has_right = 1)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH26 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH27 : (NodeHeapState right_slots hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (0 <= lo)) (PreH33 : (lo <= best)) (PreH34 : ((best + 1 ) <= hi)) (PreH35 : (0 <= (best + 1 ))) (PreH36 : (hi <= n_pre)) (PreH37 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH38 : (0 <= right_best)) (PreH39 : (right_best < (n_pre + 1 ))) (PreH40 : ((best + 1 ) <= right_best)) (PreH41 : (right_best <= hi)) (PreH42 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH43 : (0 <= lo)) (PreH44 : (lo <= (best - 1 ))) (PreH45 : ((best - 1 ) <= n_pre)) (PreH46 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH47 : (0 <= left_best)) (PreH48 : (left_best < (n_pre + 1 ))) (PreH49 : (lo <= left_best)) (PreH50 : (left_best <= (best - 1 ))) (PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH53 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < (Zlength (slots_out))) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierState right_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (best <= hi) ”
  &&  emp
).

Definition superPiano_entail_wit_15_2 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 0)) (PreH20 : (left_best = 0)) (PreH21 : (left_value = 0)) (PreH22 : (has_right = 1)) (PreH23 : (0 <= t)) (PreH24 : (t < k_pre)) (PreH25 : (0 <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH29 : (NodeHeapState right_slots hsize )) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : (0 <= (start - 1 ))) (PreH33 : ((start - 1 ) < (n_pre + 1 ))) (PreH34 : (0 <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1 ) <= hi)) (PreH37 : (0 <= (best + 1 ))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : ((Zlength (slots_out)) = heap_cap)) (PreH2 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH3 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH4 : (FrontierPushFields right_slots hsize right_value start (best + 1 ) hi right_best slots_out )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l right_ps )) (PreH15 : (SparseArgmaxBuilt right_ps st_slots_2 (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH17 : ((Zlength (right_slots)) = heap_cap)) (PreH18 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH19 : (has_left = 0)) (PreH20 : (left_best = 0)) (PreH21 : (left_value = 0)) (PreH22 : (has_right = 1)) (PreH23 : (0 <= t)) (PreH24 : (t < k_pre)) (PreH25 : (0 <= hsize)) (PreH26 : (hsize < heap_cap)) (PreH27 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH28 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH29 : (NodeHeapState right_slots hsize )) (PreH30 : (1 <= start)) (PreH31 : (start <= n_pre)) (PreH32 : (0 <= (start - 1 ))) (PreH33 : ((start - 1 ) < (n_pre + 1 ))) (PreH34 : (0 <= lo)) (PreH35 : (lo <= best)) (PreH36 : ((best + 1 ) <= hi)) (PreH37 : (0 <= (best + 1 ))) (PreH38 : (hi <= n_pre)) (PreH39 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < ((Zlength (l)) + 1 )) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < (Zlength (slots_out))) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierState right_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (best <= hi) ”
  &&  emp
).

Definition superPiano_entail_wit_15_3 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2 )) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (has_left = 0)) (PreH16 : (has_right = 0)) (PreH17 : (left_best = 0)) (PreH18 : (left_value = 0)) (PreH19 : (right_best = 0)) (PreH20 : (right_value = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH26 : (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots_2)) )) (PreH27 : (NodeHeapState slots_2 hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best )) (PreH35 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH36 : (has_right = 0)) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (left_value: Z) (right_best: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (lo: Z) (hi: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2 )) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (has_left = 0)) (PreH16 : (has_right = 0)) (PreH17 : (left_best = 0)) (PreH18 : (left_value = 0)) (PreH19 : (right_best = 0)) (PreH20 : (right_value = 0)) (PreH21 : (0 <= t)) (PreH22 : (t < k_pre)) (PreH23 : (0 <= hsize)) (PreH24 : (hsize < heap_cap)) (PreH25 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH26 : (FrontierSplitState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (@nil ((((Z * Z) * Z) * Z) * Z)) (sublist (0) (hsize) (slots_2)) )) (PreH27 : (NodeHeapState slots_2 hsize )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (lo = best)) (PreH33 : (best = hi)) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best )) (PreH35 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH36 : (has_right = 0)) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < ((Zlength (l)) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < ((Zlength (l)) + 1 )) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) (start) (hi))) (chosen)) (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (((start + L_pre ) - 1 ) <= hi) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi <= hi) ” 
  &&  “ (hi <= hi) ” 
  &&  “ (hi <= (Zlength (l))) ”
  &&  emp
).

Definition superPiano_entail_wit_15_4 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH49 : (has_right = 0)) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= has_left) ” 
  &&  “ (has_left <= 1) ” 
  &&  “ (0 <= has_right) ” 
  &&  “ (has_right <= 1) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= right_value) ” 
  &&  “ (right_value <= INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (has_left <> 0)) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize + 1 ) )) (PreH5 : (FrontierPushFields push_slots hsize left_value start lo (best - 1 ) left_best slots_out )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l push_ps )) (PreH16 : (SparseArgmaxBuilt push_ps st_slots_2 (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans_2 )) (PreH18 : ((Zlength (push_slots)) = heap_cap)) (PreH19 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH20 : (has_left = 1)) (PreH21 : (has_right = 0)) (PreH22 : (0 <= t)) (PreH23 : (t < k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize < heap_cap)) (PreH26 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH28 : (NodeHeapState push_slots hsize )) (PreH29 : (1 <= start)) (PreH30 : (start <= n_pre)) (PreH31 : (0 <= (start - 1 ))) (PreH32 : ((start - 1 ) < (n_pre + 1 ))) (PreH33 : (0 <= lo)) (PreH34 : (lo <= (best - 1 ))) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : ((best - 1 ) <= n_pre)) (PreH38 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH39 : (0 <= left_best)) (PreH40 : (left_best < (n_pre + 1 ))) (PreH41 : (lo <= left_best)) (PreH42 : (left_best <= (best - 1 ))) (PreH43 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH44 : (hi <= best)) (PreH45 : (right_best = 0)) (PreH46 : (right_value = 0)) (PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH48 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) (PreH49 : (has_right = 0)) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (Zlength (slots_out))) ” 
  &&  “ (NodeArrays slots vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < ((Zlength (l)) + 1 )) ” 
  &&  “ (INT_MIN <= left_value) ” 
  &&  “ (left_value <= INT_MAX) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= (hsize + 1 )) ” 
  &&  “ ((hsize + 1 ) < (Zlength (slots_out))) ” 
  &&  “ (((hsize + 1 ) + (k_pre - (t + 1 ) ) ) < (Zlength (slots_out))) ” 
  &&  “ (FrontierState push_ps (Zlength (l)) L_pre R_pre (cons ((ChordCode ((Zlength (l))) (start) (best))) (chosen)) (t + 1 ) total (sublist (0) ((hsize + 1 )) (slots)) ) ” 
  &&  “ (NodeHeapState slots (hsize + 1 ) ) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (lo <= best) ”
  &&  emp
).

Definition superPiano_entail_wit_16 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (right_best: Z) (left_value: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (hi: Z) (lo: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2 )) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (0 <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : (0 <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : (0 <= left_best)) (PreH20 : (left_best < (n_pre + 1 ))) (PreH21 : (0 <= right_best)) (PreH22 : (right_best < (n_pre + 1 ))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : (0 <= t)) (PreH28 : (t < k_pre)) (PreH29 : (0 <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH32 : (FrontierState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (sublist (0) (hsize) (slots_2)) )) (PreH33 : (NodeHeapState slots_2 hsize )) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best )) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : (0 <= (start - 1 ))) (PreH38 : ((start - 1 ) < (n_pre + 1 ))) (PreH39 : (((start + L_pre ) - 1 ) <= lo)) (PreH40 : (0 <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (chosen: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ans: Z)  (st_slots: (@list Z))  (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (((t + 1 ) < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
) \/
(
forall (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans_2: Z) (st_slots_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (chosen_2: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (left_best: Z) (right_best: Z) (left_value: Z) (right_value: Z) (t: Z) (hsize: Z) (total: Z) (best: Z) (start: Z) (hi: Z) (lo: Z) (value: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps_2 )) (PreH11 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2 )) (PreH13 : ((Zlength (slots_2)) = heap_cap)) (PreH14 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH15 : (0 <= has_left)) (PreH16 : (has_left <= 1)) (PreH17 : (0 <= has_right)) (PreH18 : (has_right <= 1)) (PreH19 : (0 <= left_best)) (PreH20 : (left_best < (n_pre + 1 ))) (PreH21 : (0 <= right_best)) (PreH22 : (right_best < (n_pre + 1 ))) (PreH23 : (INT_MIN <= left_value)) (PreH24 : (left_value <= INT_MAX)) (PreH25 : (INT_MIN <= right_value)) (PreH26 : (right_value <= INT_MAX)) (PreH27 : (0 <= t)) (PreH28 : (t < k_pre)) (PreH29 : (0 <= hsize)) (PreH30 : (hsize < heap_cap)) (PreH31 : ((hsize + (k_pre - (t + 1 ) ) ) < heap_cap)) (PreH32 : (FrontierState ps_2 n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen_2)) (t + 1 ) total (sublist (0) (hsize) (slots_2)) )) (PreH33 : (NodeHeapState slots_2 hsize )) (PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best )) (PreH35 : (1 <= start)) (PreH36 : (start <= n_pre)) (PreH37 : (0 <= (start - 1 ))) (PreH38 : ((start - 1 ) < (n_pre + 1 ))) (PreH39 : (((start + L_pre ) - 1 ) <= lo)) (PreH40 : (0 <= lo)) (PreH41 : (lo <= best)) (PreH42 : (best <= hi)) (PreH43 : (hi <= n_pre)) (PreH44 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  TT && emp 
|--
  EX (chosen: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ ((Zlength (slots)) = (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals_2 starts_2 los_2 his_2 bests_2 ) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= k_pre) ” 
  &&  “ (hsize <= (((Zlength (l)) + k_pre ) + 1 )) ” 
  &&  “ (FrontierState ps_2 (Zlength (l)) L_pre R_pre chosen (t + 1 ) total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (((t + 1 ) < k_pre) -> (0 < hsize)) ”
  &&  emp
).

Definition superPiano_return_wit_1 := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) (PreH1 : (t >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2 )) (PreH12 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans )) (PreH14 : ((Zlength (slots_2)) = heap_cap)) (PreH15 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH16 : (0 <= t)) (PreH17 : (t <= k_pre)) (PreH18 : (0 <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH21 : (FrontierState ps_2 n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots_2)) )) (PreH22 : (NodeHeapState slots_2 hsize )) (PreH23 : ((t < k_pre) -> (0 < hsize))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps_2 )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots_2 )
  **  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (st_slots: (@list Z))  (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z)))  (ps: (@list Z)) ,
  “ (PrefixSums l ps ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre total ) ” 
  &&  “ ((Zlength (slots)) = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre ((n_pre + k_pre ) + 1 ) vals )
  **  (IntArray.full heap_start_pre ((n_pre + k_pre ) + 1 ) starts )
  **  (IntArray.full heap_lo_pre ((n_pre + k_pre ) + 1 ) los )
  **  (IntArray.full heap_hi_pre ((n_pre + k_pre ) + 1 ) his )
  **  (IntArray.full heap_best_pre ((n_pre + k_pre ) + 1 ) bests )
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (chosen: (@list Z)) (total: Z) (hsize: Z) (t: Z) (vals_2: (@list Z)) (starts_2: (@list Z)) (los_2: (@list Z)) (his_2: (@list Z)) (bests_2: (@list Z)) (slots_2: (@list ((((Z * Z) * Z) * Z) * Z))) (ans: Z) (st_slots_2: (@list Z)) (ps_2: (@list Z)) (heap_cap: Z) (PreH1 : (t >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps_2 )) (PreH12 : (SparseArgmaxBuilt ps_2 st_slots_2 (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans )) (PreH14 : ((Zlength (slots_2)) = heap_cap)) (PreH15 : (NodeArrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 )) (PreH16 : (0 <= t)) (PreH17 : (t <= k_pre)) (PreH18 : (0 <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH21 : (FrontierState ps_2 n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots_2)) )) (PreH22 : (NodeHeapState slots_2 hsize )) (PreH23 : ((t < k_pre) -> (0 < hsize))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_2 )
  **  (IntArray.full heap_start_pre heap_cap starts_2 )
  **  (IntArray.full heap_lo_pre heap_cap los_2 )
  **  (IntArray.full heap_hi_pre heap_cap his_2 )
  **  (IntArray.full heap_best_pre heap_cap bests_2 )
|--
  EX (vals: (@list Z))  (starts: (@list Z))  (los: (@list Z))  (his: (@list Z))  (bests: (@list Z))  (slots: (@list ((((Z * Z) * Z) * Z) * Z))) ,
  “ (PrefixSums l ps_2 ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre total ) ” 
  &&  “ ((Zlength (slots)) = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ”
  &&  (IntArray.full heap_value_pre ((n_pre + k_pre ) + 1 ) vals )
  **  (IntArray.full heap_start_pre ((n_pre + k_pre ) + 1 ) starts )
  **  (IntArray.full heap_lo_pre ((n_pre + k_pre ) + 1 ) los )
  **  (IntArray.full heap_hi_pre ((n_pre + k_pre ) + 1 ) his )
  **  (IntArray.full heap_best_pre ((n_pre + k_pre ) + 1 ) bests )
).

Definition superPiano_partial_solve_wit_1_pure := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps_2 )) (PreH10 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans )) (PreH12 : ((INT64_MIN) <= ans)) (PreH13 : (ans <= INT64_MAX)) (PreH14 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int  |-> ((n_pre + k_pre ) + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  EX (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < ((Zlength (l)) + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (PrefixSums l ps ) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans: Z) (PreH1 : (R_pre <= INT_MAX)) (PreH2 : (L_pre <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((n_pre + k_pre ) + 1 ) <= INT_MAX)) (PreH6 : (R_pre >= INT_MIN)) (PreH7 : (L_pre >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((n_pre + k_pre ) + 1 ) >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (PrefixSums l ps_2 )) (PreH20 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH21 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans )) (PreH22 : ((INT64_MIN) <= ans)) (PreH23 : (ans <= INT64_MAX)) (PreH24 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  ((( &( "heap_cap" ) )) # Int  |-> ((n_pre + k_pre ) + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  EX (ps: (@list Z)) ,
  “ forall (idx: Z) , (((0 <= idx) /\ (idx < ((Zlength (l)) + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < ((Zlength (l)) + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (PrefixSums l ps ) ”
).

Definition superPiano_partial_solve_wit_1_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps_2: (@list Z)) (ans: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (PrefixSums l ps_2 )) (PreH10 : forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX)))) (PreH11 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans )) (PreH12 : ((INT64_MIN) <= ans)) (PreH13 : (ans <= INT64_MAX)) (PreH14 : forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
|--
  EX (ps: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < ((Zlength (l)) + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps_2 ) ” 
  &&  “ forall (idx_3: Z) , (((0 <= idx_3) /\ (idx_3 < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx_3 ps_2 0)) /\ ((Znth idx_3 ps_2 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((INT64_MIN) <= ans) ” 
  &&  “ (ans <= INT64_MAX) ” 
  &&  “ forall (idx_4: Z) , (((0 <= idx_4) /\ (idx_4 < n_pre)) -> (((-1000) <= (Znth idx_4 l 0)) /\ ((Znth idx_4 l 0) <= 1000))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full prefix_pre (n_pre + 1 ) )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_start_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_lo_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_hi_pre ((n_pre + k_pre ) + 1 ) )
  **  (IntArray.undef_full heap_best_pre ((n_pre + k_pre ) + 1 ) )
.

Definition superPiano_partial_solve_wit_1 := superPiano_partial_solve_wit_1_pure -> superPiano_partial_solve_wit_1_aux.

Definition superPiano_partial_solve_wit_2_pure := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH22 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((Zlength (ps)) = (n_pre + 1 )) ”
).

Definition superPiano_partial_solve_wit_2_pure_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH22 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((Zlength (ps)) = (n_pre + 1 )) ”
.

Definition superPiano_partial_solve_wit_2_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (heap_cap: Z) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS ))) (PreH12 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ ((Zlength (st_slots)) = ((n_pre + 1 ) * ST_LEVELS )) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.undef_full st_pre ((n_pre + 1 ) * ST_LEVELS ) )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
.

Definition superPiano_partial_solve_wit_2 := superPiano_partial_solve_wit_2_pure -> superPiano_partial_solve_wit_2_aux.

Definition superPiano_partial_solve_wit_3_pure := 
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (((n_pre - L_pre ) + 1 ) <= heap_cap) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ”
) \/
(
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH22 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((Zlength (ps)) = (n_pre + 1 )) ”
).

Definition superPiano_partial_solve_wit_3_pure_split_goal_1 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) (PreH1 : (heap_cap <= INT_MAX)) (PreH2 : (R_pre <= INT_MAX)) (PreH3 : (L_pre <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (heap_cap >= INT_MIN)) (PreH7 : (R_pre >= INT_MIN)) (PreH8 : (L_pre >= INT_MIN)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH22 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  ((( &( "hsize" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ ((Zlength (ps)) = (n_pre + 1 )) ”
.

Definition superPiano_partial_solve_wit_3_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (heap_cap: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l ps )) (PreH11 : forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX)))) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (((n_pre - L_pre ) + 1 ) <= heap_cap) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (ps)) = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < (n_pre + 1 ))) -> ((INT_MIN <= (Znth idx ps 0)) /\ ((Znth idx ps 0) <= INT_MAX))) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.undef_full heap_value_pre heap_cap )
  **  (IntArray.undef_full heap_start_pre heap_cap )
  **  (IntArray.undef_full heap_lo_pre heap_cap )
  **  (IntArray.undef_full heap_hi_pre heap_cap )
  **  (IntArray.undef_full heap_best_pre heap_cap )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_3 := superPiano_partial_solve_wit_3_pure -> superPiano_partial_solve_wit_3_aux.

Definition superPiano_partial_solve_wit_4_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (PreH1 : (t < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps )) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : ((Zlength (slots)) = heap_cap)) (PreH15 : (NodeArrays slots vals starts los his bests )) (PreH16 : (0 <= t)) (PreH17 : (t <= k_pre)) (PreH18 : (0 <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH21 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH22 : (NodeHeapState slots hsize )) (PreH23 : ((t < k_pre) -> (0 < hsize))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_4_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (PreH1 : (t < k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= L_pre)) (PreH5 : (L_pre <= R_pre)) (PreH6 : (R_pre <= n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH9 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (PrefixSums l ps )) (PreH12 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH13 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH14 : ((Zlength (slots)) = heap_cap)) (PreH15 : (NodeArrays slots vals starts los his bests )) (PreH16 : (0 <= t)) (PreH17 : (t <= k_pre)) (PreH18 : (0 <= hsize)) (PreH19 : (hsize <= heap_cap)) (PreH20 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH21 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH22 : (NodeHeapState slots hsize )) (PreH23 : ((t < k_pre) -> (0 < hsize))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_4 := superPiano_partial_solve_wit_4_pure -> superPiano_partial_solve_wit_4_aux.

Definition superPiano_partial_solve_wit_5_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (PreH1 : (retval = (heap_top_value (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (t < k_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l ps )) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests )) (PreH19 : (0 <= t)) (PreH20 : (t <= k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize <= heap_cap)) (PreH23 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH25 : (NodeHeapState slots hsize )) (PreH26 : ((t < k_pre) -> (0 < hsize))) (PreH27 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "start" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_5_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (PreH1 : (retval = (heap_top_value (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (t < k_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= L_pre)) (PreH8 : (L_pre <= R_pre)) (PreH9 : (R_pre <= n_pre)) (PreH10 : (1 <= k_pre)) (PreH11 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH12 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (PrefixSums l ps )) (PreH15 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH16 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH17 : ((Zlength (slots)) = heap_cap)) (PreH18 : (NodeArrays slots vals starts los his bests )) (PreH19 : (0 <= t)) (PreH20 : (t <= k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize <= heap_cap)) (PreH23 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH25 : (NodeHeapState slots hsize )) (PreH26 : ((t < k_pre) -> (0 < hsize))) (PreH27 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_5 := superPiano_partial_solve_wit_5_pure -> superPiano_partial_solve_wit_5_aux.

Definition superPiano_partial_solve_wit_6_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (heap_top_start (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval = (heap_top_value (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (t < k_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (1 <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH15 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (PrefixSums l ps )) (PreH18 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH19 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH20 : ((Zlength (slots)) = heap_cap)) (PreH21 : (NodeArrays slots vals starts los his bests )) (PreH22 : (0 <= t)) (PreH23 : (t <= k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize <= heap_cap)) (PreH26 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH28 : (NodeHeapState slots hsize )) (PreH29 : ((t < k_pre) -> (0 < hsize))) (PreH30 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_6_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (heap_top_start (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval = (heap_top_value (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (t < k_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (1 <= L_pre)) (PreH11 : (L_pre <= R_pre)) (PreH12 : (R_pre <= n_pre)) (PreH13 : (1 <= k_pre)) (PreH14 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH15 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (PrefixSums l ps )) (PreH18 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH19 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH20 : ((Zlength (slots)) = heap_cap)) (PreH21 : (NodeArrays slots vals starts los his bests )) (PreH22 : (0 <= t)) (PreH23 : (t <= k_pre)) (PreH24 : (0 <= hsize)) (PreH25 : (hsize <= heap_cap)) (PreH26 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH27 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH28 : (NodeHeapState slots hsize )) (PreH29 : ((t < k_pre) -> (0 < hsize))) (PreH30 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_6 := superPiano_partial_solve_wit_6_pure -> superPiano_partial_solve_wit_6_aux.

Definition superPiano_partial_solve_wit_7_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (heap_top_lo (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval_2 = (heap_top_start (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (retval = (heap_top_value (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests )) (PreH9 : (NodeHeapState slots hsize )) (PreH10 : (t < k_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (slots)) = heap_cap)) (PreH24 : (NodeArrays slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t <= k_pre)) (PreH27 : (0 <= hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH31 : (NodeHeapState slots hsize )) (PreH32 : ((t < k_pre) -> (0 < hsize))) (PreH33 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "lo" ) )) # Int  |-> retval_3)
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_7_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (heap_top_lo (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval_2 = (heap_top_start (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (retval = (heap_top_value (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests )) (PreH9 : (NodeHeapState slots hsize )) (PreH10 : (t < k_pre)) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l ps )) (PreH21 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (slots)) = heap_cap)) (PreH24 : (NodeArrays slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t <= k_pre)) (PreH27 : (0 <= hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH31 : (NodeHeapState slots hsize )) (PreH32 : ((t < k_pre) -> (0 < hsize))) (PreH33 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_7 := superPiano_partial_solve_wit_7_pure -> superPiano_partial_solve_wit_7_aux.

Definition superPiano_partial_solve_wit_8_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (heap_top_hi (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval_3 = (heap_top_lo (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (retval_2 = (heap_top_start (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests )) (PreH9 : (NodeHeapState slots hsize )) (PreH10 : (retval = (heap_top_value (slots)))) (PreH11 : (NodeArrays slots vals starts los his bests )) (PreH12 : (NodeHeapState slots hsize )) (PreH13 : (t < k_pre)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (1 <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= n_pre)) (PreH19 : (1 <= k_pre)) (PreH20 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH21 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (PrefixSums l ps )) (PreH24 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH25 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH26 : ((Zlength (slots)) = heap_cap)) (PreH27 : (NodeArrays slots vals starts los his bests )) (PreH28 : (0 <= t)) (PreH29 : (t <= k_pre)) (PreH30 : (0 <= hsize)) (PreH31 : (hsize <= heap_cap)) (PreH32 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH33 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH34 : (NodeHeapState slots hsize )) (PreH35 : ((t < k_pre) -> (0 < hsize))) (PreH36 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  ((( &( "hi" ) )) # Int  |-> retval_4)
  **  ((( &( "lo" ) )) # Int  |-> retval_3)
  **  ((( &( "start" ) )) # Int  |-> retval_2)
  **  ((( &( "value" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ”
.

Definition superPiano_partial_solve_wit_8_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (total: Z) (hsize: Z) (t: Z) (ans: Z) (st_slots: (@list Z)) (ps: (@list Z)) (heap_cap: Z) (slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (heap_top_hi (slots)))) (PreH2 : (NodeArrays slots vals starts los his bests )) (PreH3 : (NodeHeapState slots hsize )) (PreH4 : (retval_3 = (heap_top_lo (slots)))) (PreH5 : (NodeArrays slots vals starts los his bests )) (PreH6 : (NodeHeapState slots hsize )) (PreH7 : (retval_2 = (heap_top_start (slots)))) (PreH8 : (NodeArrays slots vals starts los his bests )) (PreH9 : (NodeHeapState slots hsize )) (PreH10 : (retval = (heap_top_value (slots)))) (PreH11 : (NodeArrays slots vals starts los his bests )) (PreH12 : (NodeHeapState slots hsize )) (PreH13 : (t < k_pre)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (1 <= L_pre)) (PreH17 : (L_pre <= R_pre)) (PreH18 : (R_pre <= n_pre)) (PreH19 : (1 <= k_pre)) (PreH20 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH21 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (PrefixSums l ps )) (PreH24 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH25 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH26 : ((Zlength (slots)) = heap_cap)) (PreH27 : (NodeArrays slots vals starts los his bests )) (PreH28 : (0 <= t)) (PreH29 : (t <= k_pre)) (PreH30 : (0 <= hsize)) (PreH31 : (hsize <= heap_cap)) (PreH32 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH33 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) )) (PreH34 : (NodeHeapState slots hsize )) (PreH35 : ((t < k_pre) -> (0 < hsize))) (PreH36 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_4 = (heap_top_hi (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_3 = (heap_top_lo (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval_2 = (heap_top_start (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (retval = (heap_top_value (slots))) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (slots)) = heap_cap) ” 
  &&  “ (NodeArrays slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (slots)) ) ” 
  &&  “ (NodeHeapState slots hsize ) ” 
  &&  “ ((t < k_pre) -> (0 < hsize)) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_8 := superPiano_partial_solve_wit_8_pure -> superPiano_partial_solve_wit_8_aux.

Definition superPiano_partial_solve_wit_9_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (value = (heap_top_value (pop_slots)))) (PreH2 : (start = (heap_top_start (pop_slots)))) (PreH3 : (lo = (heap_top_lo (pop_slots)))) (PreH4 : (hi = (heap_top_hi (pop_slots)))) (PreH5 : (best = (heap_top_best (pop_slots)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps )) (PreH16 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (pop_slots)) = heap_cap)) (PreH19 : (NodeArrays pop_slots vals starts los his bests )) (PreH20 : (0 <= t)) (PreH21 : (t < k_pre)) (PreH22 : (0 < hsize)) (PreH23 : (hsize <= heap_cap)) (PreH24 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH25 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH26 : (NodeHeapState pop_slots hsize )) (PreH27 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (((start + L_pre ) - 1 ) <= lo)) (PreH33 : (0 <= lo)) (PreH34 : (lo <= best)) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ”
.

Definition superPiano_partial_solve_wit_9_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ps: (@list Z)) (ans: Z) (st_slots: (@list Z)) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (PreH1 : (value = (heap_top_value (pop_slots)))) (PreH2 : (start = (heap_top_start (pop_slots)))) (PreH3 : (lo = (heap_top_lo (pop_slots)))) (PreH4 : (hi = (heap_top_hi (pop_slots)))) (PreH5 : (best = (heap_top_best (pop_slots)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= L_pre)) (PreH9 : (L_pre <= R_pre)) (PreH10 : (R_pre <= n_pre)) (PreH11 : (1 <= k_pre)) (PreH12 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH13 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (PrefixSums l ps )) (PreH16 : (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) )) (PreH17 : (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans )) (PreH18 : ((Zlength (pop_slots)) = heap_cap)) (PreH19 : (NodeArrays pop_slots vals starts los his bests )) (PreH20 : (0 <= t)) (PreH21 : (t < k_pre)) (PreH22 : (0 < hsize)) (PreH23 : (hsize <= heap_cap)) (PreH24 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH25 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH26 : (NodeHeapState pop_slots hsize )) (PreH27 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best )) (PreH28 : (1 <= start)) (PreH29 : (start <= n_pre)) (PreH30 : (0 <= (start - 1 ))) (PreH31 : ((start - 1 ) < (n_pre + 1 ))) (PreH32 : (((start + L_pre ) - 1 ) <= lo)) (PreH33 : (0 <= lo)) (PreH34 : (lo <= best)) (PreH35 : (best <= hi)) (PreH36 : (hi <= n_pre)) (PreH37 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
|--
  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l ps ) ” 
  &&  “ (SparseArgmaxBuilt ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap vals )
  **  (IntArray.full heap_start_pre heap_cap starts )
  **  (IntArray.full heap_lo_pre heap_cap los )
  **  (IntArray.full heap_hi_pre heap_cap his )
  **  (IntArray.full heap_best_pre heap_cap bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_9 := superPiano_partial_solve_wit_9_pure -> superPiano_partial_solve_wit_9_aux.

Definition superPiano_partial_solve_wit_10_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_10_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : (lo <= (best - 1 ))) (PreH2 : ((Zlength (slots_out)) = heap_cap)) (PreH3 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH4 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH5 : (FrontierPopTop pop_slots hsize slots_out )) (PreH6 : (value = (heap_top_value (pop_slots)))) (PreH7 : (start = (heap_top_start (pop_slots)))) (PreH8 : (lo = (heap_top_lo (pop_slots)))) (PreH9 : (hi = (heap_top_hi (pop_slots)))) (PreH10 : (best = (heap_top_best (pop_slots)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100000)) (PreH13 : (1 <= L_pre)) (PreH14 : (L_pre <= R_pre)) (PreH15 : (R_pre <= n_pre)) (PreH16 : (1 <= k_pre)) (PreH17 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH18 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH19 : ((Zlength (l)) = n_pre)) (PreH20 : (PrefixSums l query_ps )) (PreH21 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH22 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH23 : ((Zlength (pop_slots)) = heap_cap)) (PreH24 : (NodeArrays pop_slots vals starts los his bests )) (PreH25 : (0 <= t)) (PreH26 : (t < k_pre)) (PreH27 : (0 < hsize)) (PreH28 : (hsize <= heap_cap)) (PreH29 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH30 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH31 : (NodeHeapState pop_slots hsize )) (PreH32 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH33 : (1 <= start)) (PreH34 : (start <= n_pre)) (PreH35 : (0 <= (start - 1 ))) (PreH36 : ((start - 1 ) < (n_pre + 1 ))) (PreH37 : (((start + L_pre ) - 1 ) <= lo)) (PreH38 : (0 <= lo)) (PreH39 : (lo <= best)) (PreH40 : (best <= hi)) (PreH41 : (hi <= n_pre)) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_10 := superPiano_partial_solve_wit_10_pure -> superPiano_partial_solve_wit_10_aux.

Definition superPiano_partial_solve_wit_11 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT)))) # Int  |-> (Znth retval query_ps 0))
  **  (IntArray.missing_i prefix_pre retval 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_12 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : (lo <= retval)) (PreH5 : (retval <= (best - 1 ))) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : (lo <= (best - 1 ))) (PreH8 : ((Zlength (slots_out)) = heap_cap)) (PreH9 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH10 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH11 : (FrontierPopTop pop_slots hsize slots_out )) (PreH12 : (value = (heap_top_value (pop_slots)))) (PreH13 : (start = (heap_top_start (pop_slots)))) (PreH14 : (lo = (heap_top_lo (pop_slots)))) (PreH15 : (hi = (heap_top_hi (pop_slots)))) (PreH16 : (best = (heap_top_best (pop_slots)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : (1 <= L_pre)) (PreH20 : (L_pre <= R_pre)) (PreH21 : (R_pre <= n_pre)) (PreH22 : (1 <= k_pre)) (PreH23 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH24 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (PrefixSums l query_ps )) (PreH27 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH28 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH29 : ((Zlength (pop_slots)) = heap_cap)) (PreH30 : (NodeArrays pop_slots vals starts los his bests )) (PreH31 : (0 <= t)) (PreH32 : (t < k_pre)) (PreH33 : (0 < hsize)) (PreH34 : (hsize <= heap_cap)) (PreH35 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH36 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH37 : (NodeHeapState pop_slots hsize )) (PreH38 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH39 : (1 <= start)) (PreH40 : (start <= n_pre)) (PreH41 : (0 <= (start - 1 ))) (PreH42 : ((start - 1 ) < (n_pre + 1 ))) (PreH43 : (((start + L_pre ) - 1 ) <= lo)) (PreH44 : (0 <= lo)) (PreH45 : (lo <= best)) (PreH46 : (best <= hi)) (PreH47 : (hi <= n_pre)) (PreH48 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT)))) # Int  |-> (Znth (start - 1 ) query_ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_13_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> ((Znth retval query_ps 0) - (Znth (start - 1 ) query_ps 0) ))
  **  ((( &( "left_best" ) )) # Int  |-> retval)
  **  ((( &( "has_left" ) )) # Int  |-> 1)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_13_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (n_pre + 1 ))) (PreH5 : (lo <= retval)) (PreH6 : (retval <= (best - 1 ))) (PreH7 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH8 : (lo <= (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax query_ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_13 := superPiano_partial_solve_wit_13_pure -> superPiano_partial_solve_wit_13_aux.

Definition superPiano_partial_solve_wit_14_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "right_value" ) )) # Int  |-> 0)
  **  ((( &( "right_best" ) )) # Int  |-> 0)
  **  ((( &( "has_right" ) )) # Int  |-> 0)
  **  ((( &( "left_value" ) )) # Int  |-> 0)
  **  ((( &( "left_best" ) )) # Int  |-> 0)
  **  ((( &( "has_left" ) )) # Int  |-> 0)
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> (hsize - 1 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + value ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ”
.

Definition superPiano_partial_solve_wit_14_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (PreH1 : ((best + 1 ) <= hi)) (PreH2 : (lo > (best - 1 ))) (PreH3 : ((Zlength (slots_out)) = heap_cap)) (PreH4 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH5 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH6 : (FrontierPopTop pop_slots hsize slots_out )) (PreH7 : (value = (heap_top_value (pop_slots)))) (PreH8 : (start = (heap_top_start (pop_slots)))) (PreH9 : (lo = (heap_top_lo (pop_slots)))) (PreH10 : (hi = (heap_top_hi (pop_slots)))) (PreH11 : (best = (heap_top_best (pop_slots)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= L_pre)) (PreH15 : (L_pre <= R_pre)) (PreH16 : (R_pre <= n_pre)) (PreH17 : (1 <= k_pre)) (PreH18 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH19 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (PrefixSums l query_ps )) (PreH22 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH23 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH24 : ((Zlength (pop_slots)) = heap_cap)) (PreH25 : (NodeArrays pop_slots vals starts los his bests )) (PreH26 : (0 <= t)) (PreH27 : (t < k_pre)) (PreH28 : (0 < hsize)) (PreH29 : (hsize <= heap_cap)) (PreH30 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH31 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH32 : (NodeHeapState pop_slots hsize )) (PreH33 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH34 : (1 <= start)) (PreH35 : (start <= n_pre)) (PreH36 : (0 <= (start - 1 ))) (PreH37 : ((start - 1 ) < (n_pre + 1 ))) (PreH38 : (((start + L_pre ) - 1 ) <= lo)) (PreH39 : (0 <= lo)) (PreH40 : (lo <= best)) (PreH41 : (best <= hi)) (PreH42 : (hi <= n_pre)) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
|--
  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) <= 100001) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi < (n_pre + 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_14 := superPiano_partial_solve_wit_14_pure -> superPiano_partial_solve_wit_14_aux.

Definition superPiano_partial_solve_wit_15 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax query_ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval_2 * sizeof(INT)))) # Int  |-> (Znth retval_2 query_ps 0))
  **  (IntArray.missing_i prefix_pre retval_2 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_16 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval_2 )) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval_2)) (PreH5 : (retval_2 <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (RangeArgmax query_ps lo (best - 1 ) retval )) (PreH9 : (0 <= retval)) (PreH10 : (retval < (n_pre + 1 ))) (PreH11 : (lo <= retval)) (PreH12 : (retval <= (best - 1 ))) (PreH13 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH14 : (lo <= (best - 1 ))) (PreH15 : ((Zlength (slots_out)) = heap_cap)) (PreH16 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH17 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH18 : (FrontierPopTop pop_slots hsize slots_out )) (PreH19 : (value = (heap_top_value (pop_slots)))) (PreH20 : (start = (heap_top_start (pop_slots)))) (PreH21 : (lo = (heap_top_lo (pop_slots)))) (PreH22 : (hi = (heap_top_hi (pop_slots)))) (PreH23 : (best = (heap_top_best (pop_slots)))) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 100000)) (PreH26 : (1 <= L_pre)) (PreH27 : (L_pre <= R_pre)) (PreH28 : (R_pre <= n_pre)) (PreH29 : (1 <= k_pre)) (PreH30 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH31 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH32 : ((Zlength (l)) = n_pre)) (PreH33 : (PrefixSums l query_ps )) (PreH34 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH35 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH36 : ((Zlength (pop_slots)) = heap_cap)) (PreH37 : (NodeArrays pop_slots vals starts los his bests )) (PreH38 : (0 <= t)) (PreH39 : (t < k_pre)) (PreH40 : (0 < hsize)) (PreH41 : (hsize <= heap_cap)) (PreH42 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH43 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH44 : (NodeHeapState pop_slots hsize )) (PreH45 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : (1 <= start)) (PreH47 : (start <= n_pre)) (PreH48 : (0 <= (start - 1 ))) (PreH49 : ((start - 1 ) < (n_pre + 1 ))) (PreH50 : (((start + L_pre ) - 1 ) <= lo)) (PreH51 : (0 <= lo)) (PreH52 : (lo <= best)) (PreH53 : (best <= hi)) (PreH54 : (hi <= n_pre)) (PreH55 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval_2 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval_2) ” 
  &&  “ (retval_2 <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (RangeArgmax query_ps lo (best - 1 ) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ (lo <= retval) ” 
  &&  “ (retval <= (best - 1 )) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT)))) # Int  |-> (Znth (start - 1 ) query_ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_17 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + (retval * sizeof(INT)))) # Int  |-> (Znth retval query_ps 0))
  **  (IntArray.missing_i prefix_pre retval 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_18 := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (vals: (@list Z)) (starts: (@list Z)) (los: (@list Z)) (his: (@list Z)) (bests: (@list Z)) (chosen: (@list Z)) (value: Z) (start: Z) (lo: Z) (hi: Z) (best: Z) (heap_cap: Z) (t: Z) (hsize: Z) (total: Z) (pop_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (vals_out: (@list Z)) (starts_out: (@list Z)) (los_out: (@list Z)) (his_out: (@list Z)) (bests_out: (@list Z)) (slots_out: (@list ((((Z * Z) * Z) * Z) * Z))) (query_ps: (@list Z)) (query_st_slots: (@list Z)) (retval: Z) (PreH1 : (RangeArgmax query_ps (best + 1 ) hi retval )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (n_pre + 1 ))) (PreH4 : ((best + 1 ) <= retval)) (PreH5 : (retval <= hi)) (PreH6 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH7 : ((best + 1 ) <= hi)) (PreH8 : (lo > (best - 1 ))) (PreH9 : ((Zlength (slots_out)) = heap_cap)) (PreH10 : (NodeArrays slots_out vals_out starts_out los_out his_out bests_out )) (PreH11 : (NodeHeapState slots_out (hsize - 1 ) )) (PreH12 : (FrontierPopTop pop_slots hsize slots_out )) (PreH13 : (value = (heap_top_value (pop_slots)))) (PreH14 : (start = (heap_top_start (pop_slots)))) (PreH15 : (lo = (heap_top_lo (pop_slots)))) (PreH16 : (hi = (heap_top_hi (pop_slots)))) (PreH17 : (best = (heap_top_best (pop_slots)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : (1 <= L_pre)) (PreH21 : (L_pre <= R_pre)) (PreH22 : (R_pre <= n_pre)) (PreH23 : (1 <= k_pre)) (PreH24 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH25 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH26 : ((Zlength (l)) = n_pre)) (PreH27 : (PrefixSums l query_ps )) (PreH28 : (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) )) (PreH29 : (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans )) (PreH30 : ((Zlength (pop_slots)) = heap_cap)) (PreH31 : (NodeArrays pop_slots vals starts los his bests )) (PreH32 : (0 <= t)) (PreH33 : (t < k_pre)) (PreH34 : (0 < hsize)) (PreH35 : (hsize <= heap_cap)) (PreH36 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH37 : (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) )) (PreH38 : (NodeHeapState pop_slots hsize )) (PreH39 : (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best )) (PreH40 : (1 <= start)) (PreH41 : (start <= n_pre)) (PreH42 : (0 <= (start - 1 ))) (PreH43 : ((start - 1 ) < (n_pre + 1 ))) (PreH44 : (((start + L_pre ) - 1 ) <= lo)) (PreH45 : (0 <= lo)) (PreH46 : (lo <= best)) (PreH47 : (best <= hi)) (PreH48 : (hi <= n_pre)) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full prefix_pre (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RangeArgmax query_ps (best + 1 ) hi retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= retval) ” 
  &&  “ (retval <= hi) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (lo > (best - 1 )) ” 
  &&  “ ((Zlength (slots_out)) = heap_cap) ” 
  &&  “ (NodeArrays slots_out vals_out starts_out los_out his_out bests_out ) ” 
  &&  “ (NodeHeapState slots_out (hsize - 1 ) ) ” 
  &&  “ (FrontierPopTop pop_slots hsize slots_out ) ” 
  &&  “ (value = (heap_top_value (pop_slots))) ” 
  &&  “ (start = (heap_top_start (pop_slots))) ” 
  &&  “ (lo = (heap_top_lo (pop_slots))) ” 
  &&  “ (hi = (heap_top_hi (pop_slots))) ” 
  &&  “ (best = (heap_top_best (pop_slots))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l query_ps ) ” 
  &&  “ (SparseArgmaxBuilt query_ps query_st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix query_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (pop_slots)) = heap_cap) ” 
  &&  “ (NodeArrays pop_slots vals starts los his bests ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 < hsize) ” 
  &&  “ (hsize <= heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierState query_ps n_pre L_pre R_pre chosen t total (sublist (0) (hsize) (pop_slots)) ) ” 
  &&  “ (NodeHeapState pop_slots hsize ) ” 
  &&  “ (ValidNodeFields query_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (((start + L_pre ) - 1 ) <= lo) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (((prefix_pre + ((start - 1 ) * sizeof(INT)))) # Int  |-> (Znth (start - 1 ) query_ps 0))
  **  (IntArray.missing_i prefix_pre (start - 1 ) 0 (n_pre + 1 ) query_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) query_st_slots )
  **  (IntArray.full heap_value_pre heap_cap vals_out )
  **  (IntArray.full heap_start_pre heap_cap starts_out )
  **  (IntArray.full heap_lo_pre heap_cap los_out )
  **  (IntArray.full heap_hi_pre heap_cap his_out )
  **  (IntArray.full heap_best_pre heap_cap bests_out )
  **  (IntArray.full arr_pre n_pre l )
.

Definition superPiano_partial_solve_wit_19_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ”
.

Definition superPiano_partial_solve_wit_19_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (left_best: Z) (lo: Z) (left_value: Z) (total: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (RangeArgmax push_ps (best + 1 ) hi right_best )) (PreH40 : (0 <= right_best)) (PreH41 : (right_best < (n_pre + 1 ))) (PreH42 : ((best + 1 ) <= right_best)) (PreH43 : (right_best <= hi)) (PreH44 : (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH45 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH46 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (RangeArgmax push_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_19 := superPiano_partial_solve_wit_19_pure -> superPiano_partial_solve_wit_19_aux.

Definition superPiano_partial_solve_wit_20_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 0)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (hi <= best)) (PreH40 : (right_best = 0)) (PreH41 : (right_value = 0)) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ”
.

Definition superPiano_partial_solve_wit_20_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (left_best: Z) (best: Z) (lo: Z) (start: Z) (left_value: Z) (total: Z) (hi: Z) (right_best: Z) (right_value: Z) (value: Z) (push_ps: (@list Z)) (push_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (push_vals: (@list Z)) (push_starts: (@list Z)) (push_los: (@list Z)) (push_his: (@list Z)) (push_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l push_ps )) (PreH11 : (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (push_slots)) = heap_cap)) (PreH14 : (NodeArrays push_slots push_vals push_starts push_los push_his push_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 0)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) )) (PreH23 : (NodeHeapState push_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= (best - 1 ))) (PreH30 : (best <= hi)) (PreH31 : (hi <= n_pre)) (PreH32 : ((best - 1 ) <= n_pre)) (PreH33 : (RangeArgmax push_ps lo (best - 1 ) left_best )) (PreH34 : (0 <= left_best)) (PreH35 : (left_best < (n_pre + 1 ))) (PreH36 : (lo <= left_best)) (PreH37 : (left_best <= (best - 1 ))) (PreH38 : (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH39 : (hi <= best)) (PreH40 : (right_best = 0)) (PreH41 : (right_value = 0)) (PreH42 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best )) (PreH43 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l push_ps ) ” 
  &&  “ (SparseArgmaxBuilt push_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix push_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (push_slots)) = heap_cap) ” 
  &&  “ (NodeArrays push_slots push_vals push_starts push_los push_his push_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState push_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (left_value) (start) (lo) ((best - 1 )) (left_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (push_slots)) ) ” 
  &&  “ (NodeHeapState push_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ (best <= hi) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax push_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (hi <= best) ” 
  &&  “ (right_best = 0) ” 
  &&  “ (right_value = 0) ” 
  &&  “ (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap push_vals )
  **  (IntArray.full heap_start_pre heap_cap push_starts )
  **  (IntArray.full heap_lo_pre heap_cap push_los )
  **  (IntArray.full heap_hi_pre heap_cap push_his )
  **  (IntArray.full heap_best_pre heap_cap push_bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) push_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_20 := superPiano_partial_solve_wit_20_pure -> superPiano_partial_solve_wit_20_aux.

Definition superPiano_partial_solve_wit_21_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH23 : (NodeHeapState right_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (0 <= (best + 1 ))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH34 : (0 <= right_best)) (PreH35 : (right_best < (n_pre + 1 ))) (PreH36 : ((best + 1 ) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH39 : (0 <= lo)) (PreH40 : (lo <= (best - 1 ))) (PreH41 : ((best - 1 ) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH43 : (0 <= left_best)) (PreH44 : (left_best < (n_pre + 1 ))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1 ))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ”
.

Definition superPiano_partial_solve_wit_21_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (left_best: Z) (left_value: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 1)) (PreH16 : (has_right = 1)) (PreH17 : (0 <= t)) (PreH18 : (t < k_pre)) (PreH19 : (0 <= hsize)) (PreH20 : (hsize < heap_cap)) (PreH21 : ((hsize + (k_pre - t ) ) < heap_cap)) (PreH22 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH23 : (NodeHeapState right_slots hsize )) (PreH24 : (1 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= (start - 1 ))) (PreH27 : ((start - 1 ) < (n_pre + 1 ))) (PreH28 : (0 <= lo)) (PreH29 : (lo <= best)) (PreH30 : ((best + 1 ) <= hi)) (PreH31 : (0 <= (best + 1 ))) (PreH32 : (hi <= n_pre)) (PreH33 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH34 : (0 <= right_best)) (PreH35 : (right_best < (n_pre + 1 ))) (PreH36 : ((best + 1 ) <= right_best)) (PreH37 : (right_best <= hi)) (PreH38 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH39 : (0 <= lo)) (PreH40 : (lo <= (best - 1 ))) (PreH41 : ((best - 1 ) <= n_pre)) (PreH42 : (RangeArgmax right_ps lo (best - 1 ) left_best )) (PreH43 : (0 <= left_best)) (PreH44 : (left_best < (n_pre + 1 ))) (PreH45 : (lo <= left_best)) (PreH46 : (left_best <= (best - 1 ))) (PreH47 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best )) (PreH48 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH49 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l right_ps ) ” 
  &&  “ (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (has_left = 1) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((hsize + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax right_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= (best - 1 )) ” 
  &&  “ ((best - 1 ) <= n_pre) ” 
  &&  “ (RangeArgmax right_ps lo (best - 1 ) left_best ) ” 
  &&  “ (0 <= left_best) ” 
  &&  “ (left_best < (n_pre + 1 )) ” 
  &&  “ (lo <= left_best) ” 
  &&  “ (left_best <= (best - 1 )) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1 ) left_best ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_21 := superPiano_partial_solve_wit_21_pure -> superPiano_partial_solve_wit_21_aux.

Definition superPiano_partial_solve_wit_22_pure := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 0)) (PreH16 : (left_best = 0)) (PreH17 : (left_value = 0)) (PreH18 : (has_right = 1)) (PreH19 : (0 <= t)) (PreH20 : (t < k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH25 : (NodeHeapState right_slots hsize )) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : (0 <= (start - 1 ))) (PreH29 : ((start - 1 ) < (n_pre + 1 ))) (PreH30 : (0 <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1 ) <= hi)) (PreH33 : (0 <= (best + 1 ))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH36 : (0 <= right_best)) (PreH37 : (right_best < (n_pre + 1 ))) (PreH38 : ((best + 1 ) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "L" ) )) # Int  |-> L_pre)
  **  ((( &( "R" ) )) # Int  |-> R_pre)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "heap_value" ) )) # Ptr  |-> heap_value_pre)
  **  ((( &( "heap_start" ) )) # Ptr  |-> heap_start_pre)
  **  ((( &( "heap_lo" ) )) # Ptr  |-> heap_lo_pre)
  **  ((( &( "heap_hi" ) )) # Ptr  |-> heap_hi_pre)
  **  ((( &( "heap_best" ) )) # Ptr  |-> heap_best_pre)
  **  ((( &( "heap_cap" ) )) # Int  |-> heap_cap)
  **  ((( &( "has_left" ) )) # Int  |-> has_left)
  **  ((( &( "left_best" ) )) # Int  |-> left_best)
  **  ((( &( "left_value" ) )) # Int  |-> left_value)
  **  ((( &( "has_right" ) )) # Int  |-> has_right)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "hsize" ) )) # Int  |-> hsize)
  **  ((( &( "right_best" ) )) # Int  |-> right_best)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "right_value" ) )) # Int  |-> right_value)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "value" ) )) # Int  |-> value)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ”
.

Definition superPiano_partial_solve_wit_22_aux := 
forall (heap_best_pre: Z) (heap_hi_pre: Z) (heap_lo_pre: Z) (heap_start_pre: Z) (heap_value_pre: Z) (st_pre: Z) (prefix_pre: Z) (R_pre: Z) (L_pre: Z) (k_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (ans: Z) (st_slots: (@list Z)) (chosen: (@list Z)) (heap_cap: Z) (has_left: Z) (left_best: Z) (left_value: Z) (has_right: Z) (t: Z) (hsize: Z) (right_best: Z) (hi: Z) (best: Z) (start: Z) (right_value: Z) (total: Z) (lo: Z) (value: Z) (right_ps: (@list Z)) (right_slots: (@list ((((Z * Z) * Z) * Z) * Z))) (right_vals: (@list Z)) (right_starts: (@list Z)) (right_los: (@list Z)) (right_his: (@list Z)) (right_bests: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= L_pre)) (PreH4 : (L_pre <= R_pre)) (PreH5 : (R_pre <= n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (((n_pre + k_pre ) + 1 ) <= 200000)) (PreH8 : (heap_cap = ((n_pre + k_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (PrefixSums l right_ps )) (PreH11 : (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) )) (PreH12 : (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans )) (PreH13 : ((Zlength (right_slots)) = heap_cap)) (PreH14 : (NodeArrays right_slots right_vals right_starts right_los right_his right_bests )) (PreH15 : (has_left = 0)) (PreH16 : (left_best = 0)) (PreH17 : (left_value = 0)) (PreH18 : (has_right = 1)) (PreH19 : (0 <= t)) (PreH20 : (t < k_pre)) (PreH21 : (0 <= hsize)) (PreH22 : (hsize < heap_cap)) (PreH23 : (((hsize + 1 ) + (k_pre - t ) ) < heap_cap)) (PreH24 : (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) )) (PreH25 : (NodeHeapState right_slots hsize )) (PreH26 : (1 <= start)) (PreH27 : (start <= n_pre)) (PreH28 : (0 <= (start - 1 ))) (PreH29 : ((start - 1 ) < (n_pre + 1 ))) (PreH30 : (0 <= lo)) (PreH31 : (lo <= best)) (PreH32 : ((best + 1 ) <= hi)) (PreH33 : (0 <= (best + 1 ))) (PreH34 : (hi <= n_pre)) (PreH35 : (RangeArgmax right_ps (best + 1 ) hi right_best )) (PreH36 : (0 <= right_best)) (PreH37 : (right_best < (n_pre + 1 ))) (PreH38 : ((best + 1 ) <= right_best)) (PreH39 : (right_best <= hi)) (PreH40 : (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best )) (PreH41 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best )) (PreH42 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
  **  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
|--
  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= L_pre) ” 
  &&  “ (L_pre <= R_pre) ” 
  &&  “ (R_pre <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (((n_pre + k_pre ) + 1 ) <= 200000) ” 
  &&  “ (heap_cap = ((n_pre + k_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (PrefixSums l right_ps ) ” 
  &&  “ (SparseArgmaxBuilt right_ps st_slots (n_pre + 1 ) ) ” 
  &&  “ (SuperPianoAnswerByPrefix right_ps n_pre L_pre R_pre k_pre ans ) ” 
  &&  “ ((Zlength (right_slots)) = heap_cap) ” 
  &&  “ (NodeArrays right_slots right_vals right_starts right_los right_his right_bests ) ” 
  &&  “ (has_left = 0) ” 
  &&  “ (left_best = 0) ” 
  &&  “ (left_value = 0) ” 
  &&  “ (has_right = 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < k_pre) ” 
  &&  “ (0 <= hsize) ” 
  &&  “ (hsize < heap_cap) ” 
  &&  “ (((hsize + 1 ) + (k_pre - t ) ) < heap_cap) ” 
  &&  “ (FrontierSplitState right_ps n_pre L_pre R_pre (cons ((ChordCode (n_pre) (start) (best))) (chosen)) (t + 1 ) total (cons ((mkNode (right_value) (start) ((best + 1 )) (hi) (right_best))) ((@nil ((((Z * Z) * Z) * Z) * Z)))) (sublist (0) (hsize) (right_slots)) ) ” 
  &&  “ (NodeHeapState right_slots hsize ) ” 
  &&  “ (1 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (start - 1 )) ” 
  &&  “ ((start - 1 ) < (n_pre + 1 )) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= best) ” 
  &&  “ ((best + 1 ) <= hi) ” 
  &&  “ (0 <= (best + 1 )) ” 
  &&  “ (hi <= n_pre) ” 
  &&  “ (RangeArgmax right_ps (best + 1 ) hi right_best ) ” 
  &&  “ (0 <= right_best) ” 
  &&  “ (right_best < (n_pre + 1 )) ” 
  &&  “ ((best + 1 ) <= right_best) ” 
  &&  “ (right_best <= hi) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre right_value start (best + 1 ) hi right_best ) ” 
  &&  “ (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-1000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 1000))) ”
  &&  (IntArray.full heap_value_pre heap_cap right_vals )
  **  (IntArray.full heap_start_pre heap_cap right_starts )
  **  (IntArray.full heap_lo_pre heap_cap right_los )
  **  (IntArray.full heap_hi_pre heap_cap right_his )
  **  (IntArray.full heap_best_pre heap_cap right_bests )
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full prefix_pre (n_pre + 1 ) right_ps )
  **  (IntArray.full st_pre ((n_pre + 1 ) * ST_LEVELS ) st_slots )
.

Definition superPiano_partial_solve_wit_22 := superPiano_partial_solve_wit_22_pure -> superPiano_partial_solve_wit_22_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_build_prefix_safety_wit_1 : build_prefix_safety_wit_1.
Axiom proof_of_build_prefix_safety_wit_2 : build_prefix_safety_wit_2.
Axiom proof_of_build_prefix_safety_wit_3 : build_prefix_safety_wit_3.
Axiom proof_of_build_prefix_safety_wit_4 : build_prefix_safety_wit_4.
Axiom proof_of_build_prefix_safety_wit_5 : build_prefix_safety_wit_5.
Axiom proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6.
Axiom proof_of_build_prefix_safety_wit_7 : build_prefix_safety_wit_7.
Axiom proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1.
Axiom proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2.
Axiom proof_of_build_prefix_entail_wit_3 : build_prefix_entail_wit_3.
Axiom proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1.
Axiom proof_of_build_prefix_partial_solve_wit_1 : build_prefix_partial_solve_wit_1.
Axiom proof_of_build_prefix_partial_solve_wit_2 : build_prefix_partial_solve_wit_2.
Axiom proof_of_build_prefix_partial_solve_wit_3 : build_prefix_partial_solve_wit_3.
Axiom proof_of_build_prefix_partial_solve_wit_4 : build_prefix_partial_solve_wit_4.
Axiom proof_of_superPiano_safety_wit_1 : superPiano_safety_wit_1.
Axiom proof_of_superPiano_safety_wit_2 : superPiano_safety_wit_2.
Axiom proof_of_superPiano_safety_wit_3 : superPiano_safety_wit_3.
Axiom proof_of_superPiano_safety_wit_4 : superPiano_safety_wit_4.
Axiom proof_of_superPiano_safety_wit_5 : superPiano_safety_wit_5.
Axiom proof_of_superPiano_safety_wit_6 : superPiano_safety_wit_6.
Axiom proof_of_superPiano_safety_wit_7 : superPiano_safety_wit_7.
Axiom proof_of_superPiano_safety_wit_8 : superPiano_safety_wit_8.
Axiom proof_of_superPiano_safety_wit_9 : superPiano_safety_wit_9.
Axiom proof_of_superPiano_safety_wit_10 : superPiano_safety_wit_10.
Axiom proof_of_superPiano_safety_wit_11 : superPiano_safety_wit_11.
Axiom proof_of_superPiano_safety_wit_12 : superPiano_safety_wit_12.
Axiom proof_of_superPiano_safety_wit_13 : superPiano_safety_wit_13.
Axiom proof_of_superPiano_safety_wit_14 : superPiano_safety_wit_14.
Axiom proof_of_superPiano_safety_wit_15 : superPiano_safety_wit_15.
Axiom proof_of_superPiano_safety_wit_16 : superPiano_safety_wit_16.
Axiom proof_of_superPiano_safety_wit_17 : superPiano_safety_wit_17.
Axiom proof_of_superPiano_safety_wit_18 : superPiano_safety_wit_18.
Axiom proof_of_superPiano_safety_wit_19 : superPiano_safety_wit_19.
Axiom proof_of_superPiano_safety_wit_20 : superPiano_safety_wit_20.
Axiom proof_of_superPiano_safety_wit_21 : superPiano_safety_wit_21.
Axiom proof_of_superPiano_safety_wit_22 : superPiano_safety_wit_22.
Axiom proof_of_superPiano_safety_wit_23 : superPiano_safety_wit_23.
Axiom proof_of_superPiano_safety_wit_24 : superPiano_safety_wit_24.
Axiom proof_of_superPiano_safety_wit_25 : superPiano_safety_wit_25.
Axiom proof_of_superPiano_safety_wit_26 : superPiano_safety_wit_26.
Axiom proof_of_superPiano_safety_wit_27 : superPiano_safety_wit_27.
Axiom proof_of_superPiano_safety_wit_28 : superPiano_safety_wit_28.
Axiom proof_of_superPiano_safety_wit_29 : superPiano_safety_wit_29.
Axiom proof_of_superPiano_safety_wit_30 : superPiano_safety_wit_30.
Axiom proof_of_superPiano_safety_wit_31 : superPiano_safety_wit_31.
Axiom proof_of_superPiano_safety_wit_32 : superPiano_safety_wit_32.
Axiom proof_of_superPiano_safety_wit_33 : superPiano_safety_wit_33.
Axiom proof_of_superPiano_safety_wit_34 : superPiano_safety_wit_34.
Axiom proof_of_superPiano_safety_wit_35 : superPiano_safety_wit_35.
Axiom proof_of_superPiano_safety_wit_36 : superPiano_safety_wit_36.
Axiom proof_of_superPiano_safety_wit_37 : superPiano_safety_wit_37.
Axiom proof_of_superPiano_safety_wit_38 : superPiano_safety_wit_38.
Axiom proof_of_superPiano_safety_wit_39 : superPiano_safety_wit_39.
Axiom proof_of_superPiano_safety_wit_40 : superPiano_safety_wit_40.
Axiom proof_of_superPiano_safety_wit_41 : superPiano_safety_wit_41.
Axiom proof_of_superPiano_safety_wit_42 : superPiano_safety_wit_42.
Axiom proof_of_superPiano_safety_wit_43 : superPiano_safety_wit_43.
Axiom proof_of_superPiano_safety_wit_44 : superPiano_safety_wit_44.
Axiom proof_of_superPiano_safety_wit_45 : superPiano_safety_wit_45.
Axiom proof_of_superPiano_safety_wit_46 : superPiano_safety_wit_46.
Axiom proof_of_superPiano_safety_wit_47 : superPiano_safety_wit_47.
Axiom proof_of_superPiano_safety_wit_48 : superPiano_safety_wit_48.
Axiom proof_of_superPiano_safety_wit_49 : superPiano_safety_wit_49.
Axiom proof_of_superPiano_safety_wit_50 : superPiano_safety_wit_50.
Axiom proof_of_superPiano_safety_wit_51 : superPiano_safety_wit_51.
Axiom proof_of_superPiano_safety_wit_52 : superPiano_safety_wit_52.
Axiom proof_of_superPiano_safety_wit_53 : superPiano_safety_wit_53.
Axiom proof_of_superPiano_safety_wit_54 : superPiano_safety_wit_54.
Axiom proof_of_superPiano_safety_wit_55 : superPiano_safety_wit_55.
Axiom proof_of_superPiano_safety_wit_56 : superPiano_safety_wit_56.
Axiom proof_of_superPiano_safety_wit_57 : superPiano_safety_wit_57.
Axiom proof_of_superPiano_safety_wit_58 : superPiano_safety_wit_58.
Axiom proof_of_superPiano_safety_wit_59 : superPiano_safety_wit_59.
Axiom proof_of_superPiano_safety_wit_60 : superPiano_safety_wit_60.
Axiom proof_of_superPiano_safety_wit_61 : superPiano_safety_wit_61.
Axiom proof_of_superPiano_safety_wit_62 : superPiano_safety_wit_62.
Axiom proof_of_superPiano_safety_wit_63 : superPiano_safety_wit_63.
Axiom proof_of_superPiano_safety_wit_64 : superPiano_safety_wit_64.
Axiom proof_of_superPiano_safety_wit_65 : superPiano_safety_wit_65.
Axiom proof_of_superPiano_safety_wit_66 : superPiano_safety_wit_66.
Axiom proof_of_superPiano_safety_wit_67 : superPiano_safety_wit_67.
Axiom proof_of_superPiano_safety_wit_68 : superPiano_safety_wit_68.
Axiom proof_of_superPiano_safety_wit_69 : superPiano_safety_wit_69.
Axiom proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1.
Axiom proof_of_superPiano_entail_wit_2 : superPiano_entail_wit_2.
Axiom proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3.
Axiom proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4.
Axiom proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5.
Axiom proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6.
Axiom proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7.
Axiom proof_of_superPiano_entail_wit_8 : superPiano_entail_wit_8.
Axiom proof_of_superPiano_entail_wit_9 : superPiano_entail_wit_9.
Axiom proof_of_superPiano_entail_wit_10_1 : superPiano_entail_wit_10_1.
Axiom proof_of_superPiano_entail_wit_10_2 : superPiano_entail_wit_10_2.
Axiom proof_of_superPiano_entail_wit_10_3 : superPiano_entail_wit_10_3.
Axiom proof_of_superPiano_entail_wit_11_1 : superPiano_entail_wit_11_1.
Axiom proof_of_superPiano_entail_wit_11_2 : superPiano_entail_wit_11_2.
Axiom proof_of_superPiano_entail_wit_11_3 : superPiano_entail_wit_11_3.
Axiom proof_of_superPiano_entail_wit_11_4 : superPiano_entail_wit_11_4.
Axiom proof_of_superPiano_entail_wit_12_1 : superPiano_entail_wit_12_1.
Axiom proof_of_superPiano_entail_wit_12_2 : superPiano_entail_wit_12_2.
Axiom proof_of_superPiano_entail_wit_13 : superPiano_entail_wit_13.
Axiom proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14.
Axiom proof_of_superPiano_entail_wit_15_1 : superPiano_entail_wit_15_1.
Axiom proof_of_superPiano_entail_wit_15_2 : superPiano_entail_wit_15_2.
Axiom proof_of_superPiano_entail_wit_15_3 : superPiano_entail_wit_15_3.
Axiom proof_of_superPiano_entail_wit_15_4 : superPiano_entail_wit_15_4.
Axiom proof_of_superPiano_entail_wit_16 : superPiano_entail_wit_16.
Axiom proof_of_superPiano_return_wit_1 : superPiano_return_wit_1.
Axiom proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure.
Axiom proof_of_superPiano_partial_solve_wit_1 : superPiano_partial_solve_wit_1.
Axiom proof_of_superPiano_partial_solve_wit_2_pure : superPiano_partial_solve_wit_2_pure.
Axiom proof_of_superPiano_partial_solve_wit_2 : superPiano_partial_solve_wit_2.
Axiom proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure.
Axiom proof_of_superPiano_partial_solve_wit_3 : superPiano_partial_solve_wit_3.
Axiom proof_of_superPiano_partial_solve_wit_4_pure : superPiano_partial_solve_wit_4_pure.
Axiom proof_of_superPiano_partial_solve_wit_4 : superPiano_partial_solve_wit_4.
Axiom proof_of_superPiano_partial_solve_wit_5_pure : superPiano_partial_solve_wit_5_pure.
Axiom proof_of_superPiano_partial_solve_wit_5 : superPiano_partial_solve_wit_5.
Axiom proof_of_superPiano_partial_solve_wit_6_pure : superPiano_partial_solve_wit_6_pure.
Axiom proof_of_superPiano_partial_solve_wit_6 : superPiano_partial_solve_wit_6.
Axiom proof_of_superPiano_partial_solve_wit_7_pure : superPiano_partial_solve_wit_7_pure.
Axiom proof_of_superPiano_partial_solve_wit_7 : superPiano_partial_solve_wit_7.
Axiom proof_of_superPiano_partial_solve_wit_8_pure : superPiano_partial_solve_wit_8_pure.
Axiom proof_of_superPiano_partial_solve_wit_8 : superPiano_partial_solve_wit_8.
Axiom proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure.
Axiom proof_of_superPiano_partial_solve_wit_9 : superPiano_partial_solve_wit_9.
Axiom proof_of_superPiano_partial_solve_wit_10_pure : superPiano_partial_solve_wit_10_pure.
Axiom proof_of_superPiano_partial_solve_wit_10 : superPiano_partial_solve_wit_10.
Axiom proof_of_superPiano_partial_solve_wit_11 : superPiano_partial_solve_wit_11.
Axiom proof_of_superPiano_partial_solve_wit_12 : superPiano_partial_solve_wit_12.
Axiom proof_of_superPiano_partial_solve_wit_13_pure : superPiano_partial_solve_wit_13_pure.
Axiom proof_of_superPiano_partial_solve_wit_13 : superPiano_partial_solve_wit_13.
Axiom proof_of_superPiano_partial_solve_wit_14_pure : superPiano_partial_solve_wit_14_pure.
Axiom proof_of_superPiano_partial_solve_wit_14 : superPiano_partial_solve_wit_14.
Axiom proof_of_superPiano_partial_solve_wit_15 : superPiano_partial_solve_wit_15.
Axiom proof_of_superPiano_partial_solve_wit_16 : superPiano_partial_solve_wit_16.
Axiom proof_of_superPiano_partial_solve_wit_17 : superPiano_partial_solve_wit_17.
Axiom proof_of_superPiano_partial_solve_wit_18 : superPiano_partial_solve_wit_18.
Axiom proof_of_superPiano_partial_solve_wit_19_pure : superPiano_partial_solve_wit_19_pure.
Axiom proof_of_superPiano_partial_solve_wit_19 : superPiano_partial_solve_wit_19.
Axiom proof_of_superPiano_partial_solve_wit_20_pure : superPiano_partial_solve_wit_20_pure.
Axiom proof_of_superPiano_partial_solve_wit_20 : superPiano_partial_solve_wit_20.
Axiom proof_of_superPiano_partial_solve_wit_21_pure : superPiano_partial_solve_wit_21_pure.
Axiom proof_of_superPiano_partial_solve_wit_21 : superPiano_partial_solve_wit_21.
Axiom proof_of_superPiano_partial_solve_wit_22_pure : superPiano_partial_solve_wit_22_pure.
Axiom proof_of_superPiano_partial_solve_wit_22 : superPiano_partial_solve_wit_22.

End VC_Correct.
