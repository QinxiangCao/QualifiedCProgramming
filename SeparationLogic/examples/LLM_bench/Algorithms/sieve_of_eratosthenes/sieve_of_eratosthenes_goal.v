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
Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (f_pre: Z) (n_pre: Z) (initial: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) initial )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_2 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_3 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((i - 1 )) (1) (current)) )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_4 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_5 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_6 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((1 - 1 )) (0) (current)) )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solve_safety_wit_7 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((1 - 1 )) (0) (current)) )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_8 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (SieveStage n_pre 2 current )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solve_safety_wit_9 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveStage n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_10 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current 0) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition solve_safety_wit_11 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current 0) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solve_safety_wit_12 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current )) ,
  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_13 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((j - 1 )) (0) (current)) )
  **  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + i )) ”
.

Definition solve_safety_wit_14 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (SieveStage n_pre (i + 1 ) current )) ,
  ((( &( "f" ) )) # Ptr  |-> f_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_entail_wit_1 := 
(
forall (f_pre: Z) (n_pre: Z) (initial: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) initial )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (SieveInitPrefix n_pre 1 current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (initial: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  TT && emp 
|--
  “ (SieveInitPrefix n_pre 1 initial ) ”
  &&  emp
).

Definition solve_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (initial: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : ((Zlength (initial)) = n_pre)) ,
  (SieveInitPrefix n_pre 1 initial )
.

Definition solve_entail_wit_2 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((i - 1 )) (1) (current_2)) )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (SieveInitPrefix n_pre (i + 1 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  TT && emp 
|--
  “ (SieveInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 1 )) (1) (current_2)) ) ”
  &&  emp
).

Definition solve_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  (SieveInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 1 )) (1) (current_2)) )
.

Definition solve_entail_wit_3 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((2 - 1 )) (1) ((replace_Znth ((1 - 1 )) (0) (current_2)))) )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (SieveStage n_pre 2 current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  TT && emp 
|--
  “ (SieveStage n_pre 2 (replace_Znth ((2 - 1 )) (1) ((replace_Znth ((1 - 1 )) (0) (current_2)))) ) ”
  &&  emp
).

Definition solve_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current_2 )) ,
  (SieveStage n_pre 2 (replace_Znth ((2 - 1 )) (1) ((replace_Znth ((1 - 1 )) (0) (current_2)))) )
.

Definition solve_entail_wit_4 := 
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (SieveStage n_pre 2 current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (SieveStage n_pre 2 current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
.

Definition solve_entail_wit_5 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((2 * i ) <= (i * 2 )) ” 
  &&  “ ((i * 2 ) <= (n_pre + i )) ” 
  &&  “ (SieveMarkState n_pre i (i * 2 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  TT && emp 
|--
  “ (SieveMarkState n_pre i (i * 2 ) current_2 ) ”
  &&  emp
).

Definition solve_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) = 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  (SieveMarkState n_pre i (i * 2 ) current_2 )
.

Definition solve_entail_wit_6 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((j - 1 )) (0) (current_2)) )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((2 * i ) <= (j + i )) ” 
  &&  “ ((j + i ) <= (n_pre + i )) ” 
  &&  “ (SieveMarkState n_pre i (j + i ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  TT && emp 
|--
  “ (SieveMarkState n_pre i (j + i ) (replace_Znth ((j - 1 )) (0) (current_2)) ) ”
  &&  emp
).

Definition solve_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  (SieveMarkState n_pre i (j + i ) (replace_Znth ((j - 1 )) (0) (current_2)) )
.

Definition solve_entail_wit_7 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SieveStage n_pre (i + 1 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1 ) current_2 ) ”
  &&  emp
).

Definition solve_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current_2 )) ,
  (SieveStage n_pre (i + 1 ) current_2 )
.

Definition solve_entail_wit_8_1 := 
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (SieveStage n_pre (i + 1 ) current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SieveStage n_pre (i + 1 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
.

Definition solve_entail_wit_8_2 := 
(
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) <> 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SieveStage n_pre (i + 1 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
) \/
(
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) <> 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  TT && emp 
|--
  “ (SieveStage n_pre (i + 1 ) current_2 ) ”
  &&  emp
).

Definition solve_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) current_2 0) <> 1)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000000000)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (SieveStage n_pre i current_2 )) ,
  (SieveStage n_pre (i + 1 ) current_2 )
.

Definition solve_entail_wit_9 := 
forall (f_pre: Z) (n_pre: Z) (current_2: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (SieveStage n_pre (i + 1 ) current_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current_2 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (SieveStage n_pre (i + 1 ) current ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
.

Definition solve_entail_wit_10 := 
(
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveStage n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  EX (result: (@list Z)) ,
  “ (PrimeIndicatorList n_pre result ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) result )
) \/
(
forall (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveStage n_pre i current )) ,
  TT && emp 
|--
  “ (PrimeIndicatorList n_pre current ) ”
  &&  emp
).

Definition solve_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveStage n_pre i current )) ,
  (PrimeIndicatorList n_pre current )
.

Definition solve_return_wit_1 := 
forall (f_pre: Z) (n_pre: Z) (result_2: (@list Z)) (PreH1 : (PrimeIndicatorList n_pre result_2 )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) result_2 )
|--
  EX (result: (@list Z)) ,
  “ (PrimeIndicatorList n_pre result ) ”
  &&  (IntArray.seg f_pre 1 (n_pre + 1 ) result )
.

Definition solve_partial_solve_wit_1 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (i <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (SieveInitPrefix n_pre i current ) ”
  &&  (((f_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i f_pre i 1 (n_pre + 1 ) current )
.

Definition solve_partial_solve_wit_2 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (i > n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (SieveInitPrefix n_pre i current ) ”
  &&  (((f_pre + (1 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i f_pre 1 1 (n_pre + 1 ) current )
.

Definition solve_partial_solve_wit_3 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveInitPrefix n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) (replace_Znth ((1 - 1 )) (0) (current)) )
|--
  “ (i > n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (SieveInitPrefix n_pre i current ) ”
  &&  (((f_pre + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i f_pre 2 1 (n_pre + 1 ) (replace_Znth ((1 - 1 )) (0) (current)) )
.

Definition solve_partial_solve_wit_4 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (SieveStage n_pre i current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (i <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (SieveStage n_pre i current ) ”
  &&  (((f_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) current 0))
  **  (IntArray.missing_i f_pre i 1 (n_pre + 1 ) current )
.

Definition solve_partial_solve_wit_5 := 
forall (f_pre: Z) (n_pre: Z) (current: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((2 * i ) <= j)) (PreH7 : (j <= (n_pre + i ))) (PreH8 : (SieveMarkState n_pre i j current )) ,
  (IntArray.seg f_pre 1 (n_pre + 1 ) current )
|--
  “ (j <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((2 * i ) <= j) ” 
  &&  “ (j <= (n_pre + i )) ” 
  &&  “ (SieveMarkState n_pre i j current ) ”
  &&  (((f_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i f_pre j 1 (n_pre + 1 ) current )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Axiom proof_of_solve_entail_wit_8_1 : solve_entail_wit_8_1.
Axiom proof_of_solve_entail_wit_8_2 : solve_entail_wit_8_2.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.

End VC_Correct.
