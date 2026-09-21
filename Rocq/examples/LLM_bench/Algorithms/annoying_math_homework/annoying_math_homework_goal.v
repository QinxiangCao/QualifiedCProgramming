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
Require Import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function digits_sum_init -----*)

Definition digits_sum_init_safety_wit_1 := 
forall (power_pre: Z) (dp_pre: Z) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_full power_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_2 := 
forall (power_pre: Z) (dp_pre: Z) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_full power_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_sum_init_safety_wit_3 := 
forall (power_pre: Z) (dp_pre: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((power_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg power_pre 1 20 )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.undef_full dp_pre 200 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_sum_init_safety_wit_4 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (power_l)) = i)) (PreH4 : (PowerPrefix power_l i )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition digits_sum_init_safety_wit_5 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  ((( &( "bef" ) )) # Int64  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition digits_sum_init_safety_wit_6 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  ((( &( "bef" ) )) # Int64  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_sum_init_safety_wit_7 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) power_l 0) * 10 ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition digits_sum_init_safety_wit_8 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (((Znth ((i - 1 ) - 0 ) power_l 0) * 10 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) power_l 0) * 10 )) ”
) \/
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (((Znth ((i - 1 ) - 0 ) power_l 0) * 10 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) power_l 0) * 10 )) ”
).

Definition digits_sum_init_safety_wit_8_split_goal_1 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (((Znth ((i - 1 ) - 0 ) power_l 0) * 10 ) <= INT64_MAX) ”
.

Definition digits_sum_init_safety_wit_8_split_goal_2 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) power_l 0) * 10 )) ”
.

Definition digits_sum_init_safety_wit_9 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_10 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  ((( &( "bef" ) )) # Int64  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition digits_sum_init_safety_wit_11 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 (i + 1 ) (app (power_l) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))) )
  **  (IntArray.undef_seg power_pre (i + 1 ) 20 )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre 200 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digits_sum_init_safety_wit_12 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_13 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (dp_l)) = (i * 10 ))) (PreH4 : (Forall (eq (0)) dp_l )) (PreH5 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg dp_pre 0 (i * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre (i * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition digits_sum_init_safety_wit_14 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg dp_pre 0 (i * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre (i * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_15 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 20)) (PreH3 : (0 <= j)) (PreH4 : (j <= 10)) (PreH5 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH6 : (Forall (eq (0)) dp_l )) (PreH7 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_16 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition digits_sum_init_safety_wit_17 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition digits_sum_init_safety_wit_18 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_19 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_20 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  (IntArray.seg dp_pre 0 (((i * 10 ) + j ) + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * 10 ) + j ) + 1 ) 200 )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition digits_sum_init_safety_wit_21 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digits_sum_init_safety_wit_22 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.seg dp_pre 0 (i * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre (i * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_23 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (0 <= j)) (PreH2 : (j <= 10)) (PreH3 : ((Zlength (dp_l)) = 200)) (PreH4 : (DigitDPBaseProgress dp_l j )) (PreH5 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_24 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((10 + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (10 + j )) ”
.

Definition digits_sum_init_safety_wit_25 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_26 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j )) (PreH6 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 (replace_Znth ((10 + j )) (j) (dp_l)) )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition digits_sum_init_safety_wit_27 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition digits_sum_init_safety_wit_28 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (dp_l)) = 200)) (PreH4 : (DigitDPOuterProgress dp_l i )) (PreH5 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition digits_sum_init_safety_wit_29 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l i )) (PreH6 : (PowerTable power_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_30 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i < 20)) (PreH3 : (0 <= j)) (PreH4 : (j <= 10)) (PreH5 : ((Zlength (dp_l)) = 200)) (PreH6 : (DigitDPRowProgress dp_l i j )) (PreH7 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_31 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = 200)) (PreH7 : (DigitDPRowProgress dp_l i j )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_sum_init_safety_wit_32 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (2 <= i)) (PreH2 : (i < 20)) (PreH3 : (0 <= j)) (PreH4 : (j < 10)) (PreH5 : (0 <= k)) (PreH6 : (k <= 10)) (PreH7 : ((Zlength (dp_l)) = 200)) (PreH8 : (DigitDPCellProgress dp_l i j k )) (PreH9 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_33 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "sub_power" ) )) # Int64  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition digits_sum_init_safety_wit_34 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "sub_power" ) )) # Int64  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition digits_sum_init_safety_wit_35 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition digits_sum_init_safety_wit_36 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) )) ”
) \/
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) )) ”
).

Definition digits_sum_init_safety_wit_36_split_goal_1 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition digits_sum_init_safety_wit_36_split_goal_2 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((INT64_MIN) <= ((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) )) ”
.

Definition digits_sum_init_safety_wit_37 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((((Znth (i - 2 ) power_l 0) * j ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition digits_sum_init_safety_wit_38 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (i - 2 ) power_l 0) * j ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 2 ) power_l 0) * j )) ”
) \/
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (i - 2 ) power_l 0) * j ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 2 ) power_l 0) * j )) ”
).

Definition digits_sum_init_safety_wit_38_split_goal_1 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth (i - 2 ) power_l 0) * j ) <= INT64_MAX) ”
.

Definition digits_sum_init_safety_wit_38_split_goal_2 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((INT64_MIN) <= ((Znth (i - 2 ) power_l 0) * j )) ”
.

Definition digits_sum_init_safety_wit_39 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((((i - 1 ) * 10 ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * 10 ) + k )) ”
.

Definition digits_sum_init_safety_wit_40 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((i - 1 ) * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * 10 )) ”
.

Definition digits_sum_init_safety_wit_41 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition digits_sum_init_safety_wit_42 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_sum_init_safety_wit_43 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_44 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition digits_sum_init_safety_wit_45 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |->_)
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition digits_sum_init_safety_wit_46 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition digits_sum_init_safety_wit_47 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) )) ”
) \/
(
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) )) ”
).

Definition digits_sum_init_safety_wit_47_split_goal_1 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition digits_sum_init_safety_wit_47_split_goal_2 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((INT64_MIN) <= ((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) )) ”
.

Definition digits_sum_init_safety_wit_48 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "new_dp" ) )) # Int64  |->_)
  **  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition digits_sum_init_safety_wit_49 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "new_dp" ) )) # Int64  |->_)
  **  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition digits_sum_init_safety_wit_50 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "new_dp" ) )) # Int64  |->_)
  **  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_51 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition digits_sum_init_safety_wit_52 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |-> (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition digits_sum_init_safety_wit_53 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |-> (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition digits_sum_init_safety_wit_54 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  ((( &( "new_dp" ) )) # Int64  |-> (((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "moving" ) )) # Int64  |-> (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ))
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "sub_power" ) )) # Int64  |-> (Znth (i - 2 ) power_l 0))
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_sum_init_safety_wit_55 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 (replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l 0) + (((Znth (i - 2 ) power_l 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l)) )
  **  (IntArray.full power_pre 20 power_l )
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition digits_sum_init_safety_wit_56 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition digits_sum_init_safety_wit_57 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = 200)) (PreH7 : (DigitDPRowProgress dp_l i j )) (PreH8 : (PowerTable power_l )) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "power" ) )) # Ptr  |-> power_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition digits_sum_init_entail_wit_1 := 
(
forall (power_pre: Z) (dp_pre: Z) ,
  (((power_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg power_pre 1 20 )
  **  (IntArray.undef_full dp_pre 200 )
|--
  EX (power_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= 20) ” 
  &&  “ ((Zlength (power_l)) = 1) ” 
  &&  “ (PowerPrefix power_l 1 ) ”
  &&  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 1 power_l )
  **  (IntArray.undef_seg power_pre 1 20 )
) \/
(
forall (power_pre: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) ,
  (((power_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (power_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= 20) ” 
  &&  “ ((Zlength (power_l)) = 1) ” 
  &&  “ (PowerPrefix power_l 1 ) ”
  &&  (IntArray.seg power_pre 0 1 power_l )
).

Definition digits_sum_init_entail_wit_2 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  (IntArray.seg power_pre 0 (i + 1 ) (app (power_l_2) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l_2 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))) )
  **  (IntArray.undef_seg power_pre (i + 1 ) 20 )
  **  (IntArray.undef_full dp_pre 200 )
|--
  EX (power_l: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 20) ” 
  &&  “ ((Zlength (power_l)) = (i + 1 )) ” 
  &&  “ (PowerPrefix power_l (i + 1 ) ) ”
  &&  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 (i + 1 ) power_l )
  **  (IntArray.undef_seg power_pre (i + 1 ) 20 )
) \/
(
forall (power_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  TT && emp 
|--
  “ (PowerPrefix (app (power_l_2) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l_2 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ ((Zlength ((app (power_l_2) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l_2 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_2_split_goal_1 := 
forall (power_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  (PowerPrefix (app (power_l_2) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l_2 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))) (i + 1 ) )
.

Definition digits_sum_init_entail_wit_2_split_goal_2 := 
forall (power_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  ((Zlength ((app (power_l_2) ((cons ((signed_last_nbits ((((Znth ((i - 1 ) - 0 ) power_l_2 0) * 10 ) % ( 1000000007 ) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition digits_sum_init_entail_wit_3 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l_2 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 20) ” 
  &&  “ ((Zlength (dp_l)) = (0 * 10 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.seg dp_pre 0 (0 * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (dp_pre: Z) (power_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i )) ,
  (IntArray.undef_full dp_pre 200 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 20) ” 
  &&  “ ((Zlength (dp_l)) = (0 * 10 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l_2 ) ”
  &&  (IntArray.seg dp_pre 0 (0 * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * 10 ) 200 )
).

Definition digits_sum_init_entail_wit_4 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l_2 )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 (i * 10 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((Zlength (dp_l)) = ((i * 10 ) + 0 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.seg dp_pre 0 ((i * 10 ) + 0 ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + 0 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l_2 )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 (i * 10 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((Zlength (dp_l)) = ((i * 10 ) + 0 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l_2 ) ”
  &&  (IntArray.seg dp_pre 0 ((i * 10 ) + 0 ) dp_l )
).

Definition digits_sum_init_entail_wit_5 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l_2 )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 (((i * 10 ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * 10 ) + j ) + 1 ) 200 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 10) ” 
  &&  “ ((Zlength (dp_l)) = ((i * 10 ) + (j + 1 ) )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.seg dp_pre 0 ((i * 10 ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + (j + 1 ) ) 200 )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l_2 )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 (((i * 10 ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 10) ” 
  &&  “ ((Zlength (dp_l)) = ((i * 10 ) + (j + 1 ) )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l_2 ) ”
  &&  (IntArray.seg dp_pre 0 ((i * 10 ) + (j + 1 ) ) dp_l )
).

Definition digits_sum_init_entail_wit_6 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l_2 )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 20) ” 
  &&  “ ((Zlength (dp_l)) = ((i + 1 ) * 10 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.seg dp_pre 0 ((i + 1 ) * 10 ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l_2 )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 20) ” 
  &&  “ ((Zlength (dp_l)) = ((i + 1 ) * 10 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l_2 ) ”
  &&  (IntArray.seg dp_pre 0 ((i + 1 ) * 10 ) dp_l )
).

Definition digits_sum_init_entail_wit_7 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l_2 )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.seg dp_pre 0 (i * 10 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * 10 ) 200 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPBaseProgress dp_l 0 ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l_2 )) (PreH6 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPBaseProgress dp_l_2 0 ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_7_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (0 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10 ))) (PreH5 : (Forall (eq (0)) dp_l_2 )) (PreH6 : (PowerTable power_l_2 )) ,
  (DigitDPBaseProgress dp_l_2 0 )
.

Definition digits_sum_init_entail_wit_8 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 (replace_Znth ((10 + j )) (j) (dp_l_2)) )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPBaseProgress dp_l (j + 1 ) ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPBaseProgress (replace_Znth ((10 + j )) (j) (dp_l_2)) (j + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth ((10 + j )) (j) (dp_l_2)))) = 200) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_8_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  (DigitDPBaseProgress (replace_Znth ((10 + j )) (j) (dp_l_2)) (j + 1 ) )
.

Definition digits_sum_init_entail_wit_8_split_goal_2 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  ((Zlength ((replace_Znth ((10 + j )) (j) (dp_l_2)))) = 200)
.

Definition digits_sum_init_entail_wit_9 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= 2) ” 
  &&  “ (2 <= 20) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPOuterProgress dp_l 2 ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPOuterProgress dp_l_2 2 ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_9_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j >= 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j )) (PreH6 : (PowerTable power_l_2 )) ,
  (DigitDPOuterProgress dp_l_2 2 )
.

Definition digits_sum_init_entail_wit_10 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPRowProgress dp_l i 0 ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPRowProgress dp_l_2 i 0 ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_10_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  (DigitDPRowProgress dp_l_2 i 0 )
.

Definition digits_sum_init_entail_wit_11 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j 0 ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPCellProgress dp_l_2 i j 0 ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_11_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  (DigitDPCellProgress dp_l_2 i j 0 )
.

Definition digits_sum_init_entail_wit_12 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 (replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l_2 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l_2 0) + (((Znth (i - 2 ) power_l_2 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l_2)) )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j (k + 1 ) ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPCellProgress (replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l_2 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l_2 0) + (((Znth (i - 2 ) power_l_2 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l_2)) i j (k + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l_2 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l_2 0) + (((Znth (i - 2 ) power_l_2 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l_2)))) = 200) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_12_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  (DigitDPCellProgress (replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l_2 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l_2 0) + (((Znth (i - 2 ) power_l_2 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l_2)) i j (k + 1 ) )
.

Definition digits_sum_init_entail_wit_12_split_goal_2 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  ((Zlength ((replace_Znth (((i * 10 ) + j )) ((signed_last_nbits ((((Znth ((i * 10 ) + j ) dp_l_2 0) + (((Znth (((i - 1 ) * 10 ) + k ) dp_l_2 0) + (((Znth (i - 2 ) power_l_2 0) * j ) % ( 1000000007 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) (dp_l_2)))) = 200)
.

Definition digits_sum_init_entail_wit_13 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPRowProgress dp_l i (j + 1 ) ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPRowProgress dp_l_2 i (j + 1 ) ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_13_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k )) (PreH10 : (PowerTable power_l_2 )) ,
  (DigitDPRowProgress dp_l_2 i (j + 1 ) )
.

Definition digits_sum_init_entail_wit_14 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 20) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPOuterProgress dp_l (i + 1 ) ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPOuterProgress dp_l_2 (i + 1 ) ) ”
  &&  emp
).

Definition digits_sum_init_entail_wit_14_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j )) (PreH8 : (PowerTable power_l_2 )) ,
  (DigitDPOuterProgress dp_l_2 (i + 1 ) )
.

Definition digits_sum_init_return_wit_1 := 
(
forall (power_pre: Z) (dp_pre: Z) (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  (IntArray.full dp_pre 200 dp_l_2 )
  **  (IntArray.full power_pre 20 power_l_2 )
|--
  EX (power_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (DigitDPTable dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
) \/
(
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  TT && emp 
|--
  “ (DigitDPTable dp_l_2 ) ”
  &&  emp
).

Definition digits_sum_init_return_wit_1_split_goal_1 := 
forall (power_l_2: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i )) (PreH6 : (PowerTable power_l_2 )) ,
  (DigitDPTable dp_l_2 )
.

Definition digits_sum_init_partial_solve_wit_1 := 
forall (power_pre: Z) (dp_pre: Z) ,
  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_full power_pre 20 )
|--
  (((power_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg power_pre 1 20 )
  **  (IntArray.undef_full dp_pre 200 )
.

Definition digits_sum_init_partial_solve_wit_2 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (i < 20) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 20) ” 
  &&  “ ((Zlength (power_l)) = i) ” 
  &&  “ (PowerPrefix power_l i ) ”
  &&  (((power_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((i - 1 ) - 0 ) power_l 0))
  **  (IntArray.missing_i power_pre (i - 1 ) 0 i power_l )
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
.

Definition digits_sum_init_partial_solve_wit_3 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (i: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i )) ,
  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_full dp_pre 200 )
  **  (IntArray.undef_seg power_pre i 20 )
|--
  “ (i < 20) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 20) ” 
  &&  “ ((Zlength (power_l)) = i) ” 
  &&  “ (PowerPrefix power_l i ) ”
  &&  (((power_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg power_pre (i + 1 ) 20 )
  **  (IntArray.seg power_pre 0 i power_l )
  **  (IntArray.undef_full dp_pre 200 )
.

Definition digits_sum_init_partial_solve_wit_4 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10 ) + j ))) (PreH7 : (Forall (eq (0)) dp_l )) (PreH8 : (PowerTable power_l )) ,
  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * 10 ) + j ) 200 )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (j < 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 10) ” 
  &&  “ ((Zlength (dp_l)) = ((i * 10 ) + j )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((dp_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * 10 ) + j ) + 1 ) 200 )
  **  (IntArray.seg dp_pre 0 ((i * 10 ) + j ) dp_l )
  **  (IntArray.full power_pre 20 power_l )
.

Definition digits_sum_init_partial_solve_wit_5 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j < 10)) (PreH2 : (0 <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j )) (PreH6 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (j < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPBaseProgress dp_l j ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((dp_pre + ((10 + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre (10 + j ) 0 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
.

Definition digits_sum_init_partial_solve_wit_6 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (k < 10) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j k ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((power_pre + ((i - 2 ) * sizeof(INT)))) # Int  |-> (Znth (i - 2 ) power_l 0))
  **  (IntArray.missing_i power_pre (i - 2 ) 0 20 power_l )
  **  (IntArray.full dp_pre 200 dp_l )
.

Definition digits_sum_init_partial_solve_wit_7 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full power_pre 20 power_l )
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (k < 10) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j k ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((dp_pre + ((((i - 1 ) * 10 ) + k ) * sizeof(INT)))) # Int  |-> (Znth (((i - 1 ) * 10 ) + k ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((i - 1 ) * 10 ) + k ) 0 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
.

Definition digits_sum_init_partial_solve_wit_8 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (k < 10) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j k ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((dp_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((i * 10 ) + j ) dp_l 0))
  **  (IntArray.missing_i dp_pre ((i * 10 ) + j ) 0 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
.

Definition digits_sum_init_partial_solve_wit_9 := 
forall (power_pre: Z) (dp_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : (0 <= j)) (PreH5 : (j < 10)) (PreH6 : (0 <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k )) (PreH10 : (PowerTable power_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
|--
  “ (k < 10) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 20) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 10) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 10) ” 
  &&  “ ((Zlength (dp_l)) = 200) ” 
  &&  “ (DigitDPCellProgress dp_l i j k ) ” 
  &&  “ (PowerTable power_l ) ”
  &&  (((dp_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre ((i * 10 ) + j ) 0 200 dp_l )
  **  (IntArray.full power_pre 20 power_l )
.

(*----- Function prefix_digits_sum -----*)

Definition prefix_digits_sum_safety_wit_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l )) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_3 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l )) ,
  ((( &( "power_ll" ) )) # Int64  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prefix_digits_sum_safety_wit_4 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l )) ,
  ((( &( "power_ll" ) )) # Int64  |-> 1)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prefix_digits_sum_safety_wit_5 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre < 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  ((( &( "power_ll" ) )) # Int64  |-> 1)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_6 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre >= 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "power_ll" ) )) # Int64  |-> 1)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_7 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (m = 0)) (PreH4 : (ans = 0)) (PreH5 : (power_ll = 1)) (PreH6 : (0 <= i)) (PreH7 : (i <= 20)) (PreH8 : ((Zlength (digits_l)) = i)) (PreH9 : (Forall (eq (0)) digits_l )) (PreH10 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 i digits_l )
  **  (IntArray.undef_seg digits_pre i 20 )
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition prefix_digits_sum_safety_wit_8 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (eq (0)) digits_l )) (PreH11 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 i digits_l )
  **  (IntArray.undef_seg digits_pre i 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_9 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (eq (0)) digits_l )) (PreH11 : (DigitDPTable dp_l )) ,
  (IntArray.seg digits_pre 0 (i + 1 ) (app (digits_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg digits_pre (i + 1 ) 20 )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prefix_digits_sum_safety_wit_10 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((m + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m + 1 )) ”
.

Definition prefix_digits_sum_safety_wit_11 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prefix_digits_sum_safety_wit_12 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((tmpx <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_13 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_14 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (IntArray.full digits_pre 20 (replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l)) )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((tmpx <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_15 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (IntArray.full digits_pre 20 (replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l)) )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> (m + 1 ))
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_16 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prefix_digits_sum_safety_wit_17 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((power_ll * 10 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (power_ll * 10 )) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((power_ll * 10 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (power_ll * 10 )) ”
).

Definition prefix_digits_sum_safety_wit_17_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((power_ll * 10 ) <= INT64_MAX) ”
.

Definition prefix_digits_sum_safety_wit_17_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((INT64_MIN) <= (power_ll * 10 )) ”
.

Definition prefix_digits_sum_safety_wit_18 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_19 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "power_ll" ) )) # Int64  |-> (power_ll * 10 ))
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition prefix_digits_sum_safety_wit_20 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (tmpx = 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= m)) (PreH6 : (m <= 19)) (PreH7 : (0 <= ans)) (PreH8 : (ans < 1000000007)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH13 : (OuterDigitPositionPower i power_ll )) (PreH14 : (DigitDPTable dp_l )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_21 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prefix_digits_sum_safety_wit_22 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ (((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) <> (INT_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_23 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((i * 10 ) + j ) dp_l 0) )) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((i * 10 ) + j ) dp_l 0) )) ”
).

Definition prefix_digits_sum_safety_wit_23_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) <= INT_MAX) ”
.

Definition prefix_digits_sum_safety_wit_23_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ ((INT_MIN) <= (ans + (Znth ((i * 10 ) + j ) dp_l 0) )) ”
.

Definition prefix_digits_sum_safety_wit_24 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((i * 10 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 10 ) + j )) ”
.

Definition prefix_digits_sum_safety_wit_25 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((i * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 10 )) ”
.

Definition prefix_digits_sum_safety_wit_26 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_27 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition prefix_digits_sum_safety_wit_28 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) ))
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition prefix_digits_sum_safety_wit_29 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((x_pre ÷ power_ll ) <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_30 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ” 
  &&  “ (power_ll <> 0) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ” 
  &&  “ (power_ll <> 0) ”
).

Definition prefix_digits_sum_safety_wit_30_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ”
.

Definition prefix_digits_sum_safety_wit_30_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (power_ll <> 0) ”
.

Definition prefix_digits_sum_safety_wit_31 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "current_digit" ) )) # Int64  |->_)
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_32 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((((x_pre % ( power_ll ) ) + 1 ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_33 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((x_pre % ( power_ll ) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((x_pre % ( power_ll ) ) + 1 )) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((x_pre % ( power_ll ) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((x_pre % ( power_ll ) ) + 1 )) ”
).

Definition prefix_digits_sum_safety_wit_33_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((x_pre % ( power_ll ) ) + 1 ) <= INT64_MAX) ”
.

Definition prefix_digits_sum_safety_wit_33_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((INT64_MIN) <= ((x_pre % ( power_ll ) ) + 1 )) ”
.

Definition prefix_digits_sum_safety_wit_34 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ” 
  &&  “ (power_ll <> 0) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ” 
  &&  “ (power_ll <> 0) ”
).

Definition prefix_digits_sum_safety_wit_34_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((x_pre <> (INT64_MIN)) \/ (power_ll <> (-1))) ”
.

Definition prefix_digits_sum_safety_wit_34_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (power_ll <> 0) ”
.

Definition prefix_digits_sum_safety_wit_35 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prefix_digits_sum_safety_wit_36 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "lower_digits" ) )) # Int64  |->_)
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition prefix_digits_sum_safety_wit_37 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_38 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) )) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) )) ”
).

Definition prefix_digits_sum_safety_wit_38_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) <= INT64_MAX) ”
.

Definition prefix_digits_sum_safety_wit_38_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((INT64_MIN) <= ((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) )) ”
.

Definition prefix_digits_sum_safety_wit_39 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "moving" ) )) # Int64  |->_)
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition prefix_digits_sum_safety_wit_40 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) <> (INT64_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_41 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) )) ”
) \/
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) )) ”
).

Definition prefix_digits_sum_safety_wit_41_split_goal_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) <= INT64_MAX) ”
.

Definition prefix_digits_sum_safety_wit_41_split_goal_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((INT64_MIN) <= (ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) )) ”
.

Definition prefix_digits_sum_safety_wit_42 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((( &( "new_ans" ) )) # Int64  |->_)
  **  ((( &( "moving" ) )) # Int64  |-> (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ))
  **  ((( &( "lower_digits" ) )) # Int64  |-> (((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ))
  **  ((( &( "current_digit" ) )) # Int64  |-> ((x_pre ÷ power_ll ) % ( 10 ) ))
  **  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition prefix_digits_sum_safety_wit_43 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)))
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((power_ll <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition prefix_digits_sum_safety_wit_44 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)))
  **  ((( &( "power_ll" ) )) # Int64  |-> power_ll)
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prefix_digits_sum_safety_wit_45 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "digits" ) )) # Ptr  |-> digits_pre)
  **  ((( &( "tmpx" ) )) # Int64  |-> tmpx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "ans" ) )) # Int  |-> (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)))
  **  ((( &( "power_ll" ) )) # Int64  |-> (power_ll ÷ 10 ))
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition prefix_digits_sum_entail_wit_1 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre >= 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 20) ” 
  &&  “ ((Zlength (digits_l)) = 0) ” 
  &&  “ (Forall (eq (0)) digits_l ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 0 digits_l )
  **  (IntArray.undef_seg digits_pre 0 20 )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre >= 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre >= 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  (Forall (eq (0)) (@nil Z) )
.

Definition prefix_digits_sum_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre >= 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition prefix_digits_sum_entail_wit_2 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  (IntArray.seg digits_pre 0 (i + 1 ) (app (digits_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg digits_pre (i + 1 ) 20 )
  **  (IntArray.full dp_pre 200 dp_l )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (m = 0) ” 
  &&  “ (ans = 0) ” 
  &&  “ (power_ll = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 20) ” 
  &&  “ ((Zlength (digits_l)) = (i + 1 )) ” 
  &&  “ (Forall (eq (0)) digits_l ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 (i + 1 ) digits_l )
  **  (IntArray.undef_seg digits_pre (i + 1 ) 20 )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (digits_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (digits_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  (Forall (eq (0)) (app (digits_l_2) ((cons (0) ((@nil Z))))) )
.

Definition prefix_digits_sum_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  ((Zlength ((app (digits_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition prefix_digits_sum_entail_wit_3 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 i digits_l_2 )
  **  (IntArray.undef_seg digits_pre i 20 )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (ans = 0) ” 
  &&  “ (power_ll = 1) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (x_pre >= 0) ” 
  &&  “ ((x_pre <> 0) -> (m < 19)) ” 
  &&  “ ((x_pre = 0) -> (1 <= m)) ” 
  &&  “ ((x_pre = 0) -> (ExtractedDigitCount x_pre m )) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m x_pre ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (ExtractedDigitBuffer x_pre digits_l_2 0 x_pre ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_3_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (eq (0)) digits_l_2 )) (PreH11 : (DigitDPTable dp_l )) ,
  (ExtractedDigitBuffer x_pre digits_l_2 0 x_pre )
.

Definition prefix_digits_sum_entail_wit_4 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (IntArray.full digits_pre 20 (replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l_2)) )
  **  (IntArray.full dp_pre 200 dp_l )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (ans = 0) ” 
  &&  “ (power_ll = 1) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ ((m + 1 ) <= 19) ” 
  &&  “ ((tmpx ÷ 10 ) >= 0) ” 
  &&  “ (((tmpx ÷ 10 ) <> 0) -> ((m + 1 ) < 19)) ” 
  &&  “ (((tmpx ÷ 10 ) = 0) -> (1 <= (m + 1 ))) ” 
  &&  “ (((tmpx ÷ 10 ) = 0) -> (ExtractedDigitCount x_pre (m + 1 ) )) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l (m + 1 ) (tmpx ÷ 10 ) ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  TT && emp 
|--
  “ (ExtractedDigitBuffer x_pre (replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l_2)) (m + 1 ) (tmpx ÷ 10 ) ) ” 
  &&  “ ((Zlength ((replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l_2)))) = 20) ” 
  &&  “ (((tmpx ÷ 10 ) = 0) -> (ExtractedDigitCount x_pre (m + 1 ) )) ” 
  &&  “ (((tmpx ÷ 10 ) <> 0) -> ((m + 1 ) < 19)) ” 
  &&  “ ((tmpx ÷ 10 ) >= 0) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_4_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (ExtractedDigitBuffer x_pre (replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l_2)) (m + 1 ) (tmpx ÷ 10 ) )
.

Definition prefix_digits_sum_entail_wit_4_split_goal_2 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((Zlength ((replace_Znth ((m + 1 )) ((signed_last_nbits ((tmpx % ( 10 ) )) (32))) (digits_l_2)))) = 20)
.

Definition prefix_digits_sum_entail_wit_4_split_goal_3 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (((tmpx ÷ 10 ) = 0) -> (ExtractedDigitCount x_pre (m + 1 ) ))
.

Definition prefix_digits_sum_entail_wit_4_split_goal_4 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (((tmpx ÷ 10 ) <> 0) -> ((m + 1 ) < 19))
.

Definition prefix_digits_sum_entail_wit_4_split_goal_5 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  ((tmpx ÷ 10 ) >= 0)
.

Definition prefix_digits_sum_entail_wit_5 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx = 0)) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l_2 )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (ans = 0) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (DigitPositionPower 1 power_ll ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre m ans ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx = 0)) ,
  TT && emp 
|--
  “ (AccumulatedDigitSumCorrect x_pre m 0 ) ” 
  &&  “ (DigitPositionPower 1 1 ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx = 0)) ,
  (AccumulatedDigitSumCorrect x_pre m 0 )
.

Definition prefix_digits_sum_entail_wit_5_split_goal_2 := 
forall (x_pre: Z) (dp_l: (@list Z)) (digits_l_2: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx = 0)) ,
  (DigitPositionPower 1 1 )
.

Definition prefix_digits_sum_entail_wit_6 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l_2 )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (ans = 0) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (DigitPositionPower (i + 1 ) (power_ll * 10 ) ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre m ans ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (DigitPositionPower (i + 1 ) (power_ll * 10 ) ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_6_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  (DigitPositionPower (i + 1 ) (power_ll * 10 ) )
.

Definition prefix_digits_sum_entail_wit_7 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l_2 )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre m ans ) ” 
  &&  “ (OuterDigitPositionPower m power_ll ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (OuterDigitPositionPower m power_ll ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_7_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (ans: Z) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = 0)) (PreH5 : (tmpx = 0)) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH11 : (ExtractedDigitCount x_pre m )) (PreH12 : (DigitPositionPower i power_ll )) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans )) (PreH14 : (DigitDPTable dp_l )) ,
  (OuterDigitPositionPower m power_ll )
.

Definition prefix_digits_sum_entail_wit_8 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l_2)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l_2 )
|--
  EX (answer_before: Z)  (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= (Znth i digits_l 0)) ” 
  &&  “ ((Znth i digits_l 0) < 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth i digits_l 0)) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i 0 answer_before ans ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ” 
  &&  “ (OuterDigitPositionPower i power_ll ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l_2: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i > 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l_2)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  EX (answer_before: Z) ,
  “ (1 <= i) ” 
  &&  “ (0 <= (Znth i digits_l_2 0)) ” 
  &&  “ ((Znth i digits_l_2 0) < 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth i digits_l_2 0)) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i 0 answer_before ans ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_9 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before_2: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before_2 ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before_2 )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l_2 )
|--
  EX (answer_before: Z)  (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= (Znth i digits_l 0)) ” 
  &&  “ ((Znth i digits_l 0) < 10) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Znth i digits_l 0)) ” 
  &&  “ (0 <= ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) )) ” 
  &&  “ (((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) ) < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i (j + 1 ) answer_before ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) ) ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ” 
  &&  “ (OuterDigitPositionPower i power_ll ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before_2: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before_2 ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before_2 )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  EX (answer_before: Z) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Znth i digits_l_2 0)) ” 
  &&  “ (0 <= ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) )) ” 
  &&  “ (((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) ) < 1000000007) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i (j + 1 ) answer_before ((ans + (Znth ((i * 10 ) + j ) dp_l 0) ) % ( 1000000007 ) ) ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_10 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l_2 )
  **  (IntArray.full dp_pre 200 dp_l )
|--
  EX (digits_l: (@list Z)) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre (i - 1 ) (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) ) ” 
  &&  “ (OuterDigitPositionPower (i - 1 ) (power_ll ÷ 10 ) ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (OuterDigitPositionPower (i - 1 ) (power_ll ÷ 10 ) ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre (i - 1 ) (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) ) ” 
  &&  “ ((signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) < 1000000007) ” 
  &&  “ (0 <= (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32))) ”
  &&  emp
).

Definition prefix_digits_sum_entail_wit_10_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (OuterDigitPositionPower (i - 1 ) (power_ll ÷ 10 ) )
.

Definition prefix_digits_sum_entail_wit_10_split_goal_2 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (AccumulatedDigitSumCorrect x_pre (i - 1 ) (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) )
.

Definition prefix_digits_sum_entail_wit_10_split_goal_3 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  ((signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)) < 1000000007)
.

Definition prefix_digits_sum_entail_wit_10_split_goal_4 := 
forall (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l_2: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j >= (Znth i digits_l_2 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l_2 0))) (PreH9 : ((Znth i digits_l_2 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l_2 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (0 <= (signed_last_nbits (((ans + (((((x_pre % ( power_ll ) ) + 1 ) % ( 1000000007 ) ) * ((x_pre ÷ power_ll ) % ( 10 ) ) ) % ( 1000000007 ) ) ) % ( 1000000007 ) )) (32)))
.

Definition prefix_digits_sum_return_wit_1 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i <= 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (PrefixDigitSum x_pre ans ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
) \/
(
forall (digits_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i <= 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
|--
  “ (PrefixDigitSum x_pre ans ) ”
  &&  (IntArray.undef_full digits_pre 20 )
).

Definition prefix_digits_sum_return_wit_1_split_goal_1 := 
forall (digits_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i <= 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
|--
  “ (PrefixDigitSum x_pre ans ) ”
.

Definition prefix_digits_sum_return_wit_1_split_goal_spatial := 
forall (digits_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (digits_l: (@list Z)) (ans: Z) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (i <= 0)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH12 : (ExtractedDigitCount x_pre m )) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans )) (PreH14 : (OuterDigitPositionPower i power_ll )) (PreH15 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
|--
  (IntArray.undef_full digits_pre 20 )
.

Definition prefix_digits_sum_return_wit_2 := 
(
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre < 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
|--
  “ (PrefixDigitSum x_pre 0 ) ”
  &&  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.undef_full digits_pre 20 )
) \/
(
forall (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre < 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  TT && emp 
|--
  “ (PrefixDigitSum x_pre 0 ) ”
  &&  emp
).

Definition prefix_digits_sum_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (dp_l: (@list Z)) (PreH1 : (x_pre < 1)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l )) ,
  (PrefixDigitSum x_pre 0 )
.

Definition prefix_digits_sum_partial_solve_wit_1 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (i: Z) (power_ll: Z) (ans: Z) (m: Z) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = 0)) (PreH5 : (ans = 0)) (PreH6 : (power_ll = 1)) (PreH7 : (0 <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (eq (0)) digits_l )) (PreH11 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 i digits_l )
  **  (IntArray.undef_seg digits_pre i 20 )
|--
  “ (i < 20) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (m = 0) ” 
  &&  “ (ans = 0) ” 
  &&  “ (power_ll = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 20) ” 
  &&  “ ((Zlength (digits_l)) = i) ” 
  &&  “ (Forall (eq (0)) digits_l ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (((digits_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg digits_pre (i + 1 ) 20 )
  **  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.seg digits_pre 0 i digits_l )
.

Definition prefix_digits_sum_partial_solve_wit_2 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (digits_l: (@list Z)) (tmpx: Z) (m: Z) (power_ll: Z) (ans: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = 0)) (PreH4 : (power_ll = 1)) (PreH5 : (0 <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= 0)) (PreH8 : ((tmpx <> 0) -> (m < 19))) (PreH9 : ((tmpx = 0) -> (1 <= m))) (PreH10 : ((tmpx = 0) -> (ExtractedDigitCount x_pre m ))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx )) (PreH13 : (DigitDPTable dp_l )) (PreH14 : (tmpx <> 0)) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (ans = 0) ” 
  &&  “ (power_ll = 1) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (tmpx >= 0) ” 
  &&  “ ((tmpx <> 0) -> (m < 19)) ” 
  &&  “ ((tmpx = 0) -> (1 <= m)) ” 
  &&  “ ((tmpx = 0) -> (ExtractedDigitCount x_pre m )) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m tmpx ) ” 
  &&  “ (DigitDPTable dp_l ) ” 
  &&  “ (tmpx <> 0) ”
  &&  (((digits_pre + ((m + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i digits_pre (m + 1 ) 0 20 digits_l )
  **  (IntArray.full dp_pre 200 dp_l )
.

Definition prefix_digits_sum_partial_solve_wit_3 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (tmpx = 0)) (PreH4 : (1 <= i)) (PreH5 : (i <= m)) (PreH6 : (m <= 19)) (PreH7 : (0 <= (Znth i digits_l 0))) (PreH8 : ((Znth i digits_l 0) < 10)) (PreH9 : (0 <= j)) (PreH10 : (j <= (Znth i digits_l 0))) (PreH11 : (0 <= ans)) (PreH12 : (ans < 1000000007)) (PreH13 : ((Zlength (digits_l)) = 20)) (PreH14 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH15 : (ExtractedDigitCount x_pre m )) (PreH16 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH18 : (OuterDigitPositionPower i power_ll )) (PreH19 : (DigitDPTable dp_l )) ,
  (IntArray.full dp_pre 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= (Znth i digits_l 0)) ” 
  &&  “ ((Znth i digits_l 0) < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Znth i digits_l 0)) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i j answer_before ans ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ” 
  &&  “ (OuterDigitPositionPower i power_ll ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (((digits_pre + (i * sizeof(INT)))) # Int  |-> (Znth i digits_l 0))
  **  (IntArray.missing_i digits_pre i 0 20 digits_l )
  **  (IntArray.full dp_pre 200 dp_l )
.

Definition prefix_digits_sum_partial_solve_wit_4 := 
forall (digits_pre: Z) (dp_pre: Z) (x_pre: Z) (dp_l: (@list Z)) (power_ll: Z) (answer_before: Z) (ans: Z) (j: Z) (digits_l: (@list Z)) (m: Z) (i: Z) (tmpx: Z) (PreH1 : (j < (Znth i digits_l 0))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = 0)) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : (0 <= (Znth i digits_l 0))) (PreH9 : ((Znth i digits_l 0) < 10)) (PreH10 : (0 <= j)) (PreH11 : (j <= (Znth i digits_l 0))) (PreH12 : (0 <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m 0 )) (PreH16 : (ExtractedDigitCount x_pre m )) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans )) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before )) (PreH19 : (OuterDigitPositionPower i power_ll )) (PreH20 : (DigitDPTable dp_l )) ,
  (IntArray.full digits_pre 20 digits_l )
  **  (IntArray.full dp_pre 200 dp_l )
|--
  “ (j < (Znth i digits_l 0)) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000000000000) ” 
  &&  “ (tmpx = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m) ” 
  &&  “ (m <= 19) ” 
  &&  “ (0 <= (Znth i digits_l 0)) ” 
  &&  “ ((Znth i digits_l 0) < 10) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Znth i digits_l 0)) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans < 1000000007) ” 
  &&  “ ((Zlength (digits_l)) = 20) ” 
  &&  “ (ExtractedDigitBuffer x_pre digits_l m 0 ) ” 
  &&  “ (ExtractedDigitCount x_pre m ) ” 
  &&  “ (InnerCandidateDigitProgress dp_l i j answer_before ans ) ” 
  &&  “ (AccumulatedDigitSumCorrect x_pre i answer_before ) ” 
  &&  “ (OuterDigitPositionPower i power_ll ) ” 
  &&  “ (DigitDPTable dp_l ) ”
  &&  (((dp_pre + (((i * 10 ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((i * 10 ) + j ) dp_l 0))
  **  (IntArray.missing_i dp_pre ((i * 10 ) + j ) 0 200 dp_l )
  **  (IntArray.full digits_pre 20 digits_l )
.

(*----- Function interval_digits_sum -----*)

Definition interval_digits_sum_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (DigitDPTable dp_l )) (PreH2 : (PowerTable power_l )) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (DigitDPTable dp_l )) (PreH2 : (PowerTable power_l )) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  ((( &( "ans1" ) )) # Int  |-> retval)
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((x_pre - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x_pre - 1 )) ”
.

Definition interval_digits_sum_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  ((( &( "ans1" ) )) # Int  |-> retval)
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition interval_digits_sum_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  ((( &( "ans1" ) )) # Int  |-> retval)
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  ((( &( "ans1" ) )) # Int  |-> retval)
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition interval_digits_sum_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ (((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) <> (INT_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition interval_digits_sum_safety_wit_10 := 
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 )) ”
).

Definition interval_digits_sum_safety_wit_10_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) <= INT_MAX) ”
.

Definition interval_digits_sum_safety_wit_10_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((INT_MIN) <= (((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 )) ”
.

Definition interval_digits_sum_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ (((ans1 - ans2 ) <> (INT_MIN)) \/ (1000000007 <> (-1))) ” 
  &&  “ (1000000007 <> 0) ”
.

Definition interval_digits_sum_safety_wit_12 := 
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((ans1 - ans2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans1 - ans2 )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((ans1 - ans2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans1 - ans2 )) ”
).

Definition interval_digits_sum_safety_wit_12_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((ans1 - ans2 ) <= INT_MAX) ”
.

Definition interval_digits_sum_safety_wit_12_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ ((INT_MIN) <= (ans1 - ans2 )) ”
.

Definition interval_digits_sum_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition interval_digits_sum_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition interval_digits_sum_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  ((( &( "ans1" ) )) # Int  |-> ans1)
  **  ((( &( "ans2" ) )) # Int  |-> ans2)
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
|--
  “ (1000000007 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000000007) ”
.

Definition interval_digits_sum_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (IntArray.undef_full ( &( "digits" ) ) 20 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ”
  &&  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
) \/
(
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (IntArray.undef_full ( &( "digits" ) ) 20 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
|--
  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
).

Definition interval_digits_sum_entail_wit_1_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (IntArray.undef_full ( &( "digits" ) ) 20 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "dp" ) ) 200 )
|--
  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
.

Definition interval_digits_sum_entail_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (PrefixDigitSum (x_pre - 1 ) retval_2 )) (PreH2 : (PrefixDigitSum y_pre retval )) (PreH3 : (DigitDPTable dp_l )) (PreH4 : (PowerTable power_l )) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ” 
  &&  “ (PrefixDigitSum y_pre retval ) ” 
  &&  “ (PrefixDigitSum (x_pre - 1 ) retval_2 ) ”
  &&  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
) \/
(
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (PrefixDigitSum (x_pre - 1 ) retval_2 )) (PreH2 : (PrefixDigitSum y_pre retval )) (PreH3 : (DigitDPTable dp_l )) (PreH4 : (PowerTable power_l )) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
|--
  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
).

Definition interval_digits_sum_entail_wit_2_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (PrefixDigitSum (x_pre - 1 ) retval_2 )) (PreH2 : (PrefixDigitSum y_pre retval )) (PreH3 : (DigitDPTable dp_l )) (PreH4 : (PowerTable power_l )) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
|--
  (IntArray.undef_full ( &( "dp" ) ) 200 )
  **  (IntArray.undef_full ( &( "power" ) ) 20 )
  **  (IntArray.undef_full ( &( "digits" ) ) 20 )
.

Definition interval_digits_sum_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  TT && emp 
|--
  “ (IntervalDigitSum x_pre y_pre ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) % ( 1000000007 ) ) ) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  TT && emp 
|--
  “ (IntervalDigitSum x_pre y_pre ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) % ( 1000000007 ) ) ) ”
  &&  emp
).

Definition interval_digits_sum_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (ans1: Z) (ans2: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1 )) (PreH5 : (PrefixDigitSum (x_pre - 1 ) ans2 )) ,
  (IntervalDigitSum x_pre y_pre ((((ans1 - ans2 ) % ( 1000000007 ) ) + 1000000007 ) % ( 1000000007 ) ) )
.

Definition interval_digits_sum_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ”
  &&  (IntArray.undef_full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 )
  **  (IntArray.undef_full (( &( "power" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
.

Definition interval_digits_sum_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (DigitDPTable dp_l )) (PreH2 : (PowerTable power_l )) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ” 
  &&  “ (DigitDPTable dp_l ) ”
.

Definition interval_digits_sum_partial_solve_wit_2_aux := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (DigitDPTable dp_l )) (PreH2 : (PowerTable power_l )) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
|--
  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ” 
  &&  “ (DigitDPTable dp_l ) ” 
  &&  “ (DigitDPTable dp_l ) ” 
  &&  “ (PowerTable power_l ) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ”
  &&  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
.

Definition interval_digits_sum_partial_solve_wit_2 := interval_digits_sum_partial_solve_wit_2_pure -> interval_digits_sum_partial_solve_wit_2_aux.

Definition interval_digits_sum_partial_solve_wit_3_pure := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int  |->_)
  **  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  ((( &( "ans1" ) )) # Int  |-> retval)
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= (x_pre - 1 )) ” 
  &&  “ ((x_pre - 1 ) <= 1000000000000000000) ” 
  &&  “ (DigitDPTable dp_l ) ”
.

Definition interval_digits_sum_partial_solve_wit_3_aux := 
forall (y_pre: Z) (x_pre: Z) (power_l: (@list Z)) (dp_l: (@list Z)) (retval: Z) (PreH1 : (PrefixDigitSum y_pre retval )) (PreH2 : (DigitDPTable dp_l )) (PreH3 : (PowerTable power_l )) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
|--
  “ (0 <= (x_pre - 1 )) ” 
  &&  “ ((x_pre - 1 ) <= 1000000000000000000) ” 
  &&  “ (DigitDPTable dp_l ) ” 
  &&  “ (PrefixDigitSum y_pre retval ) ” 
  &&  “ (DigitDPTable dp_l ) ” 
  &&  “ (PowerTable power_l ) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= y_pre) ” 
  &&  “ (y_pre <= 1000000000000000000) ”
  &&  (IntArray.full (( &( "dp" ) ) + (0 * sizeof(INT))) 200 dp_l )
  **  (IntArray.undef_full (( &( "digits" ) ) + (0 * sizeof(INT))) 20 )
  **  (IntArray.full (( &( "power" ) ) + (0 * sizeof(INT))) 20 power_l )
.

Definition interval_digits_sum_partial_solve_wit_3 := interval_digits_sum_partial_solve_wit_3_pure -> interval_digits_sum_partial_solve_wit_3_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_digits_sum_init_safety_wit_1 : digits_sum_init_safety_wit_1.
Axiom proof_of_digits_sum_init_safety_wit_2 : digits_sum_init_safety_wit_2.
Axiom proof_of_digits_sum_init_safety_wit_3 : digits_sum_init_safety_wit_3.
Axiom proof_of_digits_sum_init_safety_wit_4 : digits_sum_init_safety_wit_4.
Axiom proof_of_digits_sum_init_safety_wit_5 : digits_sum_init_safety_wit_5.
Axiom proof_of_digits_sum_init_safety_wit_6 : digits_sum_init_safety_wit_6.
Axiom proof_of_digits_sum_init_safety_wit_7 : digits_sum_init_safety_wit_7.
Axiom proof_of_digits_sum_init_safety_wit_8 : digits_sum_init_safety_wit_8.
Axiom proof_of_digits_sum_init_safety_wit_9 : digits_sum_init_safety_wit_9.
Axiom proof_of_digits_sum_init_safety_wit_10 : digits_sum_init_safety_wit_10.
Axiom proof_of_digits_sum_init_safety_wit_11 : digits_sum_init_safety_wit_11.
Axiom proof_of_digits_sum_init_safety_wit_12 : digits_sum_init_safety_wit_12.
Axiom proof_of_digits_sum_init_safety_wit_13 : digits_sum_init_safety_wit_13.
Axiom proof_of_digits_sum_init_safety_wit_14 : digits_sum_init_safety_wit_14.
Axiom proof_of_digits_sum_init_safety_wit_15 : digits_sum_init_safety_wit_15.
Axiom proof_of_digits_sum_init_safety_wit_16 : digits_sum_init_safety_wit_16.
Axiom proof_of_digits_sum_init_safety_wit_17 : digits_sum_init_safety_wit_17.
Axiom proof_of_digits_sum_init_safety_wit_18 : digits_sum_init_safety_wit_18.
Axiom proof_of_digits_sum_init_safety_wit_19 : digits_sum_init_safety_wit_19.
Axiom proof_of_digits_sum_init_safety_wit_20 : digits_sum_init_safety_wit_20.
Axiom proof_of_digits_sum_init_safety_wit_21 : digits_sum_init_safety_wit_21.
Axiom proof_of_digits_sum_init_safety_wit_22 : digits_sum_init_safety_wit_22.
Axiom proof_of_digits_sum_init_safety_wit_23 : digits_sum_init_safety_wit_23.
Axiom proof_of_digits_sum_init_safety_wit_24 : digits_sum_init_safety_wit_24.
Axiom proof_of_digits_sum_init_safety_wit_25 : digits_sum_init_safety_wit_25.
Axiom proof_of_digits_sum_init_safety_wit_26 : digits_sum_init_safety_wit_26.
Axiom proof_of_digits_sum_init_safety_wit_27 : digits_sum_init_safety_wit_27.
Axiom proof_of_digits_sum_init_safety_wit_28 : digits_sum_init_safety_wit_28.
Axiom proof_of_digits_sum_init_safety_wit_29 : digits_sum_init_safety_wit_29.
Axiom proof_of_digits_sum_init_safety_wit_30 : digits_sum_init_safety_wit_30.
Axiom proof_of_digits_sum_init_safety_wit_31 : digits_sum_init_safety_wit_31.
Axiom proof_of_digits_sum_init_safety_wit_32 : digits_sum_init_safety_wit_32.
Axiom proof_of_digits_sum_init_safety_wit_33 : digits_sum_init_safety_wit_33.
Axiom proof_of_digits_sum_init_safety_wit_34 : digits_sum_init_safety_wit_34.
Axiom proof_of_digits_sum_init_safety_wit_35 : digits_sum_init_safety_wit_35.
Axiom proof_of_digits_sum_init_safety_wit_36 : digits_sum_init_safety_wit_36.
Axiom proof_of_digits_sum_init_safety_wit_37 : digits_sum_init_safety_wit_37.
Axiom proof_of_digits_sum_init_safety_wit_38 : digits_sum_init_safety_wit_38.
Axiom proof_of_digits_sum_init_safety_wit_39 : digits_sum_init_safety_wit_39.
Axiom proof_of_digits_sum_init_safety_wit_40 : digits_sum_init_safety_wit_40.
Axiom proof_of_digits_sum_init_safety_wit_41 : digits_sum_init_safety_wit_41.
Axiom proof_of_digits_sum_init_safety_wit_42 : digits_sum_init_safety_wit_42.
Axiom proof_of_digits_sum_init_safety_wit_43 : digits_sum_init_safety_wit_43.
Axiom proof_of_digits_sum_init_safety_wit_44 : digits_sum_init_safety_wit_44.
Axiom proof_of_digits_sum_init_safety_wit_45 : digits_sum_init_safety_wit_45.
Axiom proof_of_digits_sum_init_safety_wit_46 : digits_sum_init_safety_wit_46.
Axiom proof_of_digits_sum_init_safety_wit_47 : digits_sum_init_safety_wit_47.
Axiom proof_of_digits_sum_init_safety_wit_48 : digits_sum_init_safety_wit_48.
Axiom proof_of_digits_sum_init_safety_wit_49 : digits_sum_init_safety_wit_49.
Axiom proof_of_digits_sum_init_safety_wit_50 : digits_sum_init_safety_wit_50.
Axiom proof_of_digits_sum_init_safety_wit_51 : digits_sum_init_safety_wit_51.
Axiom proof_of_digits_sum_init_safety_wit_52 : digits_sum_init_safety_wit_52.
Axiom proof_of_digits_sum_init_safety_wit_53 : digits_sum_init_safety_wit_53.
Axiom proof_of_digits_sum_init_safety_wit_54 : digits_sum_init_safety_wit_54.
Axiom proof_of_digits_sum_init_safety_wit_55 : digits_sum_init_safety_wit_55.
Axiom proof_of_digits_sum_init_safety_wit_56 : digits_sum_init_safety_wit_56.
Axiom proof_of_digits_sum_init_safety_wit_57 : digits_sum_init_safety_wit_57.
Axiom proof_of_digits_sum_init_entail_wit_1 : digits_sum_init_entail_wit_1.
Axiom proof_of_digits_sum_init_entail_wit_2 : digits_sum_init_entail_wit_2.
Axiom proof_of_digits_sum_init_entail_wit_3 : digits_sum_init_entail_wit_3.
Axiom proof_of_digits_sum_init_entail_wit_4 : digits_sum_init_entail_wit_4.
Axiom proof_of_digits_sum_init_entail_wit_5 : digits_sum_init_entail_wit_5.
Axiom proof_of_digits_sum_init_entail_wit_6 : digits_sum_init_entail_wit_6.
Axiom proof_of_digits_sum_init_entail_wit_7 : digits_sum_init_entail_wit_7.
Axiom proof_of_digits_sum_init_entail_wit_8 : digits_sum_init_entail_wit_8.
Axiom proof_of_digits_sum_init_entail_wit_9 : digits_sum_init_entail_wit_9.
Axiom proof_of_digits_sum_init_entail_wit_10 : digits_sum_init_entail_wit_10.
Axiom proof_of_digits_sum_init_entail_wit_11 : digits_sum_init_entail_wit_11.
Axiom proof_of_digits_sum_init_entail_wit_12 : digits_sum_init_entail_wit_12.
Axiom proof_of_digits_sum_init_entail_wit_13 : digits_sum_init_entail_wit_13.
Axiom proof_of_digits_sum_init_entail_wit_14 : digits_sum_init_entail_wit_14.
Axiom proof_of_digits_sum_init_return_wit_1 : digits_sum_init_return_wit_1.
Axiom proof_of_digits_sum_init_partial_solve_wit_1 : digits_sum_init_partial_solve_wit_1.
Axiom proof_of_digits_sum_init_partial_solve_wit_2 : digits_sum_init_partial_solve_wit_2.
Axiom proof_of_digits_sum_init_partial_solve_wit_3 : digits_sum_init_partial_solve_wit_3.
Axiom proof_of_digits_sum_init_partial_solve_wit_4 : digits_sum_init_partial_solve_wit_4.
Axiom proof_of_digits_sum_init_partial_solve_wit_5 : digits_sum_init_partial_solve_wit_5.
Axiom proof_of_digits_sum_init_partial_solve_wit_6 : digits_sum_init_partial_solve_wit_6.
Axiom proof_of_digits_sum_init_partial_solve_wit_7 : digits_sum_init_partial_solve_wit_7.
Axiom proof_of_digits_sum_init_partial_solve_wit_8 : digits_sum_init_partial_solve_wit_8.
Axiom proof_of_digits_sum_init_partial_solve_wit_9 : digits_sum_init_partial_solve_wit_9.
Axiom proof_of_prefix_digits_sum_safety_wit_1 : prefix_digits_sum_safety_wit_1.
Axiom proof_of_prefix_digits_sum_safety_wit_2 : prefix_digits_sum_safety_wit_2.
Axiom proof_of_prefix_digits_sum_safety_wit_3 : prefix_digits_sum_safety_wit_3.
Axiom proof_of_prefix_digits_sum_safety_wit_4 : prefix_digits_sum_safety_wit_4.
Axiom proof_of_prefix_digits_sum_safety_wit_5 : prefix_digits_sum_safety_wit_5.
Axiom proof_of_prefix_digits_sum_safety_wit_6 : prefix_digits_sum_safety_wit_6.
Axiom proof_of_prefix_digits_sum_safety_wit_7 : prefix_digits_sum_safety_wit_7.
Axiom proof_of_prefix_digits_sum_safety_wit_8 : prefix_digits_sum_safety_wit_8.
Axiom proof_of_prefix_digits_sum_safety_wit_9 : prefix_digits_sum_safety_wit_9.
Axiom proof_of_prefix_digits_sum_safety_wit_10 : prefix_digits_sum_safety_wit_10.
Axiom proof_of_prefix_digits_sum_safety_wit_11 : prefix_digits_sum_safety_wit_11.
Axiom proof_of_prefix_digits_sum_safety_wit_12 : prefix_digits_sum_safety_wit_12.
Axiom proof_of_prefix_digits_sum_safety_wit_13 : prefix_digits_sum_safety_wit_13.
Axiom proof_of_prefix_digits_sum_safety_wit_14 : prefix_digits_sum_safety_wit_14.
Axiom proof_of_prefix_digits_sum_safety_wit_15 : prefix_digits_sum_safety_wit_15.
Axiom proof_of_prefix_digits_sum_safety_wit_16 : prefix_digits_sum_safety_wit_16.
Axiom proof_of_prefix_digits_sum_safety_wit_17 : prefix_digits_sum_safety_wit_17.
Axiom proof_of_prefix_digits_sum_safety_wit_18 : prefix_digits_sum_safety_wit_18.
Axiom proof_of_prefix_digits_sum_safety_wit_19 : prefix_digits_sum_safety_wit_19.
Axiom proof_of_prefix_digits_sum_safety_wit_20 : prefix_digits_sum_safety_wit_20.
Axiom proof_of_prefix_digits_sum_safety_wit_21 : prefix_digits_sum_safety_wit_21.
Axiom proof_of_prefix_digits_sum_safety_wit_22 : prefix_digits_sum_safety_wit_22.
Axiom proof_of_prefix_digits_sum_safety_wit_23 : prefix_digits_sum_safety_wit_23.
Axiom proof_of_prefix_digits_sum_safety_wit_24 : prefix_digits_sum_safety_wit_24.
Axiom proof_of_prefix_digits_sum_safety_wit_25 : prefix_digits_sum_safety_wit_25.
Axiom proof_of_prefix_digits_sum_safety_wit_26 : prefix_digits_sum_safety_wit_26.
Axiom proof_of_prefix_digits_sum_safety_wit_27 : prefix_digits_sum_safety_wit_27.
Axiom proof_of_prefix_digits_sum_safety_wit_28 : prefix_digits_sum_safety_wit_28.
Axiom proof_of_prefix_digits_sum_safety_wit_29 : prefix_digits_sum_safety_wit_29.
Axiom proof_of_prefix_digits_sum_safety_wit_30 : prefix_digits_sum_safety_wit_30.
Axiom proof_of_prefix_digits_sum_safety_wit_31 : prefix_digits_sum_safety_wit_31.
Axiom proof_of_prefix_digits_sum_safety_wit_32 : prefix_digits_sum_safety_wit_32.
Axiom proof_of_prefix_digits_sum_safety_wit_33 : prefix_digits_sum_safety_wit_33.
Axiom proof_of_prefix_digits_sum_safety_wit_34 : prefix_digits_sum_safety_wit_34.
Axiom proof_of_prefix_digits_sum_safety_wit_35 : prefix_digits_sum_safety_wit_35.
Axiom proof_of_prefix_digits_sum_safety_wit_36 : prefix_digits_sum_safety_wit_36.
Axiom proof_of_prefix_digits_sum_safety_wit_37 : prefix_digits_sum_safety_wit_37.
Axiom proof_of_prefix_digits_sum_safety_wit_38 : prefix_digits_sum_safety_wit_38.
Axiom proof_of_prefix_digits_sum_safety_wit_39 : prefix_digits_sum_safety_wit_39.
Axiom proof_of_prefix_digits_sum_safety_wit_40 : prefix_digits_sum_safety_wit_40.
Axiom proof_of_prefix_digits_sum_safety_wit_41 : prefix_digits_sum_safety_wit_41.
Axiom proof_of_prefix_digits_sum_safety_wit_42 : prefix_digits_sum_safety_wit_42.
Axiom proof_of_prefix_digits_sum_safety_wit_43 : prefix_digits_sum_safety_wit_43.
Axiom proof_of_prefix_digits_sum_safety_wit_44 : prefix_digits_sum_safety_wit_44.
Axiom proof_of_prefix_digits_sum_safety_wit_45 : prefix_digits_sum_safety_wit_45.
Axiom proof_of_prefix_digits_sum_entail_wit_1 : prefix_digits_sum_entail_wit_1.
Axiom proof_of_prefix_digits_sum_entail_wit_2 : prefix_digits_sum_entail_wit_2.
Axiom proof_of_prefix_digits_sum_entail_wit_3 : prefix_digits_sum_entail_wit_3.
Axiom proof_of_prefix_digits_sum_entail_wit_4 : prefix_digits_sum_entail_wit_4.
Axiom proof_of_prefix_digits_sum_entail_wit_5 : prefix_digits_sum_entail_wit_5.
Axiom proof_of_prefix_digits_sum_entail_wit_6 : prefix_digits_sum_entail_wit_6.
Axiom proof_of_prefix_digits_sum_entail_wit_7 : prefix_digits_sum_entail_wit_7.
Axiom proof_of_prefix_digits_sum_entail_wit_8 : prefix_digits_sum_entail_wit_8.
Axiom proof_of_prefix_digits_sum_entail_wit_9 : prefix_digits_sum_entail_wit_9.
Axiom proof_of_prefix_digits_sum_entail_wit_10 : prefix_digits_sum_entail_wit_10.
Axiom proof_of_prefix_digits_sum_return_wit_1 : prefix_digits_sum_return_wit_1.
Axiom proof_of_prefix_digits_sum_return_wit_2 : prefix_digits_sum_return_wit_2.
Axiom proof_of_prefix_digits_sum_partial_solve_wit_1 : prefix_digits_sum_partial_solve_wit_1.
Axiom proof_of_prefix_digits_sum_partial_solve_wit_2 : prefix_digits_sum_partial_solve_wit_2.
Axiom proof_of_prefix_digits_sum_partial_solve_wit_3 : prefix_digits_sum_partial_solve_wit_3.
Axiom proof_of_prefix_digits_sum_partial_solve_wit_4 : prefix_digits_sum_partial_solve_wit_4.
Axiom proof_of_interval_digits_sum_safety_wit_1 : interval_digits_sum_safety_wit_1.
Axiom proof_of_interval_digits_sum_safety_wit_2 : interval_digits_sum_safety_wit_2.
Axiom proof_of_interval_digits_sum_safety_wit_3 : interval_digits_sum_safety_wit_3.
Axiom proof_of_interval_digits_sum_safety_wit_4 : interval_digits_sum_safety_wit_4.
Axiom proof_of_interval_digits_sum_safety_wit_5 : interval_digits_sum_safety_wit_5.
Axiom proof_of_interval_digits_sum_safety_wit_6 : interval_digits_sum_safety_wit_6.
Axiom proof_of_interval_digits_sum_safety_wit_7 : interval_digits_sum_safety_wit_7.
Axiom proof_of_interval_digits_sum_safety_wit_8 : interval_digits_sum_safety_wit_8.
Axiom proof_of_interval_digits_sum_safety_wit_9 : interval_digits_sum_safety_wit_9.
Axiom proof_of_interval_digits_sum_safety_wit_10 : interval_digits_sum_safety_wit_10.
Axiom proof_of_interval_digits_sum_safety_wit_11 : interval_digits_sum_safety_wit_11.
Axiom proof_of_interval_digits_sum_safety_wit_12 : interval_digits_sum_safety_wit_12.
Axiom proof_of_interval_digits_sum_safety_wit_13 : interval_digits_sum_safety_wit_13.
Axiom proof_of_interval_digits_sum_safety_wit_14 : interval_digits_sum_safety_wit_14.
Axiom proof_of_interval_digits_sum_safety_wit_15 : interval_digits_sum_safety_wit_15.
Axiom proof_of_interval_digits_sum_entail_wit_1 : interval_digits_sum_entail_wit_1.
Axiom proof_of_interval_digits_sum_entail_wit_2 : interval_digits_sum_entail_wit_2.
Axiom proof_of_interval_digits_sum_return_wit_1 : interval_digits_sum_return_wit_1.
Axiom proof_of_interval_digits_sum_partial_solve_wit_1 : interval_digits_sum_partial_solve_wit_1.
Axiom proof_of_interval_digits_sum_partial_solve_wit_2_pure : interval_digits_sum_partial_solve_wit_2_pure.
Axiom proof_of_interval_digits_sum_partial_solve_wit_2 : interval_digits_sum_partial_solve_wit_2.
Axiom proof_of_interval_digits_sum_partial_solve_wit_3_pure : interval_digits_sum_partial_solve_wit_3_pure.
Axiom proof_of_interval_digits_sum_partial_solve_wit_3 : interval_digits_sum_partial_solve_wit_3.

End VC_Correct.
